## Experiment 3: bidirectional elaborator with metavariables, Miller pattern
## unification, and implicit-argument insertion.
##
## Two modes, following Dunfield & Krishnaswami, extended à la
## Kovács's elaboration-zoo / Norell:
##   inferTm -- synthesis mode; produces (Term, Term), the type possibly
##              containing metavariables.
##   checkTm -- checking mode against an expected *Term*; lambdas and pairs
##              elaborate against it, everything else infers then unifies.
##
## Metavariables (unify.nim) are created for implicit arguments, holes `_`,
## unannotated lambda domains, and unknown function/pair types. They are
## solved by pattern unification during elaboration; elabCheck zonks
## (substitutes all solutions) before the core's check/infer ever runs, so
## the core never sees a metavariable in the success path. Leftover unsolved
## metas are elaboration errors carrying the creation location.
##
## Implicit arguments: Pi/lambda binders written `{A : ?}` elaborate to
## core binders flagged `impl`; using a variable whose type has implicit
## leading Pis inserts fresh metas for them (insertImplicits), which
## unification solves from later explicit arguments. There is no surface
## syntax for explicit implicit application in Experiment 3.

import tables
import sequtils
import strutils
import sets
import os        # issue #49: module file loading
import hashes    # issue #49: content-hash module cache
import preterm
import parse_surf
import eponym_init
import unify
import egraph
import usage_check  # Issue #64: linear usage verification

type
  ElabError* = object of CatchableError
    loc*: Loc

proc elabErr(loc: Loc, msg: string): ref ElabError =
  let e = newException(ElabError,
    "line " & $loc.line & ", col " & $loc.col & ": " & msg)
  e.loc = loc
  e

proc unifyElab(ms: var MetaStore, a, b: Term, loc: Loc) =
  ## unify, translating UnifyError into ElabError (adds the source location).
  try:
    unify(ms, a, b, loc)
  except UnifyError as e:
    raise elabErr(loc, e.msg)

type
  CtxEntry* = object
    name*: string
    ty*: Term
    qty*: Qty  # Issue #66: binder quantity (concrete or variable)
  Ctx* = seq[CtxEntry]            # innermost-first
  GEntry* = object
    tm*: Term                     # the R node, for building terms
    ty*: Term                     # elaborated + zonked type, for implicits
    isElim*: bool                 # Experiment 4: declared with 'elim'
    elimNargs*: int               # Experiment 4: eliminator arity (incl. scrutinee)
  Globals* = Table[string, GEntry]

# Forward declaration for use in tactics
proc convElab(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
              ctx: Ctx, globals: Globals)

# --- Basic tactics (Experiment 6) ------------------------------------

proc tacAssumption(goal: Term, ctx: Ctx, globals: Globals,
                   ms: var MetaStore, supply: var Supply,
                   loc: Loc): Term =
  ## Find a hypothesis in ctx whose type matches the goal (up to conversion).
  for i, e in ctx:
    try:
      # Use conversion check: elaborate e.ty and goal, compare via convElab
      # For now, simple syntactic check via unification
      var msCopy = ms  # don't pollute the real store on failure
      unify(msCopy, e.ty, goal, loc)
      return vv(i)
    except:
      continue
  raise elabErr(loc, "assumption: no hypothesis matches the goal")

proc tacRefl(goal: Term, ctx: Ctx, globals: Globals,
             ms: var MetaStore, supply: var Supply,
             loc: Loc): Term =
  ## For Eq A x y goals where x and y are convertible, return refl.
  # Goal should be ((Eq A) x) y — an application spine of length 3
  # (head Eq applied to A, x, y)
  var spine: seq[Term] = @[]
  var cur = goal
  while cur.kind == tApp:
    spine.add(cur.arg)
    cur = cur.fn
  spine.add(cur)
  # spine is now [y, x, A, Eq] (reversed); we need 4 elements
  if spine.len != 4:
    raise elabErr(loc, "refl: goal is not an equality (spine length " &
      $spine.len & ")")
  let eqHead = spine[3]
  let aTy = spine[2]
  let x = spine[1]
  let y = spine[0]
  # Check head is Eq (a tR node)
  if eqHead.kind != tR:
    raise elabErr(loc, "refl: goal head is not Eq")
  # Check x and y are convertible via full conversion (Experiment 5b)
  try:
    convElab(ms, supply, x, y, loc, ctx, globals)
  except ElabError as e:
    raise elabErr(loc, "refl: sides are not convertible: " & e.msg)
  # Build refl A x : Eq A x x
  if "refl" notin globals:
    raise elabErr(loc, "refl: 'refl' not in scope")
  let reflTm = globals["refl"].tm
  tmApp(tmApp(reflTm, aTy), x)

# (initTactics removed: built-ins are dispatched directly in pkBy case)

proc prettyTerm(t: Term, ctx: Ctx, refNames: Table[int, string]): string =
  ## User-facing pretty-printer: uses names from the context and globals
  ## instead of internal IDs (R1, V6, ?m3).
  if t == nil: return "<nil>"
  case t.kind
  of tR:
    if t.refId in refNames: refNames[t.refId] else: "R" & $t.refId
  of tV:
    if t.idx < ctx.len and ctx[t.idx].name != "_": ctx[t.idx].name
    else: "V" & $t.idx
  of tC: $t.c
  of tInt: $t.intVal
  of tNatLit: $t.natLitVal
  of tPrim: $t.primOp
  of tPi, tSi, tLam:
    let adv = if t.scope.adv != "_": t.scope.adv else: "_"
    let kindStr =
      if t.kind == tPi:
        if t.erased: "Pi(0 "
        elif t.impl: "Pi{"
        else: "Pi("
      elif t.kind == tSi:
        if t.erased: "Si(0 "
        elif t.impl: "Si{"
        else: "Si("
      else:
        if t.erased: "L(0 "
        elif t.impl: "L{"
        else: "L("
    let ctx2 = @[CtxEntry(name: adv, ty: t.dom, qty: t.qty)] & ctx
    kindStr & prettyTerm(t.dom, ctx, refNames) & ", " & adv & ". " &
      prettyTerm(t.scope.bdy, ctx2, refNames) & ")"
  of tMeta: "?_"
  of tPair:
    "P(" & prettyTerm(t.pFst, ctx, refNames) & ", " &
      prettyTerm(t.pSnd, ctx, refNames) & ")"
  of tApp:
    "(" & prettyTerm(t.fn, ctx, refNames) & " " &
      prettyTerm(t.arg, ctx, refNames) & ")"
  of tFst: "(" & prettyTerm(t.sub, ctx, refNames) & ".1)"
  of tSnd: "(" & prettyTerm(t.sub, ctx, refNames) & ".2)"
  of tAbsurd: "(absurd " & prettyTerm(t.sub, ctx, refNames) & ")"
  of tLet:
    "let " & prettyTerm(t.letVal, ctx, refNames) & " in " &
      prettyTerm(t.letScope.bdy, @[CtxEntry(name: "_", ty: t.letTy, qty: qOmega)] & ctx, refNames)

template withConvHandler*(ms: var MetaStore, h: ConvHandler,
                          body: untyped): untyped =
  ## Experiment 41: install a conversion handler for the dynamic extent of
  ## `body`. The handler applies to every conversion goal raised (via
  ## convElab) while `body` runs — including in nested calls — and is
  ## removed afterwards even if `body` raises. This is the dynamic scoping
  ## of Andromeda-style handlers, realized without algebraic effects.
  ms.convHandlers.add(h)
  try:
    body
  finally:
    discard ms.convHandlers.pop()

proc containsNatLit(t: Term): bool =
  ## Issue #93: does t mention a primitive Nat literal anywhere?
  if t.isNil: return false
  case t.kind
  of tNatLit: true
  of tR, tV, tC, tInt, tPrim, tMeta: false
  of tPi, tSi, tLam: containsNatLit(t.dom) or containsNatLit(t.scope.bdy)
  of tPair: containsNatLit(t.pFst) or containsNatLit(t.pSnd) or
              containsNatLit(t.pScope.bdy)
  of tApp: containsNatLit(t.fn) or containsNatLit(t.arg)
  of tFst, tSnd, tAbsurd: containsNatLit(t.sub)
  of tLet: containsNatLit(t.letVal) or containsNatLit(t.letTy) or
             containsNatLit(t.letScope.bdy)

proc expandNatLit(t: Term, zeroTm, sucTm: Term): Term =
  ## Issue #93: rewrite every tNatLit(k) to the suc^k(zero) chain.
  ## Used only as a conversion fallback (see defaultConv): the elaborator's
  ## canonical numeral form is the O(1) literal, but hand-written
  ## suc-chains must stay definitionally equal to it.
  if t.isNil: return nil
  case t.kind
  of tNatLit:
    var res = zeroTm
    for _ in 1 .. t.natLitVal: res = tmApp(sucTm, res)
    res
  of tR, tV, tC, tInt, tPrim, tMeta: t
  of tPi, tSi, tLam:
    mkBinder(t.kind, expandNatLit(t.dom, zeroTm, sucTm),
             Scope(adv: t.scope.adv,
                   bdy: expandNatLit(t.scope.bdy, zeroTm, sucTm)),
             t.impl, t.qty)
  of tPair:
    tmPair(expandNatLit(t.pFst, zeroTm, sucTm),
           expandNatLit(t.pSnd, zeroTm, sucTm), t.pScope.adv,
           expandNatLit(t.pScope.bdy, zeroTm, sucTm))
  of tApp:
    tmApp(expandNatLit(t.fn, zeroTm, sucTm), expandNatLit(t.arg, zeroTm, sucTm))
  of tFst: tmFst(expandNatLit(t.sub, zeroTm, sucTm))
  of tSnd: tmSnd(expandNatLit(t.sub, zeroTm, sucTm))
  of tAbsurd: tmAbsurd(expandNatLit(t.sub, zeroTm, sucTm))
  of tLet:
    tmLet(expandNatLit(t.letVal, zeroTm, sucTm),
          expandNatLit(t.letTy, zeroTm, sucTm), t.letScope.adv,
          expandNatLit(t.letScope.bdy, zeroTm, sucTm))

proc defaultConv(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
                 ctx: Ctx, globals: Globals) =
  ## Experiment 41: the bottom of the handler stack — the Experiment 5b
  ## conversion (full reduction via the core evaluator, then the core's
  ## type-directed conversion areEqual). Raises ElabError("not
  ## convertible") on failure, exactly as convElab did before handlers
  ## existed, so behavior with an empty stack is bit-for-bit unchanged.
  ## Successes are recorded in ms.convCache, which the scoped
  ## cacheConvHandler below probes.
  ##
  ## Issue #80: rigid noConfusion pre-check — a forced constructor
  ## conflict fails fast with a named reason instead of running NbE
  ## only to report a generic mismatch. Sound: the check fires only on
  ## positive rigid evidence (distinct constructors of one datatype at
  ## some position, reached through non-unfolding heads), which no
  ## conversion could equate.
  let nc = noConfusionConflict(ms, a, b)
  if nc.bad:
    var refNames = initTable[int, string]()
    for name, g in globals:
      if g.tm.kind == tR: refNames[g.tm.refId] = name
    raise elabErr(loc, "inferred type " & prettyTerm(a, ctx, refNames) &
      " does not match expected type " & prettyTerm(b, ctx, refNames) &
      ": " & noConfusionMsg(ms, nc.c1, nc.c2))
  var env = newSeq[Value](ctx.len)
  for i in 0 ..< ctx.len:
    env[i] = freshPara(s, nil)  # types unused by conversion; identity suffices
  let va = eval(a, env)
  let vb = eval(b, env)
  try:
    areEqual(s, vStar(), va, vb)
    # Success: record in the cache for scoped cache handlers to probe.
    merge(ms.convCache, convKey(ctx.len, a, b))
  except ValueError as e:
    # Issue #93: tNatLit(k) is definitionally suc^k(zero). The core
    # compares literals only to literals (O(1) fast path above), so a
    # mixed goal — literal vs hand-written suc-chain — fails there.
    # Retry with literals expanded on both sides: this keeps
    # `refl : 2 = suc (suc zero)` and old unary artifacts convertible.
    # The expansion runs only after a genuine mismatch, never on the
    # hot path.
    if "zero" in globals and "suc" in globals and
        (containsNatLit(a) or containsNatLit(b)):
      let a2 = expandNatLit(a, globals["zero"].tm, globals["suc"].tm)
      let b2 = expandNatLit(b, globals["zero"].tm, globals["suc"].tm)
      try:
        areEqual(s, vStar(), eval(a2, env), eval(b2, env))
        merge(ms.convCache, convKey(ctx.len, a2, b2))
        return
      except ValueError:
        discard
    var refNames = initTable[int, string]()
    for name, g in globals:
      if g.tm.kind == tR: refNames[g.tm.refId] = name
    raise elabErr(loc, "inferred type " & prettyTerm(a, ctx, refNames) &
      " does not match expected type " & prettyTerm(b, ctx, refNames) &
      ": not convertible (" & e.msg & ")")

proc convElab(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
              ctx: Ctx, globals: Globals) =
  ## Conversion for the inferred-vs-expected check (Experiment 5b):
  ## compare up to full reduction — delta-unfolding of
  ## definitions, beta, and the registered wRed rules — via the core
  ## evaluator, then the core's type-directed conversion (areEqual).
  ## Free variables become fresh neutral parameters, so open terms
  ## evaluate soundly; both sides share one environment, so the same
  ## variable is the same parameter on each side.
  ## While unsolved metavariables remain, fall back to pattern
  ## unification instead: evaluation cannot solve flex constraints,
  ## and unify is the only thing that can.
  ##
  ## Experiment 41: the equality effect. Instead of running conversion
  ## directly, convElab raises the goal `a === b` to the handler stack in
  ## ms.convHandlers (top = most recently installed). Each handler either
  ## discharges the goal (cvDischarged) or declines (cvDeclined) to the
  ## next one down. The bottom of the stack is defaultConv above. The
  ## choke points that raise the effect are exactly the old failure sites:
  ## the infer-then-check boundary in checkTm and the `refl` tactic.
  ##
  ## Issue #93: reflexivity fast path. Pointer-identical terms are
  ## trivially convertible (reflexivity holds in every handler extension),
  ## so skip zonking, unification, handlers, and cache bookkeeping.
  ## This fires e.g. when the elaborator checks a literal against the
  ## canonical globals["Nat"].tm object it also used to build the type.
  if a == b: return
  let a1 = zonk(ms, a)
  let b1 = zonk(ms, b)
  if findUnsolved(ms, a1).found or findUnsolved(ms, b1).found:
    unifyElab(ms, a1, b1, loc)
    return
  var i = ms.convHandlers.high
  while i >= 0:
    let h = ms.convHandlers[i]
    if h.decide(ms, s, a1, b1, loc, ctx.len) == cvDischarged:
      if not h.coreValid:
        # A domain handler extended conversion beyond the core: record it
        # so elabDefDecl can relax the core re-check for this definition.
        inc ms.extDischarges
      return
    dec i
  defaultConv(ms, s, a1, b1, loc, ctx, globals)

proc cacheConvHandler*(): ConvHandler =
  ## Experiment 41: the Experiment 10 conversion cache as a scoped,
  ## composable decision procedure. Probes the memo table; on a hit the
  ## goal is discharged without running NbE. On a miss it declines, and
  ## the default handler below records its success in the cache — so the
  ## cache only ever contains goals the stack actually proved.
  ## coreValid=true: cache hits replay goals the default handler proved,
  ## so the core's re-check backstop stays in force.
  let decide: ConvDecide =
    proc(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
         ctxLen: int): ConvVerdict {.closure.} =
      let (hit, _) = areEqualCached(ms.convCache,
                                    convKey(ctxLen, a, b))
      if hit: cvDischarged else: cvDeclined
  ConvHandler(decide: decide, coreValid: true)

type NatPoly = object
  cst*: int
  coeff*: Table[string, int]  # atom key -> coefficient

proc polyAdd(a, b: NatPoly): NatPoly =
  result.cst = a.cst + b.cst
  result.coeff = a.coeff
  for k, v in b.coeff:
    result.coeff.mgetOrPut(k, 0) += v

proc spineOf(t: Term): tuple[head: Term, args: seq[Term]] =
  ## Destructure an application spine; args are innermost-first.
  var args: seq[Term] = @[]
  var cur = t
  while cur.kind == tApp:
    args.add(cur.arg)
    cur = cur.fn
  (cur, args)

proc normNat(t: Term, zeroId, sucId, addId: int): NatPoly =
  ## Normalize a Nat term to the linear polynomial c + Σ kᵢ·xᵢ over
  ## {zero, suc, add}. Variables and non-Nat subterms become opaque atoms
  ## keyed by their exact term rendering, so two terms share an atom only
  ## if they are syntactically identical.
  let (head, args) = spineOf(t)
  # args is innermost-first: args[0] is the last argument
  if head.kind == tR and head.refId == zeroId and args.len == 0:
    return NatPoly(cst: 0, coeff: initTable[string, int]())
  if head.kind == tR and head.refId == sucId and args.len >= 1:
    let r = normNat(args[0], zeroId, sucId, addId)
    return NatPoly(cst: r.cst + 1, coeff: r.coeff)
  if head.kind == tR and head.refId == addId and args.len >= 2:
    return polyAdd(normNat(args[1], zeroId, sucId, addId),
                   normNat(args[0], zeroId, sucId, addId))
  if t.kind == tV:
    var co = initTable[string, int]()
    co["v" & $t.idx] = 1
    return NatPoly(cst: 0, coeff: co)
  var co = initTable[string, int]()
  co["t:" & $t] = 1
  NatPoly(cst: 0, coeff: co)

proc natConv(a, b: Term, zeroId, sucId, addId, eqId: int): bool =
  ## Decide `a === b` in the linear-Nat fragment, with congruence under
  ## the Eq type former (needed because the inferred-vs-expected check
  ## compares `Eq Nat x x` against `Eq Nat x y`, not just the sides).
  let ra = normNat(a, zeroId, sucId, addId)
  let rb = normNat(b, zeroId, sucId, addId)
  if ra.cst == rb.cst and ra.coeff == rb.coeff:
    return true
  if eqId >= 0:
    let (ha, aa) = spineOf(a)
    let (hb, bb) = spineOf(b)
    if ha.kind == tR and hb.kind == tR and ha.refId == eqId and
       hb.refId == eqId and aa.len == bb.len and aa.len >= 3:
      for i in 0 ..< aa.len:
        if not natConv(aa[i], bb[i], zeroId, sucId, addId, eqId):
          return false
      return true
  false

proc natArithHandler*(globals: Globals): ConvHandler =
  ## Experiment 41: a tiny domain-specific decision procedure for linear
  ## Nat equations over {zero, suc, add}, installed with dynamic scope
  ## (see the `arith` tactic). It discharges goals the default conversion
  ## cannot — e.g. `add n (suc m) === suc (add n m)` with neutral n, m,
  ## where the core's NbE gets stuck on the neutral first argument — by
  ## normalizing both sides to c + Σ kᵢ·xᵢ and comparing.
  ##
  ## Soundness (trusted decision procedure): each normalization step is a
  ## lemma provable by induction (add-zero-right, add-suc-right, and
  ## associativity/commutativity of +), and the normal form is complete
  ## for linear equations over (ℕ, 0, suc, +). Goals outside the fragment
  ## are declined, never discharged. The handler only ever equates terms
  ## whose normal forms agree syntactically, so it agrees with the default
  ## conversion on ground terms. Returning proof evidence for the core to
  ## validate (the full Andromeda design) is future work — see decisions.org.
  var zeroId = -1
  var sucId = -1
  var addId = -1
  var eqId = -1
  if "zero" in globals and globals["zero"].tm.kind == tR:
    zeroId = globals["zero"].tm.refId
  if "suc" in globals and globals["suc"].tm.kind == tR:
    sucId = globals["suc"].tm.refId
  if "add" in globals and globals["add"].tm.kind == tR:
    addId = globals["add"].tm.refId
  if "Eq" in globals and globals["Eq"].tm.kind == tR:
    eqId = globals["Eq"].tm.refId
  result.coreValid = false
  result.decide =
    proc(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
         ctxLen: int): ConvVerdict {.closure.} =
      if addId < 0 or zeroId < 0 or sucId < 0:
        return cvDeclined  # no Nat/add in scope: nothing to decide
      if natConv(a, b, zeroId, sucId, addId, eqId): cvDischarged
      else: cvDeclined

proc ext(ctx: Ctx, name: string, ty: Term, qty: Qty = qOmega): Ctx =
  ## Extend the context: every stored type is weakened into the new frame.
  ## (Types are Terms in the frame of the context that stores them; going
  ## under a binder shifts all of them, including the new entry.)
  let w = ctx.mapIt(CtxEntry(name: it.name, ty: weaken(it.ty), qty: it.qty))
  @[CtxEntry(name: name, ty: weaken(ty), qty: qty)] & w

# --- quantity variables (Issue #66) --------------------------------------
#
# Surface `(q x : A)` binds a quantity variable `q`, declaration-scoped
# (first occurrence binds; later occurrences in the same declaration share
# it). Elaboration solves each variable from the use count at its binding
# lambda (see enforceBinderQty); zonkQty substitutes the solution when
# building core terms. A variable never solved (e.g. occurring only in a
# postulate's type) defaults to qOmega.

proc resetQVars(ms: var MetaStore) =
  ## Fresh quantity-variable scope for a top-level declaration.
  ms.qvarNames.clear()
  ms.qvarSols = @[]
  ms.qvarPending.clear()

proc qvarId(ms: var MetaStore, vname: string): int =
  ## Get-or-create the solution index for a quantity variable name.
  if vname in ms.qvarNames: return ms.qvarNames[vname]
  result = ms.qvarSols.len
  ms.qvarNames[vname] = result
  ms.qvarSols.add(QtySol(kind: qsUnknown))

proc qvarIdOpt(ms: MetaStore, vname: string): int =
  ## Solution index, or -1 if the name was never bound (no creation).
  if vname in ms.qvarNames: ms.qvarNames[vname] else: -1

proc solveQVar(ms: var MetaStore, vname: string, q: Quantity, loc: Loc) =
  ## Solve a quantity variable; conflicting solutions are an error.
  let vid = qvarId(ms, vname)
  case ms.qvarSols[vid].kind
  of qsUnknown:
    ms.qvarSols[vid] = QtySol(kind: qsSolved, q: q)
  of qsSolved:
    if ms.qvarSols[vid].q != q:
      raise elabErr(loc, "quantity variable '" & vname &
        "' requires quantity " & $ms.qvarSols[vid].q &
        " here but quantity " & $q & " elsewhere")

proc zonkQty(ms: MetaStore, qty: Qty): Quantity =
  ## Substitute the solution of a quantity variable; unsolved defaults to
  ## qOmega (backward compatible: today's code is all-omega).
  if not qty.isVar: return qty.q
  let vid = qvarIdOpt(ms, qty.vname)
  if vid >= 0 and ms.qvarSols[vid].kind == qsSolved:
    ms.qvarSols[vid].q
  else: qOmega

proc qtyIsLinear(ms: MetaStore, qty: Qty): bool =
  ## Is this binder quantity linear (concrete q1, or a variable solved to q1)?
  ## An unsolved variable defaults to qOmega (see zonkQty), so it is not linear.
  if qty.isVar:
    let vid = qvarIdOpt(ms, qty.vname)
    vid >= 0 and ms.qvarSols[vid].kind == qsSolved and
      ms.qvarSols[vid].q == q1
  else: qty.q == q1

proc flushQvarPending(ms: var MetaStore, vname: string) =
  ## Flush pending erased-arg obligations for a quantity variable
  ## (Issue #66): checkErasedArg records app sites mentioning the variable
  ## while it was unsolved. A q1 solution means the argument would be
  ## silently discarded by the 0-parameter — reject at the app site.
  ## q0/qOmega solutions (or a conflicting-solution error) drop them.
  if vname in ms.qvarPending:
    let pend = ms.qvarPending[vname]
    ms.qvarPending.del(vname)
    let vid = qvarId(ms, vname)
    if pend.len > 0 and ms.qvarSols[vid].kind == qsSolved and
       ms.qvarSols[vid].q == q1:
      raise elabErr(pend[0].loc, "linear variable '" & pend[0].varName &
        "' passed to an erased (quantity-0) parameter" &
        " — it would be silently discarded")

proc enforceQtyCount(q: Quantity, body: Term, loc: Loc, name: string,
                     ms: var MetaStore) =
  ## Enforce a concrete binder quantity against the elaborated `body`
  ## (index 0 = the binder). `body` is zonked first; a body that still
  ## mentions unsolved metas can't be counted reliably (a hole may later
  ## solve to a use) — the post-pass re-checks at the end of the
  ## declaration, when metas are solved or reported.
  if q == qOmega: return
  let zb = zonk(ms, body)
  if hasUnresolvedMetas(zb): return
  let n = countVarUses(zb)
  case q
  of q0:
    if n > 0:
      raise elabErr(loc, "erased variable '" & name & "' used " & $n &
        " time(s) in term position")
  of q1:
    if n == 0:
      raise elabErr(loc, "linear variable '" & name & "' not used")
    elif n > 1:
      raise elabErr(loc, "linear variable '" & name & "' used " & $n &
        " times (expected exactly once)")
  of qOmega: discard

proc enforceBinderQty(qty: Qty, body: Term, loc: Loc, name: string,
                      ms: var MetaStore) =
  ## Issue #66: quantity-aware typing judgment for lambdas. Enforce the
  ## binder's quantity against the elaborated body *during* elaboration,
  ## with the binder's source location (rather than only in the post-pass
  ## checkUsage, which reports at the declaration). `body` is the
  ## elaborated lambda body in the extended frame (index 0 = the binder).
  ## Only lambdas: Pi binders are deliberately not enforced here — a
  ## postulate like `Pi (1 ch : Chan s). ...` declares linearity to be
  ## enforced at use sites, and its codomain need not mention the binder.
  ##
  ## Quantity variables (surface `(q x : A)`) are *solved* here instead of
  ## enforced: the use count determines the quantity (0 -> q0, 1 -> q1,
  ## 2+ -> qOmega). A variable occurring at several binders must agree;
  ## conflicting counts are an error. (Checking mode unifies the variable
  ## with the expected Pi's quantity *before* elaborating the body and
  ## continues with the concrete quantity, so a variable reaching this
  ## branch is either unsolved or was solved from a use count — never
  ## silently from an expected type.)
  if qty.isVar:
    let zb = zonk(ms, body)
    # A body that still mentions unsolved metas can't be counted reliably
    # (a hole may later solve to a use); the post-pass re-checks at the end
    # of the declaration, when metas are solved or reported. The variable
    # then keeps its default (qOmega, see zonkQty).
    if hasUnresolvedMetas(zb): return
    let n = countVarUses(zb)
    solveQVar(ms, qty.vname, (if n == 0: q0 elif n == 1: q1 else: qOmega), loc)
    flushQvarPending(ms, qty.vname)
    return
  enforceQtyCount(qty.q, body, loc, name, ms)

proc checkErasedArgWalk(t: Term, depth: int, ctx: Ctx, loc: Loc,
                        ms: var MetaStore,
                        pending: var seq[tuple[vname, varName: string, loc: Loc]]) =
  ## Walker for checkErasedArg (Issue #66). Module-level so it can take ms
  ## as a var parameter — a nested proc may not capture it.
  case t.kind
  of tV:
    if t.idx >= depth:
      let e = ctx[t.idx - depth]
      # A variable solved to q1 is linear; an unsolved one defaults to
      # qOmega (see zonkQty) and is not.
      if qtyIsLinear(ms, e.qty):
        raise elabErr(loc, "linear variable '" & e.name &
          "' passed to an erased (quantity-0) parameter" &
          " — it would be silently discarded")
      elif e.qty.isVar:
        let vid = qvarIdOpt(ms, e.qty.vname)
        if vid < 0 or ms.qvarSols[vid].kind == qsUnknown:
          pending.add((e.qty.vname, e.name, loc))
  of tLam, tPi, tSi:
    checkErasedArgWalk(t.scope.bdy, depth + 1, ctx, loc, ms, pending)
  of tApp:
    checkErasedArgWalk(t.fn, depth, ctx, loc, ms, pending)
    checkErasedArgWalk(t.arg, depth, ctx, loc, ms, pending)
  of tPair:
    checkErasedArgWalk(t.pFst, depth, ctx, loc, ms, pending)
    checkErasedArgWalk(t.pSnd, depth, ctx, loc, ms, pending)
    checkErasedArgWalk(t.pScope.bdy, depth + 1, ctx, loc, ms, pending)
  of tFst, tSnd, tAbsurd:
    checkErasedArgWalk(t.sub, depth, ctx, loc, ms, pending)
  of tLet:
    checkErasedArgWalk(t.letVal, depth, ctx, loc, ms, pending)
    checkErasedArgWalk(t.letScope.bdy, depth + 1, ctx, loc, ms, pending)
  of tPrim:
    discard
  of tR, tC, tMeta, tInt, tNatLit:
    discard

proc checkErasedArg(arg: Term, ctx: Ctx, loc: Loc, ms: var MetaStore) =
  ## Issue #66: application-site quantity enforcement. When the Pi binder
  ## being applied has quantity q0, the argument is checked for free uses
  ## of q1-bound (linear) variables: a 0-parameter cannot consume them, so
  ## passing one would silently discard it. Mirrors countVarUses's
  ## discipline — binder domains and type annotations are types (checked
  ## in the all-0 context), so mentions there are 0-uses, not violations.
  ##
  ## A variable whose quantity variable is still unsolved can't be decided
  ## here: the obligation is recorded in ms.qvarPending and re-checked by
  ## enforceBinderQty when the variable is solved (a q1 solution rejects).
  let za = zonk(ms, arg)
  if hasUnresolvedMetas(za): return  # a hole may later solve to anything
  var pending: seq[tuple[vname, varName: string, loc: Loc]] = @[]
  checkErasedArgWalk(za, 0, ctx, loc, ms, pending)
  for p in pending:
    ms.qvarPending.mgetOrPut(p.vname, @[]).add((p.varName, p.loc))

proc resolveVar(ctx: Ctx, globals: Globals, name: string,
                loc: Loc): tuple[tm, ty: Term] =
  for i, e in ctx:
    if e.name == name: return (vv(i), e.ty)
  # Experiment 11: primitive Int operations
  if name in ["addInt", "subInt", "mulInt"] and "Int" in globals:
    let intTy = globals["Int"].tm
    let opTy = tmPi(intTy, "_", tmPi(intTy, "_", intTy))
    let op = case name
      of "addInt": opAdd
      of "subInt": opSub
      else: opMul
    return (tmPrim(op, opTy), opTy)
  if name in globals:
    let g = globals[name]
    return (g.tm, g.ty)
  raise elabErr(loc, "unbound variable '" & name & "'")

proc headTy(ms: MetaStore, t: Term): Term =
  ## Head-normalize a type for the elaborator: zonk, unfold definitions,
  ## head-beta. Purely syntactic; the core's eval is never involved.
  var cur = zonk(ms, t)
  while true:
    case cur.kind
    of tApp:
      let fh = headTy(ms, cur.fn)
      if fh.kind == tLam:
        cur = zonk(ms, subst(fh.scope.bdy, 0, cur.arg))
      else:
        return tmApp(fh, zonk(ms, cur.arg))
    of tR:
      if cur.refIsDefn and not cur.refVal.isNil:
        cur = zonk(ms, cur.refVal.syn)
      else:
        return cur
    else:
      return cur

proc ensurePi(ms: var MetaStore, loc: Loc, t: Term,
              ctxLen: int): tuple[dom, codBdy: Term, impl: bool, adv: string,
                                  qty: Quantity] =
  ## t's head must be a Pi; a metavariable head is unified with a fresh
  ## (explicit) Pi. Returns dom, the codomain body (in the extended frame),
  ## and the binder's quantity (Issue #66: part of the Pi type).
  let h = headTy(ms, t)
  if h.kind == tPi:
    return (h.dom, h.scope.bdy, h.impl, h.scope.adv, h.qty)
  if h.kind == tMeta:
    let dom = freshMeta(ms, tmC(cStar), ctxLen, 0, loc)
    let cod = freshMeta(ms, tmC(cStar), ctxLen, 1, loc)
    unifyElab(ms, h, tmPi(dom, "x", cod), loc)
    return (dom, cod, false, "x", qOmega)
  raise elabErr(loc, "expected a function type")

proc ensureSi(ms: var MetaStore, loc: Loc, t: Term,
              ctxLen: int): tuple[dom, codBdy: Term, adv: string] =
  ## t's head must be a Sigma; a metavariable head is unified with a fresh one.
  let h = headTy(ms, t)
  if h.kind == tSi:
    return (h.dom, h.scope.bdy, h.scope.adv)
  if h.kind == tMeta:
    let dom = freshMeta(ms, tmC(cStar), ctxLen, 0, loc)
    let cod = freshMeta(ms, tmC(cStar), ctxLen, 1, loc)
    unifyElab(ms, h, tmSi(dom, "_", cod), loc)
    return (dom, cod, "_")
  raise elabErr(loc, "expected a Sigma type")

proc insertImplicits(pre: PreTerm, tm, ty: Term, ctxLen: int,
                     ms: var MetaStore): tuple[tm, ty: Term] =
  ## While the type's head is an implicit Pi, apply a fresh metavariable.
  var f = tm
  var fty = ty
  while true:
    let h = headTy(ms, fty)
    if h.kind == tPi and h.impl:
      let m = freshMeta(ms, h.dom, ctxLen, 0, pre.loc)
      f = tmApp(f, m)
      fty = subst(h.scope.bdy, 0, m)
    else:
      break
  (f, fty)

proc inferTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore, supply: var Supply): tuple[tm, ty: Term]
proc checkTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore, supply: var Supply, expTy: Term): Term

proc inferTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore, supply: var Supply): tuple[tm, ty: Term] =
  ## Synthesis mode.
  case pre.kind
  of pkVar:
    let (tm, ty) = resolveVar(ctx, globals, pre.name, pre.loc)
    insertImplicits(pre, tm, ty, ctx.len, ms)
  of pkUniv: (tmC(cStar), tmC(cStar))
  of pkUnitTy: (tmC(cOne), tmC(cStar))
  of pkUnitV: (tmC(cVoid), tmC(cOne))
  of pkEmptyTy: (tmC(cZero), tmC(cStar))
  of pkHole:
    let tyM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
    let holeTm = freshMeta(ms, tyM, ctx.len, 0, pre.loc)
    # Issue #58: record the hole for LSP hover — goal type + binder context.
    var hctx: seq[tuple[name: string, ty: Term]] = @[]
    for e in ctx: hctx.add((e.name, e.ty))
    ms.holes.add(HoleInfo(holeLoc: pre.loc, holeGoal: tyM, holeCtx: hctx))
    (holeTm, tyM)
  of pkInt:
    # Experiment 11: integer literal; type is the postulated Int
    if "Int" notin globals:
      raise elabErr(pre.loc, "integer literal requires 'postulate Int : ?'")
    let intTy = globals["Int"].tm  # the R node for Int
    (tmInt(pre.intVal), intTy)
  of pkPi:
    let d = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
    let c = checkTm(pre.c2, ctx.ext(pre.name, d, pre.qty), globals, ms, supply, tmC(cStar))
    (tmPi(d, pre.name, c, pre.impl, pre.erased, zonkQty(ms, pre.qty)), tmC(cStar))
  of pkSigma:
    let d = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
    let c = checkTm(pre.c2, ctx.ext(pre.name, d), globals, ms, supply, tmC(cStar))
    (tmSi(d, pre.name, c), tmC(cStar))
  of pkLam:
    let d =
      if pre.c1.isNil: freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
      else: checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
    let (b, bty) = inferTm(pre.c2, ctx.ext(pre.name, d, pre.qty), globals, ms, supply)
    enforceBinderQty(pre.qty, b, pre.loc, pre.name, ms)  # Issue #66
    # zonkQty after enforcement: a variable is solved by now (or defaults).
    let bq = zonkQty(ms, pre.qty)
    (tmLam(d, pre.name, b, pre.impl, pre.erased, bq), tmPi(d, pre.name, bty, pre.impl, pre.erased, bq))
  of pkApp:
    var (f, fty) = inferTm(pre.c1, ctx, globals, ms, supply)
    (f, fty) = insertImplicits(pre, f, fty, ctx.len, ms)
    let (dom, codBdy, impl, _, qty) = ensurePi(ms, pre.loc, fty, ctx.len)
    if impl:
      raise elabErr(pre.loc,
        "cannot apply explicitly to an implicit argument")
    let a = checkTm(pre.c2, ctx, globals, ms, supply, dom)
    if qty == q0:
      checkErasedArg(a, ctx, pre.loc, ms)  # Issue #66: no linear var into 0-param
    (tmApp(f, a), subst(codBdy, 0, a))
  of pkPair:
    # Non-dependent Sigma with metavariable components (as the core's cPair).
    let aM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
    let bM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
    let a = checkTm(pre.c1, ctx, globals, ms, supply, aM)
    let b = checkTm(pre.c2, ctx, globals, ms, supply, bM)
    (tmPair(a, b, "_", weaken(bM)), tmSi(aM, "_", weaken(bM)))
  of pkFst:
    let (p, pty) = inferTm(pre.c1, ctx, globals, ms, supply)
    let (dom, _, _) = ensureSi(ms, pre.loc, pty, ctx.len)
    (tmFst(p), dom)
  of pkSnd:
    let (p, pty) = inferTm(pre.c1, ctx, globals, ms, supply)
    let (_, codBdy, _) = ensureSi(ms, pre.loc, pty, ctx.len)
    (tmSnd(p), subst(codBdy, 0, tmFst(p)))
  of pkLet:
    let (v, vty) =
      if pre.c1.isNil: inferTm(pre.c2, ctx, globals, ms, supply)
      elif pretermHasQtyVar(pre.c1):
        # Issue #66: quantity variables in the annotation are solved from
        # the value; infer the value first, then elaborate the annotation.
        let (vi, vtyi) = inferTm(pre.c2, ctx, globals, ms, supply)
        let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
        convElab(ms, supply, vtyi, aty, pre.loc, ctx, globals)
        (vi, aty)
      else:
        let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
        (checkTm(pre.c2, ctx, globals, ms, supply, aty), aty)
    let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, vty), globals, ms, supply)
    (tmLet(v, vty, pre.name, b), subst(bty, 0, v))
  of pkAnn:
    if pretermHasQtyVar(pre.c2):
      # Issue #66: as for pkLet above — infer the term first so quantity
      # variables in the ascribed type are solved before it elaborates.
      let (t, tty) = inferTm(pre.c1, ctx, globals, ms, supply)
      let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar))
      convElab(ms, supply, tty, ty, pre.loc, ctx, globals)
      (t, ty)
    else:
      let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar))
      (checkTm(pre.c1, ctx, globals, ms, supply, ty), ty)
  of pkBy:
    raise elabErr(pre.loc, "'by' tactic requires an expected type (use in checking mode)")

proc mkNatLit(n: int, loc: Loc): Term =
  ## Build a primitive Nat literal tNatLit(n) for integer literal n
  ## (Issue #93). O(1): no suc^n(zero) chain is constructed. The literal
  ## is definitionally equal to suc^n(zero); conversion against
  ## hand-written suc-chains is handled by defaultConv's expansion
  ## fallback below. Requires 'Nat' in scope (checked by the caller).
  if n < 0:
    raise elabErr(loc, "negative integer literal in Nat position")
  tmNatLit(n)

proc checkTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore, supply: var Supply, expTy: Term): Term =
  ## Checking mode against an expected type.
  case pre.kind
  of pkInt:
    # Literal overloading: integer literal adapts to expected type.
    # Try Nat (inductive) first, then primitive Int.
    # mkNatLit builds the O(1) primitive tNatLit; no manual reification needed.
    block:
      # Debug
      # echo "pkInt in checkTm, intVal=", pre.intVal
      var done = false
      var resTm: Term = nil
      if "Nat" in globals:
        try:
          let natTm = mkNatLit(pre.intVal, pre.loc)
          let natTy = globals["Nat"].tm
          convElab(ms, supply, natTy, expTy, pre.loc, ctx, globals)
          resTm = natTm
          done = true
        except ElabError:
          discard  # Not Nat; try Int
      if not done:
        if "Int" notin globals:
          raise elabErr(pre.loc, "integer literal requires 'postulate Int : ?' or 'data Nat'")
        let intTy = globals["Int"].tm
        convElab(ms, supply, intTy, expTy, pre.loc, ctx, globals)
        resTm = tmInt(pre.intVal)
      resTm
  of pkLam:
    let (dom, codBdy, _, _, piQty) = ensurePi(ms, pre.loc, expTy, ctx.len)
    let d =
      if pre.c1.isNil: dom
      else:
        let ad = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
        unifyElab(ms, ad, dom, pre.loc)
        ad
    # Issue #66: subject-side quantity tracking (Γ ⊢ t :^q A). Reconcile
    # the lambda's binder quantity with the expected Pi's before
    # elaborating the body:
    # - quantity variable: solve from the expected type (conflicting
    #   solutions are an error); the body is then checked under it.
    # - concrete and equal: fine.
    # - concrete qOmega: the surface has no explicit-omega annotation, so
    #   this means "unannotated" — inherit the expected quantity (the
    #   Idris 2 behaviour for unannotated binders in checking mode).
    # - concrete and different: an elaboration error.
    var bQty: Qty
    if pre.qty.isVar:
      solveQVar(ms, pre.qty.vname, piQty, pre.loc)
      flushQvarPending(ms, pre.qty.vname)
      bQty = toQty(piQty)
    elif pre.qty.q == piQty or pre.qty.q == qOmega:
      bQty = toQty(if pre.qty.q == piQty: pre.qty.q else: piQty)
    else:
      raise elabErr(pre.loc, "lambda binder quantity " & $pre.qty.q &
        " does not match the expected quantity " & $piQty &
        " from the function type")
    let b = checkTm(pre.c2, ctx.ext(pre.name, d, bQty), globals, ms, supply, codBdy)
    enforceBinderQty(bQty, b, pre.loc, pre.name, ms)  # Issue #66
    # DEBUG
    # echo "DEBUG checkTm pkLam: pre.qty=", pre.qty, " name=", pre.name
    tmLam(d, pre.name, b, pre.impl, pre.erased, zonkQty(ms, bQty))
  of pkPair:
    let h = headTy(ms, expTy)
    if h.kind == tSi:
      let a = checkTm(pre.c1, ctx, globals, ms, supply, h.dom)
      let b = checkTm(pre.c2, ctx, globals, ms, supply, subst(h.scope.bdy, 0, a))
      tmPair(a, b, h.scope.adv, h.scope.bdy)
    elif h.kind == tMeta:
      let (dom, codBdy, adv) = ensureSi(ms, pre.loc, expTy, ctx.len)
      let a = checkTm(pre.c1, ctx, globals, ms, supply, dom)
      let b = checkTm(pre.c2, ctx, globals, ms, supply, subst(codBdy, 0, a))
      tmPair(a, b, adv, codBdy)
    else:
      raise elabErr(pre.loc, "pair " & $pre &
        " checked against a non-Sigma type")
  of pkLet:
    if pre.c1.isNil:
      let (v, vty) = inferTm(pre.c2, ctx, globals, ms, supply)
      let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, vty), globals, ms, supply)
      unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
      tmLet(v, vty, pre.name, b)
    elif pretermHasQtyVar(pre.c1):
      # Issue #66: quantity variables in the annotation are solved from
      # the value; infer the value first, then elaborate the annotation.
      let (v, vty) = inferTm(pre.c2, ctx, globals, ms, supply)
      let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
      convElab(ms, supply, vty, aty, pre.loc, ctx, globals)
      let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, aty), globals, ms, supply)
      unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
      tmLet(v, aty, pre.name, b)
    else:
      let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
      let v = checkTm(pre.c2, ctx, globals, ms, supply, aty)
      let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, aty), globals, ms, supply)
      unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
      tmLet(v, aty, pre.name, b)
  of pkAnn:
    if pretermHasQtyVar(pre.c2):
      # Issue #66: as for pkLet above — infer the term first so quantity
      # variables in the ascribed type are solved before it elaborates.
      let (t, tty) = inferTm(pre.c1, ctx, globals, ms, supply)
      let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar))
      convElab(ms, supply, tty, ty, pre.loc, ctx, globals)
      unifyElab(ms, ty, expTy, pre.loc)
      t
    else:
      let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar))
      let t = checkTm(pre.c1, ctx, globals, ms, supply, ty)
      unifyElab(ms, ty, expTy, pre.loc)
      t
  of pkBy:
    # Experiment 6: run a built-in tactic against the expected type.
    # (Custom tactic registration removed; built-ins are sufficient
    # for the macro embedding path.)
    case pre.name
    of "refl": tacRefl(expTy, ctx, globals, ms, supply, pre.loc)
    of "assumption": tacAssumption(expTy, ctx, globals, ms, supply, pre.loc)
    of "arith":
      # Experiment 41: run the refl tactic with the Nat arithmetic
      # decision procedure installed for the dynamic extent of the
      # tactic *and* the subsequent inferred-vs-expected check — both
      # raise conversion goals through convElab, so both see the handler.
      withConvHandler(ms, natArithHandler(globals),
        tacRefl(expTy, ctx, globals, ms, supply, pre.loc))
    else: raise elabErr(pre.loc, "unknown tactic '" & pre.name & "'")
  else:
    let (t, ty) = inferTm(pre, ctx, globals, ms, supply)
    convElab(ms, supply, ty, expTy, pre.loc, ctx, globals)
    t

type
  ElabDef* = object
    name*: string
    tyTm*: Term
    tmTm*: Term
    loc*: Loc

proc elabDefDecl(d: SurfDef, globals: var Globals, supply: var Supply,
               ms: var MetaStore): ElabDef =
  ## Elaborate one `def` (the Experiment 2/3 pipeline, unchanged).
  # Experiment 41: snapshot the extended-conversion counter. If a
  # coreValid=false handler discharged a goal while elaborating this
  # definition, conversion was deliberately extended beyond the core's
  # for its dynamic extent, and step 3's bare-core re-check is relaxed
  # (the elaborator's checkTm above already validated with the extended
  # conversion). This is the Andromeda semantics: installing an equality
  # handler extends what the system accepts, scoping the trust extension.
  let extBefore = ms.extDischarges
  resetQVars(ms)  # Issue #66: fresh quantity-variable scope per declaration
  # 1. elaborate the type; it must be a type and contain no metas
  let tyPre = d.desugarTy()
  let tmPre = d.desugarTm()
  # Issue #66: quantity variables in the ascribed type are solved from the
  # body's binders, so when the type mentions one, elaborate the body first
  # (inference), then the type (variables solved by then), then check the
  # inferred body type against the ascribed type. Otherwise the usual
  # order: elaborate the type, then check the body against it.
  # (The quantity-first order cannot use checking-only constructs: a `by`
  # tactic body or an integer literal needing Nat from the expected type
  # raises the usual "requires an expected type" error.)
  let qtyFirst = pretermHasQtyVar(tyPre)
  var tmT0: Term
  var tmTy0: Term
  if qtyFirst:
    let inferred = inferTm(tmPre, @[], globals, ms, supply)
    tmT0 = inferred.tm
    tmTy0 = zonk(ms, inferred.ty)
  let (tyTm0, tyTy) = inferTm(tyPre, @[], globals, ms, supply)
  unifyElab(ms, tyTy, tmC(cStar), d.loc)
  let tyT = zonk(ms, tyTm0)
  let ru = findUnsolved(ms, tyT)
  if ru.found and not ms.allowHoles:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the type of '" & d.name & "'")
  let tyV =
    if ru.found:
      # allowHoles (issue #58): the type mentions holes, so the core
      # cannot value it; registration is skipped below and this dummy
      # is never read.
      vStar()
    else:
      try: check(supply, vStar(), tyT)
      except ValueError as e:
        raise elabErr(d.loc,
          "ill-formed type of '" & d.name & "': " & e.msg)
  # 2. elaborate the body against the type; zonk; reject leftovers
  if qtyFirst:
    convElab(ms, supply, tmTy0, tyT, d.loc, @[], globals)
  else:
    tmT0 = checkTm(tmPre, @[], globals, ms, supply, tyT)
  let tmT = zonk(ms, tmT0)
  let ru2 = findUnsolved(ms, tmT)
  if ru2.found and not ms.allowHoles:
    raise elabErr(ru2.loc, "unsolved metavariable ?m" & $ru2.id &
      " in the definition of '" & d.name & "'")
  if d.name in globals:
    raise elabErr(d.loc, "duplicate definition '" & d.name & "'")
  if ms.allowHoles and (ru.found or ru2.found):
    # Issue #58: hole-tolerant tooling mode. The core can never see a
    # metavariable, so skip the core re-check; register postulate-style
    # (type known, value stuck) when the type is meta-free, otherwise
    # leave the name unregistered — later decls mentioning it fail at
    # their own location.
    if not ru.found:
      let tyV =
        try: check(supply, vStar(), tyT)
        except ValueError as e:
          raise elabErr(d.loc,
            "ill-formed type of '" & d.name & "': " & e.msg)
      globals[d.name] = GEntry(tm: newPostulateRef(supply, tyV), ty: tyT)
    return ElabDef(name: d.name, tyTm: tyT, tmTm: tmT, loc: d.loc)
  # 3. the core verifies the zonked (meta-free) terms — unless a
  # domain handler extended conversion for this definition (see above).
  let tmV =
    if ms.extDischarges != extBefore:
      eval(tmT, @[])
    else:
      try: check(supply, tyV, tmT)
      except ValueError as e:
        raise elabErr(d.loc, "definition '" & d.name &
          "' does not check against its declared type: " & e.msg &
          "\n  expected: " & $d.desugarTy() &
          "\n  body:     " & $d.desugarTm())
  globals[d.name] = GEntry(tm: newDefRef(supply, tyV, tmV), ty: tyT)
  ElabDef(name: d.name, tyTm: tyT, tmTm: tmT, loc: d.loc)

proc elabPostulateDecl(name: string, ty: PreTerm, loc: Loc,
                       globals: var Globals, supply: var Supply,
                       ms: var MetaStore, isElim: bool) =
  ## Experiment 4: `postulate name : Ty` / `elim name : Ty`.
  ## A parameter-like global; `elim` additionally installs an empty
  ## reduction rule table on the R node for later `red` declarations.
  resetQVars(ms)  # Issue #66: fresh quantity-variable scope per declaration
  if name in globals:
    raise elabErr(loc, "duplicate declaration '" & name & "'")
  let (tyTm0, tyTy) = inferTm(ty, @[], globals, ms, supply)
  unifyElab(ms, tyTy, tmC(cStar), loc)
  let tyT = zonk(ms, tyTm0)
  let ru = findUnsolved(ms, tyT)
  if ru.found and not ms.allowHoles:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the type of '" & name & "'")
  let tyV =
    if ru.found:
      # allowHoles (issue #58): the type mentions holes; the core cannot
      # value it and registration is skipped below — dummy never read.
      vStar()
    else:
      try: check(supply, vStar(), tyT)
      except ValueError as e:
        raise elabErr(loc, "ill-formed type of '" & name & "': " & e.msg)
  if ru.found:
    # allowHoles: leave the name unregistered; later decls mentioning it
    # fail at their own location.
    return
  # the type must be a Pi spine (for `elim`: determines the arity)
  var nargs = 0
  var tyHead = tyT
  while true:
    let h = headTy(ms, tyHead)
    if h.kind != tPi: break
    inc nargs
    tyHead = h.scope.bdy  # already in the extended frame
  if isElim and nargs < 1:
    raise elabErr(loc, "eliminator '" & name &
      "' must have a Pi type (at least the scrutinee argument)")
  let tm =
    if isElim: newRedRef(supply, tyV, nargs)
    else: newPostulateRef(supply, tyV)
  globals[name] = GEntry(tm: tm, ty: tyT, isElim: isElim, elimNargs: nargs)

proc flattenAppSpine(pre: PreTerm): seq[PreTerm] =
  ## head-first application spine
  var cur = pre
  var rev: seq[PreTerm] = @[]
  while cur.kind == pkApp:
    rev.add(cur.c2); cur = cur.c1
  rev.add(cur)
  for i in countdown(rev.high, 0):
    result.add(rev[i])

proc checkStructuralRec(rhs: PreTerm, elimName: string, nargs: int,
                        smallerVars: seq[string], loc: Loc,
                        lamBound: seq[string] = @[]) =
  ## Issue #36: syntactic structural recursion check for `red` rules.
  ## Any application of `elimName` in the RHS must take a direct subterm
  ## of the LHS pattern (a variable from `smallerVars`) in the scrutinee
  ## position (last argument). Issue #113: for higher-order constructor
  ## arguments the generated computation rule recurses under binders, so
  ## a scrutinee of shape `(v y1..yn)` — a direct subterm `v` applied to
  ## lambda-bound variables — is also accepted. Otherwise the rule may
  ## not terminate.
  case rhs.kind
  of pkApp:
    var spine: seq[PreTerm] = @[]
    var h = rhs
    while h.kind == pkApp:
      spine.add(h.c2)
      h = h.c1
    var rspine: seq[PreTerm] = @[]
    for i in countdown(spine.high, 0): rspine.add(spine[i])
    if h.kind == pkVar and h.name == elimName:
      if rspine.len == nargs:
        let scrutArg = rspine[^1]
        var structOk = scrutArg.kind == pkVar and
                       scrutArg.name in smallerVars
        if not structOk:
          # Issue #113: higher-order subterm.
          let ssp = flattenAppSpine(scrutArg)
          if ssp.len > 1 and ssp[0].kind == pkVar and
             ssp[0].name in smallerVars:
            structOk = true
            for k in 1 ..< ssp.len:
              if ssp[k].kind != pkVar or ssp[k].name notin lamBound:
                structOk = false
                break
        if not structOk:
          raise elabErr(rhs.loc,
            "non-structurally-recursive call in `red` rule: '" & elimName &
            "' applied to '" & $scrutArg &
            "', which is not a direct subterm of the LHS pattern " &
            "(for higher-order arguments, apply the variable only to " &
            "lambda-bound variables)")
      # Recurse into the spine args (they may contain nested calls)
      for a in rspine:
        checkStructuralRec(a, elimName, nargs, smallerVars, loc, lamBound)
    else:
      checkStructuralRec(h, elimName, nargs, smallerVars, loc, lamBound)
      for a in rspine:
        checkStructuralRec(a, elimName, nargs, smallerVars, loc, lamBound)
  of pkLam:
    if rhs.c1 != nil:
      checkStructuralRec(rhs.c1, elimName, nargs, smallerVars, loc, lamBound)
    checkStructuralRec(rhs.c2, elimName, nargs, smallerVars, loc,
                       lamBound & @[rhs.name])
  of pkPi:
    checkStructuralRec(rhs.c1, elimName, nargs, smallerVars, loc)
    checkStructuralRec(rhs.c2, elimName, nargs, smallerVars, loc)
  of pkPair:
    checkStructuralRec(rhs.c1, elimName, nargs, smallerVars, loc)
    checkStructuralRec(rhs.c2, elimName, nargs, smallerVars, loc)
  of pkLet:
    checkStructuralRec(rhs.c1, elimName, nargs, smallerVars, loc)
    checkStructuralRec(rhs.c2, elimName, nargs, smallerVars, loc)
    checkStructuralRec(rhs.c3, elimName, nargs, smallerVars, loc)
  of pkAnn:
    checkStructuralRec(rhs.c1, elimName, nargs, smallerVars, loc)
    checkStructuralRec(rhs.c2, elimName, nargs, smallerVars, loc)
  else:
    discard

proc elabRedDecl(lhs, rhs: PreTerm, loc: Loc,
                 globals: var Globals, supply: var Supply,
                 ms: var MetaStore) =
  ## Experiment 4: `red elim v1..v(k-1) scPat = contractum`,
  ## where scPat is `ctor` or `(ctor w1..wm)`, all bare variables.
  ## Elaborates the contractum in the pattern context and registers
  resetQVars(ms)  # Issue #66: fresh quantity-variable scope per declaration
  ## the case on the eliminator's rule table.
  let spine = flattenAppSpine(lhs)
  if spine[0].kind != pkVar:
    raise elabErr(loc, "red pattern must start with the eliminator name")
  let elimName = spine[0].name
  if elimName notin globals:
    raise elabErr(loc, "unbound eliminator '" & elimName & "'")
  let g = globals[elimName]
  if not g.isElim:
    raise elabErr(loc, "'" & elimName &
      "' is not an eliminator (declare it with 'elim')")
  let nargs = g.elimNargs
  if spine.len != nargs + 1:
    raise elabErr(loc, "eliminator '" & elimName & "' takes " & $nargs &
      " arguments; red pattern has " & $(spine.len - 1))
  # eliminator argument patterns: distinct bare variables
  var elimVars: seq[string] = @[]
  for i in 1 ..< nargs:
    if spine[i].kind != pkVar:
      raise elabErr(loc,
        "eliminator arguments in a red pattern must be bare variables")
    elimVars.add(spine[i].name)
  # scrutinee pattern: `ctor` or `(ctor w1..wm)`.
  # Arguments may be fresh variables (bound as ctor vars) or references
  # to already-bound eliminator variables (Experiment 5: `data`
  # generates `(nil A)` where A is a param). Leading bound variables
  # are the constructor's params (nParams); only fresh ones are ctor vars.
  let scSpine = flattenAppSpine(spine[nargs])
  if scSpine[0].kind != pkVar:
    raise elabErr(loc, "scrutinee pattern must be a constructor application")
  let ctorName = scSpine[0].name
  var ctorVars: seq[string] = @[]
  var nParams = 0
  var seenParamsDone = false
  for i in 1 ..< scSpine.len:
    if scSpine[i].kind != pkVar:
      raise elabErr(loc,
        "constructor arguments in a red pattern must be bare variables")
    let vn = scSpine[i].name
    if not seenParamsDone and vn in elimVars:
      inc nParams
    else:
      seenParamsDone = true
      if vn in elimVars or vn in ctorVars:
        raise elabErr(loc, "pattern variables in a red rule must be distinct")
      ctorVars.add(vn)
  let allVars = elimVars & ctorVars
  if allVars.deduplicate().len != allVars.len:
    raise elabErr(loc, "pattern variables in a red rule must be distinct")
  if ctorName notin globals:
    raise elabErr(loc, "unbound constructor '" & ctorName & "'")
  let cg = globals[ctorName]
  if cg.tm.kind != tR:
    raise elabErr(loc, "constructor '" & ctorName & "' must be a postulate")
  # introduce the eliminator variables, types from the eliminator's Pi spine
  var ctx: Ctx = @[]
  var elimTy = g.ty
  for nm in elimVars:
    let h = headTy(ms, elimTy)
    if h.kind != tPi:
      raise elabErr(loc, "eliminator type is not a Pi spine of length " &
        $nargs)
    ctx = ext(ctx, nm, h.dom)   # h.dom is in the current frame
    elimTy = h.scope.bdy        # already in the extended frame
  # introduce the constructor variables, types from the constructor's Pi spine.
  # First instantiate the leading params with the already-bound variables
  # (Experiment 5: `nil : Pi (A:? ). Vec A zero` applied to the elim's A).
  var ctorTy = cg.ty
  for i in 0 ..< nParams:
    let h = headTy(ms, ctorTy)
    if h.kind != tPi:
      raise elabErr(loc, "constructor '" & ctorName &
        "' does not take enough arguments")
    let varIdx = elimVars.len - 1 - i  # de Bruijn index of elimVars[i]
    ctorTy = subst(h.scope.bdy, 0, vv(varIdx))
  for nm in ctorVars:
    let h = headTy(ms, ctorTy)
    if h.kind != tPi:
      raise elabErr(loc, "constructor '" & ctorName & "' does not take " &
        $(nParams + ctorVars.len) & " arguments")
    ctx = ext(ctx, nm, h.dom)
    ctorTy = h.scope.bdy
  # Issue #36: structural recursion check — recursive calls must take
  # direct subterms of the LHS pattern. The ctorVars are exactly the
  # direct subterms of the scrutinee pattern.
  checkStructuralRec(rhs, elimName, nargs, ctorVars, loc)
  # elaborate the contractum (inference mode — the rule is trusted, like
  # an axiom; a production system would check it against the motive)
  let (rhsTm0, _) = inferTm(rhs, ctx, globals, ms, supply)
  let rhsTm = zonk(ms, rhsTm0)
  let ru = findUnsolved(ms, rhsTm)
  if ru.found and not ms.allowHoles:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the contractum of a red rule")
  try:
    attachRedCase(g.tm, cg.tm.refId, rhsTm, nParams)
  except ValueError as e:
    raise elabErr(loc, e.msg)

# --- Experiment 5: data declarations -------------------------------------------
# A `data` declaration desugars to postulate/elim/red (Experiment 4) and
# goes through the same elaborators. The desugarer generates:
#   postulate F : Pi (params...). indexTy
#   postulate c : Pi (params...). Pi (tele...). retTy     (per constructor)
#   elim fElim : Pi (params...)(C : Pi (idx...). F params idx -> ?).
#                Pi (methods...). Pi (idx...)(v : F params idx). C idx v
#   red fElim params C methods idxVars (c params teleVars) = contractum
# Index positions in red patterns are dummy variables (unused in the
# contractum); fireRed's spine convention already accounts for them.

proc mkPis(tele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]],
           body: PreTerm, loc: Loc): PreTerm =
  result = body
  for i in countdown(tele.high, 0):
    result = mkPi(tele[i].name, tele[i].ty, result, loc, tele[i].impl, tele[i].erased, tele[i].qty)

proc flattenPiPre(pre: PreTerm):
    tuple[tele: seq[tuple[name: string, ty: PreTerm]], body: PreTerm] =
  var cur = pre
  var tele: seq[tuple[name: string, ty: PreTerm]] = @[]
  while cur.kind == pkPi:
    tele.add((cur.name, cur.c1))
    cur = cur.c2
  (tele, cur)

proc extractIndices(retTy: PreTerm, famName: string, nParams: int,
                    loc: Loc): seq[PreTerm] =
  ## retTy should be `F p1..pn i1..ik`; return [i1..ik] as PreTerms.
  let spine = flattenAppSpine(retTy)
  if spine.len == 0 or spine[0].kind != pkVar or spine[0].name != famName:
    raise elabErr(loc, "constructor return type must be the family '" &
      famName & "' applied to indices")
  if spine.len < 1 + nParams:
    raise elabErr(loc, "constructor return type missing parameters")
  spine[1 + nParams .. ^1]

proc mentionsFam(pre: PreTerm, famName: string): bool =
  case pre.kind
  of pkVar: pre.name == famName
  of pkApp: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  of pkPi: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  of pkSigma: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  of pkLam: mentionsFam(pre.c2, famName)
  of pkPair: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  of pkFst, pkSnd: mentionsFam(pre.c1, famName)
  of pkLet: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName) or
             mentionsFam(pre.c3, famName)
  of pkAnn: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  else: false

proc substPreN(t: PreTerm, subs: seq[(string, PreTerm)],
               fresh: var int): PreTerm
proc substPreSeq(ts: seq[PreTerm], subs: seq[(string, PreTerm)],
                 fresh: var int): seq[PreTerm]

proc splitCtorArg(argTy: PreTerm, famName, ctorName, argName: string,
                  nParams: int, loc: Loc):
    tuple[tele: seq[tuple[name: string, ty: PreTerm]],
          indices: seq[PreTerm]] =
  ## Issue #113: split a constructor argument type into its leading Pi
  ## telescope and the family indices of its head. The head must be a
  ## direct application of the family (first-order case: empty telescope),
  ## and the telescope domains must not mention the family (strict
  ## positivity). Raises accurate errors naming the offending argument —
  ## the old `extractIndices`-only path reported these as "constructor
  ## return type must be the family", which was misleading.
  var tele: seq[tuple[name: string, ty: PreTerm]] = @[]
  var head = argTy
  while head.kind == pkPi:
    tele.add((head.name, head.c1))
    head = head.c2
  for (bn, bty) in tele:
    if mentionsFam(bty, famName):
      raise elabErr(loc, "constructor '" & ctorName & "' argument '" &
        argName & "': the family '" & famName &
        "' occurs in the domain of a higher-order argument " &
        "(not strictly positive)")
  let spine = flattenAppSpine(head)
  if spine.len == 0 or spine[0].kind != pkVar or spine[0].name != famName:
    raise elabErr(loc, "constructor '" & ctorName & "' argument '" &
      argName & "': the family '" & famName &
      "' must occur as a direct application to indices " &
      "(nested occurrences are not supported)")
  if spine.len < 1 + nParams:
    raise elabErr(loc, "constructor '" & ctorName & "' argument '" &
      argName & "': family application is missing parameters")
  (tele, spine[1 + nParams .. ^1])

proc freshenHoTele(tele: seq[tuple[name: string, ty: PreTerm]],
                   taken: var seq[string], loc: Loc):
    tuple[tele: seq[tuple[name: string, ty: PreTerm]], names: seq[string],
          subst: seq[(string, PreTerm)]] =
  ## Issue #113: rename a higher-order argument's Pi telescope binders to
  ## names fresh w.r.t. `taken` (chosen names are added to `taken`),
  ## substituting earlier binders in later domain types (capture-avoiding
  ## via substPreN). Anonymous binders get a real name so the generated
  ## induction hypothesis and computation-rule lambda can apply the
  ## argument to them. The returned `subst` maps original binder names to
  ## freshened variables (replace-on-shadow, matching surface scoping) for
  ## use on index terms mentioning the telescope binders.
  var subs: seq[(string, PreTerm)] = @[]
  var fresh = 0
  var names: seq[string] = @[]
  var outTele: seq[tuple[name: string, ty: PreTerm]] = @[]
  for (bn, bty) in tele:
    var nb = if bn == "_" or bn.len == 0: "x" else: bn
    while nb in taken: nb &= "'"
    taken.add(nb)
    let btySub = substPreN(bty, subs, fresh)
    let rv = mkVar(nb, loc)
    var replaced = false
    for k in 0 ..< subs.len:
      if subs[k][0] == bn:
        subs[k] = (bn, rv)
        replaced = true
    if not replaced:
      subs.add((bn, rv))
    names.add(nb)
    outTele.add((nb, btySub))
  (outTele, names, subs)


proc elimNameFor(dname: string): string =
  result = dname
  if result.len > 0:
    result[0] = result[0].toLowerAscii()
  result &= "Elim"

proc famAppPre(famName: string, params: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]],
               idxTerms: seq[PreTerm], loc: Loc): PreTerm =
  result = mkVar(famName, loc)
  for p in params: result = mkApp(result, mkVar(p.name, loc), loc)
  for t in idxTerms: result = mkApp(result, t, loc)

proc genElimTy(d: SurfDecl, loc: Loc): tuple[ty: PreTerm, methodNames: seq[string]] =
  ## Generate the eliminator type PreTerm and the method binder names.
  let famName = d.dname
  let (indexTele, _) = flattenPiPre(d.indexTy)
  var indexNames: seq[string] = @[]
  for i in 0 ..< indexTele.len:
    indexNames.add("i" & $i)
  # Issue #112: later index domains may mention earlier index binders
  # (dependent index telescopes, e.g. `Pi (n : Nat). VExpr n -> ?`).
  # The eliminator renames binders to i0, i1, ..., so substitute the
  # old names for the generated ones across the telescope; a no-op for
  # non-dependent telescopes. Capture-avoiding via substPreN (a domain
  # that binds an iN name itself is renamed internally).
  var idxSubs: seq[(string, PreTerm)] = @[]
  var idxFresh = 0
  var indexTys: seq[PreTerm] = @[]
  for i in 0 ..< indexTele.len:
    indexTys.add(substPreN(indexTele[i].ty, idxSubs, idxFresh))
    idxSubs.add((indexTele[i].name, mkVar(indexNames[i], loc)))
  # C : Pi (idx...). F params idx -> ?
  var cTy = mkArrow(famAppPre(famName, d.params,
                             indexNames.mapIt(mkVar(it, loc)), loc),
                    mkUniv(loc), loc)
  for i in countdown(indexTele.high, 0):
    cTy = mkPi(indexNames[i], indexTys[i], cTy, loc)
  # methods, one per constructor
  var methodNames: seq[string] = @[]
  var methodTys: seq[PreTerm] = @[]
  for ci, ctor in d.ctors:
    let mName = "m" & $ci & "_" & ctor.name
    methodNames.add(mName)
    var teleVars: seq[PreTerm] = @[]
    for t in ctor.tele: teleVars.add(mkVar(t.name, loc))
    var ctorApp = mkVar(ctor.name, loc)
    for p in d.params: ctorApp = mkApp(ctorApp, mkVar(p.name, loc), loc)
    for v in teleVars: ctorApp = mkApp(ctorApp, v, loc)
    let retIndices = extractIndices(ctor.retTy, famName, d.params.len, ctor.cloc)
    var mRet = mkVar("C", loc)
    for ri in retIndices: mRet = mkApp(mRet, ri, loc)
    mRet = mkApp(mRet, ctorApp, loc)
    var mTy = mRet
    var ihCount = 0
    # Issue #113: names already bound in the method telescope; freshened
    # higher-order telescope binders must avoid all of these.
    var taken: seq[string] = @["C", "v"]
    for p in d.params: taken.add(p.name)
    for mn in methodNames: taken.add(mn)
    for iNm in indexNames: taken.add(iNm)
    for t in ctor.tele: taken.add(t.name)
    for i in countdown(ctor.tele.high, 0):
      let argTy = ctor.tele[i].ty
      let argName = ctor.tele[i].name
      if mentionsFam(argTy, famName):
        # Issue #113: split off a leading Pi telescope; the empty
        # telescope is the first-order case (identical to the old code).
        let (hoTele, argIndices) = splitCtorArg(argTy, famName, ctor.name,
                                               argName, d.params.len,
                                               ctor.cloc)
        let (freshTele, hoNames, hoSubst) =
          freshenHoTele(hoTele, taken, ctor.cloc)
        var fresh = 0
        # Indices may mention the telescope binders (#113: e.g. an index
        # computed from a bound value); freshen them too.
        let argIndicesSub = substPreSeq(argIndices, hoSubst, fresh)
        var ihTy = mkVar("C", loc)
        for ai in argIndicesSub: ihTy = mkApp(ihTy, ai, loc)
        var kApp = mkVar(argName, loc)
        for hn in hoNames: kApp = mkApp(kApp, mkVar(hn, ctor.cloc), loc)
        ihTy = mkApp(ihTy, kApp, loc)
        # Higher-order induction hypothesis:
        #   ih : Pi (x1:A1)...(xn:An). C idx (k x1 ... xn)
        # Issue #66: generated IH binders are unrestricted (qOmega), like
        # the rest of the generated method telescope.
        for j in countdown(freshTele.high, 0):
          ihTy = mkPi(freshTele[j].name, freshTele[j].ty, ihTy, ctor.cloc)
        let ihName = "ih" & $ihCount
        taken.add(ihName)
        mTy = mkPi(ihName, ihTy, mTy, loc)
        inc ihCount
      mTy = mkPi(argName, argTy, mTy, loc)
    methodTys.add(mTy)
  # Pi (params...)(C : cTy)(methods...)(idx...)(v : F params idx). C idx v
  var vTy = famAppPre(famName, d.params,
                      indexNames.mapIt(mkVar(it, loc)), loc)
  var body = mkVar("C", loc)
  for iNm in indexNames: body = mkApp(body, mkVar(iNm, loc), loc)
  body = mkApp(body, mkVar("v", loc), loc)
  var elimTy = mkPi("v", vTy, body, loc)
  for i in countdown(indexNames.high, 0):
    elimTy = mkPi(indexNames[i], indexTys[i], elimTy, loc)
  for i in countdown(methodNames.high, 0):
    elimTy = mkPi(methodNames[i], methodTys[i], elimTy, loc)
  elimTy = mkPi("C", cTy, elimTy, loc)
  for i in countdown(d.params.high, 0):
    elimTy = mkPi(d.params[i].name, d.params[i].ty, elimTy, d.daloc,
                  d.params[i].impl)
  (elimTy, methodNames)

proc genRedDecls(d: SurfDecl, elimName: string, methodNames: seq[string],
                 loc: Loc): seq[SurfDecl] =
  ## Generate one `red` per constructor. Index positions are dummy
  ## variables (fireRed's spine convention includes them; the
  ## contractum never mentions them).
  let famName = d.dname
  let (indexTele, _) = flattenPiPre(d.indexTy)
  var idxNames: seq[string] = @[]
  for i in 0 ..< indexTele.len:
    idxNames.add("idx" & $i)
  for ci, ctor in d.ctors:
    var lhs = mkVar(elimName, loc)
    for p in d.params: lhs = mkApp(lhs, mkVar(p.name, loc), loc)
    lhs = mkApp(lhs, mkVar("C", loc), loc)
    for mn in methodNames: lhs = mkApp(lhs, mkVar(mn, loc), loc)
    for iNm in idxNames: lhs = mkApp(lhs, mkVar(iNm, loc), loc)
    var sc = mkVar(ctor.name, loc)
    for p in d.params: sc = mkApp(sc, mkVar(p.name, loc), loc)
    for t in ctor.tele: sc = mkApp(sc, mkVar(t.name, loc), loc)
    lhs = mkApp(lhs, sc, loc)
    # contractum: method applied to teleVars with each recursive call
    # immediately after its argument, matching the interleaved method
    # telescope built by genElimTy (Pi (a) (ih_a) (b) (ih_b) ...).
    # (A two-loop form -- all args, then all recursive calls -- is only
    # correct when every recursive argument is trailing.)
    # Issue #113: the lambda binders for higher-order arguments must avoid
    # the red pattern variables (they are bound in the contractum context).
    var taken: seq[string] = @["C"]
    for p in d.params: taken.add(p.name)
    for mn in methodNames: taken.add(mn)
    for iNm in idxNames: taken.add(iNm)
    for t in ctor.tele: taken.add(t.name)
    var rhs = mkVar(methodNames[ci], loc)
    for t in ctor.tele:
      rhs = mkApp(rhs, mkVar(t.name, loc), loc)
      if mentionsFam(t.ty, famName):
        # Issue #113: split off a leading Pi telescope (empty = first-order,
        # identical to the old code below).
        let (hoTele, argIndices) = splitCtorArg(t.ty, famName, ctor.name,
                                               t.name, d.params.len,
                                               ctor.cloc)
        let (freshTele, hoNames, hoSubst) =
          freshenHoTele(hoTele, taken, ctor.cloc)
        var fresh = 0
        let argIndicesSub = substPreSeq(argIndices, hoSubst, fresh)
        var rec = mkVar(elimName, loc)
        for p in d.params: rec = mkApp(rec, mkVar(p.name, loc), loc)
        rec = mkApp(rec, mkVar("C", loc), loc)
        for mn in methodNames: rec = mkApp(rec, mkVar(mn, loc), loc)
        for ai in argIndicesSub: rec = mkApp(rec, ai, loc)
        var kApp = mkVar(t.name, loc)
        for hn in hoNames: kApp = mkApp(kApp, mkVar(hn, ctor.cloc), loc)
        rec = mkApp(rec, kApp, loc)
        # Issue #113: the method receives (fun x1..xn => elim C ms idx
        # (k x1 .. xn)), not a direct recursive call.
        var lam = rec
        for j in countdown(freshTele.high, 0):
          lam = mkLam(freshTele[j].name, freshTele[j].ty, lam, ctor.cloc)
        rhs = mkApp(rhs, lam, loc)
    result.add(SurfDecl(kind: dkRed, lhs: lhs, rhs: rhs, rloc: ctor.cloc))

proc elabDataDecl(d: SurfDecl, globals: var Globals, supply: var Supply,
                  ms: var MetaStore, dataInfos: var Table[string, SurfDecl]) =
  ## Experiment 5: desugar `data` to postulate/elim/red.
  ## Records the SurfDecl in dataInfos for coverage checking (issue #32).
  let loc = d.daloc
  # name clash check for the generated binders
  for p in d.params:
    if p.name == "C":
      raise elabErr(loc, "data parameter may not be named 'C' (reserved for the motive)")
  for ctor in d.ctors:
    for t in ctor.tele:
      if t.name == "C":
        raise elabErr(ctor.cloc, "constructor binder may not be named 'C' (reserved)")
  # type former
  elabPostulateDecl(d.dname, mkPis(d.params, d.indexTy, loc), loc,
                    globals, supply, ms, false)
  # constructors
  for ctor in d.ctors:
    discard extractIndices(ctor.retTy, d.dname, d.params.len, ctor.cloc)
    var fullTele = d.params & ctor.tele
    elabPostulateDecl(ctor.name, mkPis(fullTele, ctor.retTy, ctor.cloc),
                      ctor.cloc, globals, supply, ms, false)
  # eliminator
  let elimName = elimNameFor(d.dname)
  let (elimTy, methodNames) = genElimTy(d, loc)
  elabPostulateDecl(elimName, elimTy, loc, globals, supply, ms, true)
  # reduction rules
  for rd in genRedDecls(d, elimName, methodNames, loc):
    elabRedDecl(rd.lhs, rd.rhs, rd.rloc, globals, supply, ms)
  # record for coverage checking (issue #32)
  dataInfos[d.dname] = d
  # Issue #80: register the constructor disjointness facts (noConfusion /
  # noCycle) for unification. The constructors were just postulated above,
  # so each name resolves to a tR global.
  var ctorIds: seq[(int, string)] = @[]
  for ctor in d.ctors:
    let ctm = globals[ctor.name].tm
    if ctm.kind != tR:
      raise elabErr(ctor.cloc, "internal: constructor '" & ctor.name &
        "' did not elaborate to a global reference")
    ctorIds.add((ctm.refId, ctor.name))
  ms.registerDataCtors(globals[d.dname].tm.refId, d.dname, ctorIds)
  # Issue #115: register Nat's constructor refIds on the supply so the
  # core's conversion can equate wNatLit(k) with suc-chains
  # (definitionally equal per Issue #93). Carried on the supply (not a
  # module global) so it works under compile-time macro evaluation.
  if d.dname == "Nat":
    for ctor in d.ctors:
      let ctm = globals[ctor.name].tm
      if ctm.kind == tR:
        if ctor.name == "zero": supply.natZeroRefId = ctm.refId
        elif ctor.name == "suc": supply.natSucRefId = ctm.refId

# --- Capture-avoiding PreTerm substitution ----------------------------------
# Needed by issue #32 (indexed clause defs): instantiating the motive and
# refining scrutinee index variables per constructor must not capture
# user-written binders.

proc freeVarsPreAux(t: PreTerm, bound: var HashSet[string],
                    acc: var HashSet[string]) =
  case t.kind
  of pkVar:
    if t.name notin bound: acc.incl(t.name)
  of pkApp, pkPair, pkAnn:
    freeVarsPreAux(t.c1, bound, acc)
    freeVarsPreAux(t.c2, bound, acc)
  of pkPi, pkLam, pkSigma:
    if not t.c1.isNil: freeVarsPreAux(t.c1, bound, acc)
    let shadowed = t.name in bound
    bound.incl(t.name)
    freeVarsPreAux(t.c2, bound, acc)
    if not shadowed: bound.excl(t.name)
  of pkFst, pkSnd:
    freeVarsPreAux(t.c1, bound, acc)
  of pkLet:
    if not t.c1.isNil: freeVarsPreAux(t.c1, bound, acc)
    freeVarsPreAux(t.c2, bound, acc)
    let shadowed = t.name in bound
    bound.incl(t.name)
    freeVarsPreAux(t.c3, bound, acc)
    if not shadowed: bound.excl(t.name)
  else: discard

proc freeVarsPre(t: PreTerm): HashSet[string] =
  result = initHashSet[string]()
  var bound = initHashSet[string]()
  freeVarsPreAux(t, bound, result)

proc allNamesPreAux(t: PreTerm, acc: var HashSet[string]) =
  ## Every variable and binder name in the term (over-approximation,
  ## for picking fresh names).
  case t.kind
  of pkVar:
    acc.incl(t.name)
  of pkPi, pkLam, pkSigma, pkLet:
    if t.name.len > 0: acc.incl(t.name)
    if not t.c1.isNil: allNamesPreAux(t.c1, acc)
    allNamesPreAux(t.c2, acc)
    if t.kind == pkLet and not t.c3.isNil: allNamesPreAux(t.c3, acc)
  of pkApp, pkPair, pkAnn:
    allNamesPreAux(t.c1, acc)
    allNamesPreAux(t.c2, acc)
  of pkFst, pkSnd:
    allNamesPreAux(t.c1, acc)
  else: discard

proc allNamesPre(t: PreTerm): HashSet[string] =
  result = initHashSet[string]()
  allNamesPreAux(t, result)

proc substPre(t: PreTerm, name: string, repl: PreTerm,
              fresh: var int): PreTerm =
  ## Capture-avoiding substitution of free variable `name` by `repl`.
  ## `fresh` supplies suffixes when a binder must be renamed to avoid
  ## capturing free variables of `repl`.
  case t.kind
  of pkVar:
    if t.name == name: repl else: t
  of pkApp:
    mkApp(substPre(t.c1, name, repl, fresh),
          substPre(t.c2, name, repl, fresh), t.loc)
  of pkPi, pkLam, pkSigma:
    let d = if t.c1.isNil: nil else: substPre(t.c1, name, repl, fresh)
    if t.name == name or t.name.len == 0:
      # shadowed (or anonymous): the body cannot mention `name`
      case t.kind
      of pkPi: mkPi(t.name, d, t.c2, t.loc, t.impl, t.erased, t.qty)
      of pkLam: mkLam(t.name, d, t.c2, t.loc, t.impl, t.erased, t.qty)
      else: mkSigma(t.name, d, t.c2, t.loc, t.erased)
    else:
      var bname = t.name
      var body = t.c2
      if bname in freeVarsPre(repl):
        bname = bname & "'" & $fresh
        inc fresh
        body = substPre(t.c2, t.name, mkVar(bname, t.loc), fresh)
      body = substPre(body, name, repl, fresh)
      case t.kind
      of pkPi: mkPi(bname, d, body, t.loc, t.impl, t.erased, t.qty)
      of pkLam: mkLam(bname, d, body, t.loc, t.impl, t.erased, t.qty)
      else: mkSigma(bname, d, body, t.loc, t.erased)
  of pkPair:
    mkPair(substPre(t.c1, name, repl, fresh),
           substPre(t.c2, name, repl, fresh), t.loc)
  of pkFst:
    mkFst(substPre(t.c1, name, repl, fresh), t.loc)
  of pkSnd:
    mkSnd(substPre(t.c1, name, repl, fresh), t.loc)
  of pkLet:
    let ann = if t.c1.isNil: nil else: substPre(t.c1, name, repl, fresh)
    let v = substPre(t.c2, name, repl, fresh)
    if t.name == name or t.name.len == 0:
      mkLet(t.name, ann, v, t.c3, t.loc)
    else:
      var bname = t.name
      var body = t.c3
      if bname in freeVarsPre(repl):
        bname = bname & "'" & $fresh
        inc fresh
        body = substPre(t.c3, t.name, mkVar(bname, t.loc), fresh)
      body = substPre(body, name, repl, fresh)
      mkLet(bname, ann, v, body, t.loc)
  of pkAnn:
    mkAnn(substPre(t.c1, name, repl, fresh),
          substPre(t.c2, name, repl, fresh), t.loc)
  else:
    t

proc substPreN(t: PreTerm, subs: seq[(string, PreTerm)],
               fresh: var int): PreTerm =
  ## Apply a list of substitutions in order.
  result = t
  for (n, r) in subs:
    result = substPre(result, n, r, fresh)

proc substPreSeq(ts: seq[PreTerm], subs: seq[(string, PreTerm)],
                 fresh: var int): seq[PreTerm] =
  result = @[]
  for t in ts:
    result.add(substPreN(t, subs, fresh))

# --- Issue #32: clause-style definitions --------------------------------------
# `def name : Ty` with `| pat1 .. patn = rhs` clauses, compiled to an
# eliminator application. The scrutinee is the first explicit argument
# whose type is a data type; patterns are variables or constructor
# applications (no nesting, no catch-all yet); recursive calls become IH
# applications. Indexed families are supported: the scrutinee's type may
# be `D params idxs...` with variable indices; the motive abstracts over
# the indices and each method refines them to the constructor's return
# indices.

proc scrutineeDataName(ty: PreTerm,
                       dataInfos: Table[string, SurfDecl]): string =
  ## Find the first explicit Pi domain in `ty` that names a data type.
  ## Returns the data type name, or "" if none.
  var cur = ty
  while cur.kind == pkPi:
    if not cur.impl:
      let dom = cur.c1
      if dom.kind == pkVar and dataInfos.hasKey(dom.name):
        return dom.name
      # also handle `D params` applications
      var h = dom
      while h.kind == pkApp: h = h.c1
      if h.kind == pkVar and dataInfos.hasKey(h.name):
        return h.name
    cur = cur.c2
  ""

proc patHeadName(pat: PreTerm, ctorNames: seq[string]): tuple[isCtor: bool,
    name: string, args: seq[PreTerm]] =
  ## Decompose a pattern: either a variable or a constructor application.
  ## A bare variable naming a constructor is a nullary constructor pattern.
  if pat.kind == pkVar:
    if pat.name in ctorNames:
      return (true, pat.name, @[])
    return (false, pat.name, @[])
  var h = pat
  var args: seq[PreTerm] = @[]
  while h.kind == pkApp:
    args.add(h.c2)
    h = h.c1
  if h.kind == pkVar:
    var rargs: seq[PreTerm] = @[]
    for i in countdown(args.high, 0): rargs.add(args[i])
    return (true, h.name, rargs)
  (false, "", @[])

proc replaceRecCalls(rhs: PreTerm, fname: string, recVar: string,
                    ihName: string): PreTerm =
  ## Replace `fname recVar rest...` (recursive call on recVar in the
  ## scrutinee position) with `ihName rest...` (IH application).
  ## MVP: only handles the case where recVar is the first (scrutinee)
  ## argument. Calls with recVar elsewhere are left alone for the
  ## termination checker (issue #36) to reject.
  case rhs.kind
  of pkApp:
    # Check if this is `f recVar ...` — flatten the spine
    var spine: seq[PreTerm] = @[]
    var h = rhs
    while h.kind == pkApp:
      spine.add(h.c2)
      h = h.c1
    var rspine: seq[PreTerm] = @[]
    for i in countdown(spine.high, 0): rspine.add(spine[i])
    spine = rspine
    if h.kind == pkVar and h.name == fname and spine.len > 0:
      let a0 = spine[0]
      if a0.kind == pkVar and a0.name == recVar:
        # Build `ihName` applied to args after the scrutinee
        var res = mkVar(ihName, rhs.loc)
        for j in 1 ..< spine.len:
          res = mkApp(res, replaceRecCalls(spine[j], fname, recVar, ihName),
                      rhs.loc)
        return res
    # Not a structural recursive call; recurse into children
    result = rhs
    result.c1 = replaceRecCalls(rhs.c1, fname, recVar, ihName)
    result.c2 = replaceRecCalls(rhs.c2, fname, recVar, ihName)
  of pkLam:
    result = rhs
    result.c2 = replaceRecCalls(rhs.c2, fname, recVar, ihName)
    if rhs.c1 != nil:
      result.c1 = replaceRecCalls(rhs.c1, fname, recVar, ihName)
  of pkPi:
    result = rhs
    result.c1 = replaceRecCalls(rhs.c1, fname, recVar, ihName)
    result.c2 = replaceRecCalls(rhs.c2, fname, recVar, ihName)
  of pkPair:
    result = rhs
    result.c1 = replaceRecCalls(rhs.c1, fname, recVar, ihName)
    result.c2 = replaceRecCalls(rhs.c2, fname, recVar, ihName)
  else:
    result = rhs

proc checkClauseTermination(rhs: PreTerm, fname: string, loc: Loc) =
  ## Issue #36: clause-level structural recursion check.
  ## After `replaceRecCalls` has rewritten structural self-calls on direct
  ## pattern subterms into IH applications, any remaining reference to
  ## `fname` is a non-structurally-recursive self-call (on the original
  ## scrutinee, a constructed/growing value, or an unrelated argument).
  ## Reject it here with a located, name-aware error instead of letting
  ## elaboration fail later with a confusing "unbound variable".
  var bound: seq[string] = @[]
  proc walk(t: PreTerm) =
    case t.kind
    of pkVar:
      if t.name == fname and t.name notin bound:
        raise elabErr(t.loc,
          "non-structurally-recursive call in 'def " & fname & "': '" &
          fname & "' referenced outside a structural recursive call; " &
          "recursive calls must be on direct subterms of the clause pattern")
    of pkApp:
      let spine = flattenAppSpine(t)
      if spine[0].kind == pkVar and spine[0].name == fname and
         spine[0].name notin bound:
        let badArg = if spine.len > 1: $spine[1] else: $t
        raise elabErr(t.loc,
          "non-structurally-recursive call in 'def " & fname & "': '" &
          fname & "' applied to '" & badArg &
          "', which is not a direct subterm of the clause pattern")
      for s in spine: walk(s)
    of pkLam, pkPi:
      if t.c1 != nil: walk(t.c1)
      bound.add(t.name)
      walk(t.c2)
      discard bound.pop()
    of pkLet:
      if t.c1 != nil: walk(t.c1)
      walk(t.c2)
      bound.add(t.name)
      walk(t.c3)
      discard bound.pop()
    of pkSigma:
      if t.c1 != nil: walk(t.c1)
      bound.add(t.name)
      walk(t.c2)
      discard bound.pop()
    of pkPair:
      walk(t.c1)
      walk(t.c2)
    of pkFst, pkSnd:
      walk(t.c1)
    of pkAnn:
      walk(t.c1)
      walk(t.c2)
    else:
      discard
  walk(rhs)

proc ctorHeadNamePre(t: PreTerm, ctorToData: Table[string, string],
                     bound: HashSet[string]): string =
  ## Head constructor name of a PreTerm application spine, or "" when the
  ## head is not a known data constructor. `bound` holds the in-scope
  ## variable names (telescope binders, pattern variables): a variable
  ## shadowing a constructor name is not a constructor.
  var cur = t
  while cur.kind == pkApp: cur = cur.c1
  if cur.kind == pkVar and cur.name notin bound and
     ctorToData.hasKey(cur.name):
    cur.name
  else: ""

proc noConfusionConflictPre(t1, t2: PreTerm,
                            ctorToData: Table[string, string],
                            bound: HashSet[string]): tuple[bad: bool,
    reason: string] =
  ## Issue #80: rigid noConfusion check on surface preterms. Returns
  ## bad=true with a named reason when t1/t2 are constructor-headed
  ## (possibly under applications) with distinct heads from the same
  ## datatype — or, when the heads agree, when some argument pair
  ## recursively conflicts (injectivity). Anything else (variables,
  ## defined functions, non-constructor heads) counts as compatible:
  ## the check fires only on positive rigid evidence, so it can never
  ## reject a well-typed clause.
  let h1 = ctorHeadNamePre(t1, ctorToData, bound)
  let h2 = ctorHeadNamePre(t2, ctorToData, bound)
  if h1.len > 0 and h2.len > 0:
    if h1 != h2:
      if ctorToData[h1] == ctorToData[h2]:
        return (true, "noConfusion: '" & h1 & "' and '" & h2 &
          "' are distinct constructors of '" & ctorToData[h1] & "'")
    else:
      var a1: seq[PreTerm] = @[]
      var c1 = t1
      while c1.kind == pkApp: a1.add(c1.c2); c1 = c1.c1
      var a2: seq[PreTerm] = @[]
      var c2 = t2
      while c2.kind == pkApp: a2.add(c2.c2); c2 = c2.c1
      if a1.len == a2.len:
        for i in 0 ..< a1.len:
          let r = noConfusionConflictPre(a1[i], a2[i], ctorToData, bound)
          if r.bad: return r
  (false, "")

proc elabClausesDecl(cd: ClausesDef, globals: var Globals, supply: var Supply,
                     ms: var MetaStore,
                     dataInfos: var Table[string, SurfDecl]): ElabDef =
  let loc = cd.loc
  resetQVars(ms)  # Issue #66: fresh quantity-variable scope per declaration
  # 1. Find the scrutinee's data type from the type signature.
  let dataName = scrutineeDataName(cd.ty, dataInfos)
  if dataName == "":
    raise elabErr(loc, "'def' clauses require the first explicit argument " &
      "to have a data type; none found in the type signature")
  let dataDecl = dataInfos[dataName]
  # Issue #80: constructor -> datatype map for the impossible-clause check.
  var ctorToData = initTable[string, string]()
  for dn, dd in dataInfos:
    for ctor in dd.ctors: ctorToData[ctor.name] = dn
  let elimName = elimNameFor(dataName)
  if not globals.hasKey(elimName):
    raise elabErr(loc, "eliminator '" & elimName & "' not found for data '" &
      dataName & "'")
  # 2. Count explicit Pis in the type to validate clause arity.
  var nExplicit = 0
  var cur = cd.ty
  while cur.kind == pkPi:
    if not cur.impl: inc nExplicit
    cur = cur.c2
  # 3. Process clauses: coverage + overlap.
  var covered: Table[string, int] = initTable[string, int]()  # ctor -> clause idx
  var ctorNames: seq[string] = @[]
  for ctor in dataDecl.ctors: ctorNames.add(ctor.name)
  for ci, cl in cd.clauses:
    if cl.pats.len != nExplicit:
      raise elabErr(cl.cloc, "clause has " & $cl.pats.len & " patterns but " &
        "the type has " & $nExplicit & " explicit arguments")
    let (isCtor, headName, _) = patHeadName(cl.pats[0], ctorNames)
    if not isCtor:
      raise elabErr(cl.cloc, "first pattern must be a constructor pattern " &
        "(no variable/catch-all patterns yet)")
    if headName notin ctorNames:
      raise elabErr(cl.cloc, "'" & headName & "' is not a constructor of '" &
        dataName & "'")
    if covered.hasKey(headName):
      raise elabErr(cl.cloc, "overlapping clauses: '" & headName &
        "' already covered by the clause at " &
        $cd.clauses[covered[headName]].cloc.line & ":" &
        $cd.clauses[covered[headName]].cloc.col)
    covered[headName] = ci
  for ctor in dataDecl.ctors:
    if not covered.hasKey(ctor.name):
      raise elabErr(loc, "missing case for constructor '" & ctor.name &
        "' of '" & dataName & "'")
  # 4. Build the eliminator application as a PreTerm, then elaborate as a def.
  #    Supports indexed families: the scrutinee's type may be
  #    `D params idxs...` with variable indices.
  #    Motive C := lam (i0:Idx0)... . lam (_:D params i0..). Pi (rest...). Ret[i:=idx]
  #    Def:  proc name ... =
  #            elimD params C m_0 ... m_(k-1) idxs... x_s rest...
  #    The motive's trailing Pi and the methods' rest lambdas are all
  #    explicit (the elaborator rejects explicit application to an implicit
  #    Pi); the user-facing proc type keeps the declared implicit flags.
  var tele: seq[tuple[name: string, ty: PreTerm, impl: bool]] = @[]
  var tcur = cd.ty
  while tcur.kind == pkPi:
    tele.add((tcur.name, tcur.c1, tcur.impl))
    tcur = tcur.c2
  let retTy = tcur
  # Issue #80: telescope binder names for the impossible-clause check's
  # shadowing guard (a binder named like a constructor is not one).
  var teleNames = initHashSet[string]()
  for b in tele:
    if b.name.len > 0: teleNames.incl(b.name)
  # Binder hygiene: the compiler generates references to telescope binders
  # (scrutinee, rest args) by name, so duplicate names would misresolve.
  # "_" binders (from `->`) are unreferenceable — `_` parses as a hole —
  # so freshening them is semantics-preserving and needs no substitution.
  # Any other duplicate is rejected with a clear error.
  var seenTele = initHashSet[string]()
  var freshTele = 0
  for i in 0 ..< tele.len:
    let bn = tele[i].name
    if bn.len == 0 or bn == "_":
      if bn in seenTele:
        var nn = "_'c" & $freshTele
        inc freshTele
        while nn in seenTele:
          nn = "_'c" & $freshTele
          inc freshTele
        tele[i].name = nn
      seenTele.incl(tele[i].name)
    else:
      if bn in seenTele:
        raise elabErr(loc, "'def' clauses: duplicate binder name '" & bn &
          "' in the type; rename one of them")
      seenTele.incl(bn)
  # Find scrutinee position (first explicit argument)
  var sPos = -1
  for i, b in tele:
    if not b.impl:
      sPos = i
      break
  if sPos < 0:
    raise elabErr(loc, "'def' clauses need at least one explicit argument " &
      "(the scrutinee)")
  # Scrutinee domain analysis: `D params... idxs...`
  let domS = tele[sPos].ty
  let domSpine = flattenAppSpine(domS)
  if domSpine.len == 0 or domSpine[0].kind != pkVar or
     domSpine[0].name != dataName:
    raise elabErr(loc, "scrutinee type must be '" & dataName &
      "' applied to parameters and indices")
  let (indexTele, _) = flattenPiPre(dataDecl.indexTy)
  let nParams = dataDecl.params.len
  if domSpine.len - 1 != nParams + indexTele.len:
    raise elabErr(loc, "scrutinee type must apply '" & dataName & "' to " &
      $nParams & " parameter(s) and " & $indexTele.len & " index/indices")
  var paramTerms: seq[PreTerm] = @[]
  for i in 1 .. nParams:
    paramTerms.add(domSpine[i])
  var scrIdxTerms: seq[PreTerm] = @[]
  var scrIdxVars: seq[string] = @[]
  for i in 1 + nParams ..< domSpine.len:
    let t = domSpine[i]
    if t.kind != pkVar:
      raise elabErr(loc, "'def' clauses: scrutinee index must be a " &
        "variable (found '" & $t & "')")
    if t.name in scrIdxVars:
      raise elabErr(loc, "'def' clauses: duplicate scrutinee index " &
        "variable '" & t.name & "'")
    scrIdxTerms.add(t)
    scrIdxVars.add(t.name)
  # Parameter substitution: data-decl param names := actual param terms
  # (from the scrutinee's type; identity in the common case where the
  # def type binds the same names).
  var paramSubst: seq[(string, PreTerm)] = @[]
  for i, p in dataDecl.params:
    paramSubst.add((p.name, paramTerms[i]))
  var fresh = 0
  # Fresh motive index binder names, avoiding every name in sight.
  var usedNames = allNamesPre(cd.ty)
  for cl0 in cd.clauses:
    for p in cl0.pats: usedNames = usedNames + allNamesPre(p)
    usedNames = usedNames + allNamesPre(cl0.rhs)
  for ctor0 in dataDecl.ctors:
    for t in ctor0.tele: usedNames = usedNames + allNamesPre(t.ty)
    usedNames = usedNames + allNamesPre(ctor0.retTy)
  var motiveIdxNames: seq[string] = @[]
  for i in 0 ..< indexTele.len:
    var nm = "midx" & $i
    while nm in usedNames:
      nm = "midx" & $i & "_" & $fresh
      inc fresh
    usedNames.incl(nm)
    motiveIdxNames.add(nm)
  # Build motive C := lam (i0:Idx0)... . lam (_:D params i0..). cBody
  # where cBody = Pi (rest...). Ret with scrutinee index vars := i0...
  var midxSubst: seq[(string, PreTerm)] = @[]
  for j, v in scrIdxVars:
    midxSubst.add((v, mkVar(motiveIdxNames[j], loc)))
  var cBody = substPreN(retTy, midxSubst, fresh)
  for ti in countdown(tele.high, sPos + 1):
    let bn = if tele[ti].name.len > 0: tele[ti].name else: "x" & $ti
    cBody = mkPi(bn, substPreN(tele[ti].ty, midxSubst, fresh), cBody, loc)
  var scrTyMotive = mkVar(dataName, loc)
  for pt in paramTerms: scrTyMotive = mkApp(scrTyMotive, pt, loc)
  for mn in motiveIdxNames: scrTyMotive = mkApp(scrTyMotive, mkVar(mn, loc), loc)
  var motive = mkLam("_motive", scrTyMotive, cBody, loc)
  # Issue #112: later index domains may mention earlier index binders
  # (dependent index telescopes); the motive binds midx0, midx1, ...,
  # so substitute old->new across the telescope in dependency order
  # (a no-op for non-dependent telescopes).
  var idxSubst: seq[(string, PreTerm)] = @[]
  var indexTysSub: seq[PreTerm] = @[]
  for j in 0 ..< indexTele.len:
    indexTysSub.add(substPreN(substPreN(indexTele[j].ty, paramSubst, fresh),
                              idxSubst, fresh))
    idxSubst.add((indexTele[j].name, mkVar(motiveIdxNames[j], loc)))
  for j in countdown(motiveIdxNames.high, 0):
    motive = mkLam(motiveIdxNames[j], indexTysSub[j], motive, loc)
  # Build methods, one per constructor (in dataDecl order)
  var methods: seq[PreTerm] = @[]
  for ctor in dataDecl.ctors:
    let ci = covered[ctor.name]
    let cl = cd.clauses[ci]
    let (_, _, patArgs) = patHeadName(cl.pats[0], ctorNames)
    if patArgs.len != ctor.tele.len:
      raise elabErr(cl.cloc, "constructor '" & ctor.name & "' takes " &
        $ctor.tele.len & " arguments but pattern has " & $patArgs.len)
    # Pattern arg names (must be variables; no nested patterns yet)
    var argNames: seq[string] = @[]
    for pa in patArgs:
      if pa.kind != pkVar:
        raise elabErr(cl.cloc, "'def' clauses: constructor arguments " &
          "must be variables (no nested patterns)")
      argNames.add(pa.name)
    # Remaining patterns must be variables; collect explicit rest names
    var restPatNames: seq[string] = @[]
    var seenPats = initHashSet[string]()
    for pn in argNames:
      if pn in seenPats:
        raise elabErr(cl.cloc, "duplicate pattern variable '" & pn & "'")
      seenPats.incl(pn)
    var pi = 1
    for ti in sPos + 1 .. tele.high:
      if not tele[ti].impl:
        if cl.pats[pi].kind != pkVar:
          raise elabErr(cl.cloc, "'def' clauses: non-scrutinee patterns " &
            "must be variables")
        if cl.pats[pi].name in seenPats:
          raise elabErr(cl.cloc, "duplicate pattern variable '" &
            cl.pats[pi].name & "'")
        seenPats.incl(cl.pats[pi].name)
        restPatNames.add(cl.pats[pi].name)
        inc pi
    # Pattern variables must not shadow other telescope binders (the
    # method body rebinds rest implicits by their tele names, so a
    # colliding pattern variable would be silently misread).
    for ti, b in tele:
      if ti != sPos and b.name.len > 0 and b.name in seenPats and
         b.name notin restPatNames:
        raise elabErr(cl.cloc, "pattern variable '" & b.name &
          "' shadows argument '" & b.name & "'; rename the pattern variable")
    # Name substitution: constructor tele names := pattern names
    var nameSubst: seq[(string, PreTerm)] = @[]
    for i, tn in ctor.tele:
      nameSubst.add((tn.name, mkVar(argNames[i], loc)))
    # Constructor return indices, with params and tele names substituted
    var retIdx = substPreSeq(extractIndices(ctor.retTy, dataName, nParams,
                                            ctor.cloc), paramSubst, fresh)
    retIdx = substPreSeq(retIdx, nameSubst, fresh)
    # Issue #80: impossible-clause check — the constructor's return indices
    # must be compatible with the scrutinee's indices. A rigid noConfusion
    # conflict (e.g. clause `nil` against a scrutinee of type `Vec A (suc
    # n)`) is rejected here with a named error instead of failing later
    # with a confusing unification/conversion error. (Currently the
    # scrutinee indices are always variables, so this fires once rigid
    # scrutinee indices are allowed; the check itself is tested directly.)
    # Pattern variables shadowing constructor names are excluded via bound.
    var bound80 = teleNames
    for an in argNames: bound80.incl(an)
    for j in 0 ..< min(scrIdxTerms.len, retIdx.len):
      let nc = noConfusionConflictPre(retIdx[j], scrIdxTerms[j], ctorToData,
                                      bound80)
      if nc.bad:
        raise elabErr(cl.cloc, "impossible clause for constructor '" &
          ctor.name & "': " & nc.reason)
    # Index refinement for this method: scrutinee idx vars := ret indices
    var idxSubst: seq[(string, PreTerm)] = @[]
    for j, v in scrIdxVars:
      idxSubst.add((v, retIdx[j]))
    # Constructor argument types with params/names substituted
    var argTys: seq[PreTerm] = @[]
    for te in ctor.tele:
      argTys.add(substPreN(substPreN(te.ty, paramSubst, fresh),
                           nameSubst, fresh))
    # Build method body: lam (args...). lam (ihs...). lam (rest...). rhs'
    var rhs = substPreN(cl.rhs, idxSubst, fresh)
    # Identify recursive args and their IH names/types
    var ihTys: seq[PreTerm] = @[]
    var ihCount = 0
    for ti, te in ctor.tele:
      if mentionsFam(te.ty, dataName):
        # Issue #113: clause compilation passes a bare recursive call for
        # each recursive argument; higher-order arguments need the
        # under-binder lambda form, which is not implemented here yet.
        let (clHoTele, _) = splitCtorArg(te.ty, dataName, ctor.name, te.name,
                                        nParams, ctor.cloc)
        if clHoTele.len > 0:
          raise elabErr(cl.cloc, "constructor '" & ctor.name &
            "' has a higher-order recursive argument '" & te.name &
            "'; clause-style definitions over such datatypes are not yet " &
            "supported (use the '" & elimNameFor(dataName) &
            "' eliminator directly)")
        let ihN = "ih" & $ihCount
        if ihN in seenPats:
          raise elabErr(cl.cloc, "pattern variable '" & ihN &
            "' clashes with a generated induction hypothesis name; " &
            "rename the pattern variable")
        var argIdx = substPreSeq(extractIndices(te.ty, dataName, nParams,
                                                ctor.cloc), paramSubst, fresh)
        argIdx = substPreSeq(argIdx, nameSubst, fresh)
        # IH type: the motive tail with index binders := this arg's indices
        var ihTy = cBody
        for j, mn in motiveIdxNames:
          ihTy = substPre(ihTy, mn, argIdx[j], fresh)
        ihTys.add(ihTy)
        inc ihCount
        # Replace recursive calls on this variable
        rhs = replaceRecCalls(rhs, cd.name, argNames[ti], ihN)
    # Issue #36: any self-reference surviving IH-rewriting is a
    # non-structural recursive call — reject with a termination error.
    checkClauseTermination(rhs, cd.name, cl.cloc)
    # Build the lambda nest: args, then IHs (in tele order, IH after its
    # var), then rest args. Rest lambdas are explicit to match the
    # all-explicit motive tail.
    var body = rhs
    var rpi = 0
    for ti in countdown(tele.high, sPos + 1):
      var bn: string
      if tele[ti].impl:
        bn = if tele[ti].name.len > 0: tele[ti].name else: "x" & $ti
      else:
        bn = restPatNames[rpi]
        inc rpi
      let bty = substPreN(substPreN(tele[ti].ty, paramSubst, fresh),
                          idxSubst, fresh)
      body = mkLam(bn, bty, body, loc)
    # constructor args and IHs (reverse order, IH after its var)
    for ti in countdown(ctor.tele.high, 0):
      if mentionsFam(ctor.tele[ti].ty, dataName):
        # IH for this var; IHs were numbered in forward order
        var fwdIdx = 0
        for tj in 0 ..< ti:
          if mentionsFam(ctor.tele[tj].ty, dataName): inc fwdIdx
        body = mkLam("ih" & $fwdIdx, ihTys[fwdIdx], body, loc)
      body = mkLam(argNames[ti], argTys[ti], body, loc)
    methods.add(body)
  # Build the full application:
  #   elimD params... C m_0 ... m_(k-1) idxs... x_s rest...
  var app = mkVar(elimName, loc)
  for i, p in dataDecl.params:
    if not p.impl:
      app = mkApp(app, paramTerms[i], loc)
    # implicit params: the elaborator inserts metas, solved by unification
    # against the motive/method types below
  app = mkApp(app, motive, loc)
  for m in methods: app = mkApp(app, m, loc)
  for it in scrIdxTerms: app = mkApp(app, it, loc)
  var procTele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]] = @[]
  var restVars: seq[string] = @[]
  for i, b in tele:
    let bn = if b.name.len > 0: b.name else: "x" & $i
    # The proc syntax supports implicits; keep them.
    # Note: data tele doesn't carry qty yet; default to qOmega
    procTele.add((bn, b.ty, b.impl, false, Qty(isVar: false, q: qOmega)))
    if i > sPos:
      restVars.add(bn)
  # scrutinee first, then the remaining telescope in order
  # (implicit rest args applied explicitly: the motive tail is all-explicit)
  app = mkApp(app, mkVar(procTele[sPos].name, loc), loc)
  for rv in restVars:
    app = mkApp(app, mkVar(rv, loc), loc)
  # Build the SurfDef and elaborate
  let sdef = SurfDef(name: cd.name, tele: procTele, retTy: retTy, body: app,
                     loc: loc)
  elabDefDecl(sdef, globals, supply, ms)

proc elabDecl(d: SurfDecl, globals: var Globals, supply: var Supply,
              ms: var MetaStore,
              dataInfos: var Table[string, SurfDecl]): seq[ElabDef] =
  ## Elaborate one top-level declaration (Experiment 5: data desugars
  ## to postulate/elim/red and goes through the same path).
  ## Returns the defs it produced (only dkDef yields one directly).
  case d.kind
  of dkDef:
    result.add(elabDefDecl(d.def, globals, supply, ms))
  of dkPostulate:
    elabPostulateDecl(d.name, d.ty, d.dloc, globals, supply, ms, false)
  of dkElim:
    elabPostulateDecl(d.name, d.ty, d.dloc, globals, supply, ms, true)
  of dkRed:
    elabRedDecl(d.lhs, d.rhs, d.rloc, globals, supply, ms)
  of dkData:
    elabDataDecl(d, globals, supply, ms, dataInfos)
  of dkClauses:
    result.add(elabClausesDecl(d.clausesDef, globals, supply, ms, dataInfos))
  of dkImport:
    # Issue #49: `import` needs a file context (base directory for path
    # resolution); the ModuleDriver below handles it. A bare elabCheck
    # over a source string has no directory to resolve against.
    raise elabErr(d.iloc, "import \"" & d.ipath &
      "\" requires a file context; use elabCheckFile")

proc elabCheckState*(src: string, handlers: seq[ConvHandler] = @[]):
    tuple[defs: seq[ElabDef], ms: MetaStore] =
  ## Parse, elaborate, and typecheck a surface program, decl by decl,
  ## returning the MetaStore too (for tooling: hole info, issue #58).
  ## Raises ParseError (carries loc) or ElabError (carries loc).
  let decls = parseProgram(src)
  var globals: Globals = initTable[string, GEntry]()
  var supply = Supply()
  var ms = initMetaStore()  # includes fresh convCache (Experiment 10)
  for h in handlers: ms.convHandlers.add(h)
  var dataInfos: Table[string, SurfDecl] = initTable[string, SurfDecl]()
  var defs: seq[ElabDef] = @[]
  for d in decls:
    let eds = elabDecl(d, globals, supply, ms, dataInfos)
    for ed in eds:
      # Issue #64: verify linear/erased usage in the elaborated term
      try:
        checkUsage(ed.tmTm)
      except UsageError as e:
        raise elabErr(ed.loc, "usage error in '" & ed.name & "': " & e.msg)
      defs.add(ed)
  (defs, ms)

proc elabCheck*(src: string, handlers: seq[ConvHandler] = @[]): seq[ElabDef] =
  ## Parse, elaborate, and typecheck a surface program, decl by decl.
  ## Later decls may mention earlier ones (via closed R nodes).
  ## Raises ParseError (carries loc) or ElabError (carries loc).
  ## Experiment 41: `handlers` installs conversion decision procedures
  ## for the dynamic extent of the whole program (e.g. @[cacheConvHandler]).
  elabCheckState(src, handlers).defs

proc elabCheckHoles*(src: string): tuple[defs: seq[ElabDef], ms: MetaStore,
    errLoc: Loc, errMsg: string] =
  ## Issue #58: hole-tolerant elaboration for tooling (LSP hover).
  ## Like elabCheckState, but unsolved metavariables (surface `_` holes)
  ## do not fail the declaration: open defs are registered postulate-style
  ## and the core re-check is skipped for them. Elaborates decl by decl
  ## and stops at the first declaration that fails for any *other* reason,
  ## returning the accumulated state so holes from the successful prefix
  ## stay queryable; the first failure is reported via errLoc/errMsg
  ## (both empty when the whole document elaborated). Raises ParseError
  ## as usual (an unparseable document has no meaningful hole state).
  let decls = parseProgram(src)
  var globals: Globals = initTable[string, GEntry]()
  var supply = Supply()
  var ms = initMetaStore()
  ms.allowHoles = true
  var dataInfos: Table[string, SurfDecl] = initTable[string, SurfDecl]()
  var defs: seq[ElabDef] = @[]
  var errLoc = noLoc
  var errMsg = ""
  for d in decls:
    try:
      let eds = elabDecl(d, globals, supply, ms, dataInfos)
      for ed in eds:
        # checkUsage is meta-safe (tMeta is a no-op case); open defs keep
        # their holes in tmTm.
        try:
          checkUsage(ed.tmTm)
        except UsageError as e:
          raise elabErr(ed.loc, "usage error in '" & ed.name & "': " & e.msg)
        defs.add(ed)
    except ElabError as e:
      # A partially elaborated decl may have recorded holes before the
      # failure; keep the successful prefix and stop.
      errLoc = e.loc
      errMsg = e.msg
      break
  (defs, ms, errLoc, errMsg)

# --- Issue #49: multi-file programs via `import` ------------------------------

type
  ModuleDriver* = object
    ## Stateful driver for elaborating multi-file programs. `import "path"`
    ## declarations resolve relative to the importing file's directory and
    ## merge unqualified into one shared environment (decisions.org: flat,
    ## unqualified imports for v1; revisit on first name collision).
    globals*: Globals
    supply*: Supply
    ms*: MetaStore
    dataInfos*: Table[string, SurfDecl]
    loading*: seq[string]        # canonical paths on the import stack
    modHash*: Table[string, Hash] # canonical path -> content hash (skip unchanged)
    elabCount*: Table[string, int] # canonical path -> times elaborated

proc initModuleDriver*(handlers: seq[ConvHandler] = @[]): ModuleDriver =
  result.ms = initMetaStore()  # includes fresh convCache (Experiment 10)
  for h in handlers: result.ms.convHandlers.add(h)
  result.globals = initTable[string, GEntry]()
  result.dataInfos = initTable[string, SurfDecl]()

proc elabFile*(drv: var ModuleDriver, path: string,
               importLoc: Loc = noLoc): seq[ElabDef]
  ## Forward: elaborates one file (defined below); elabDeclsDir recurses
  ## through it for nested imports.

proc elabDeclsDir*(drv: var ModuleDriver, decls: seq[SurfDecl],
                   baseDir: string, srcLabel: string): seq[ElabDef] =
  ## Elaborate `decls` into the driver's environment, recursively
  ## elaborating `import` declarations first. Import paths resolve relative
  ## to `baseDir` (the importing source's directory); `srcLabel` names the
  ## importing source in error messages (a file path, or "<eponymBlock>").
  ## Returns the defs declared by `decls` themselves; imported definitions
  ## live in `drv.globals`. Raises ElabError on cycles, missing files, or
  ## elaboration failures.
  for d in decls:
    if d.kind == dkImport:
      let target = if isAbsolute(d.ipath): d.ipath
                   else: baseDir / d.ipath
      if not fileExists(target):
        raise elabErr(d.iloc, "import \"" & d.ipath & "\": file not found " &
          "(resolved to '" & target & "', imported from '" & srcLabel & "')")
      discard drv.elabFile(target, d.iloc)
    else:
      let eds = elabDecl(d, drv.globals, drv.supply, drv.ms, drv.dataInfos)
      for ed in eds:
        # Issue #64: verify linear/erased usage in the elaborated term
        try:
          checkUsage(ed.tmTm)
        except UsageError as e:
          raise elabErr(ed.loc, "usage error in '" & ed.name & "': " & e.msg)
        result.add(ed)

proc elabFile*(drv: var ModuleDriver, path: string,
               importLoc: Loc = noLoc): seq[ElabDef] =
  ## Elaborate the file at `path`, recursively elaborating its `import`
  ## declarations first. Returns the defs declared by this file itself;
  ## imported definitions live in `drv.globals`.
  ## Raises ElabError (located) on import cycles, missing files, parse
  ## errors, or elaboration failures. Files already elaborated with
  ## identical content are skipped via the content-hash cache.
  let cpath =
    try:
      when nimvm:
        # Issue #131: expandFilename needs realpath/getcwd (importc), which
        # the Nim VM cannot call. Imports elaborated at compile time (via
        # eponymBlock) always resolve to absolute paths (callerDir is absolute),
        # so lexical normalization suffices there; symlinks are resolved
        # only at runtime.
        normalizedPath(path)
      else:
        expandFilename(path)
    except OSError:
      raise elabErr(importLoc, "import '" & path & "': file not found" &
        (if drv.loading.len > 0: " (imported from '" & drv.loading[^1] & "')"
         else: ""))
  if cpath in drv.loading:
    raise elabErr(importLoc, "import cycle detected: " &
      (drv.loading & @[cpath]).join(" -> "))
  let src =
    try: readFile(cpath)
    except IOError as e:
      raise elabErr(importLoc, "cannot read '" & cpath & "': " & e.msg)
  let h = hash(src)
  if drv.modHash.getOrDefault(cpath, 0) == h:
    return @[]  # unchanged since this driver elaborated it: skip
  let decls =
    try: parseProgram(src)
    except ParseError as e:
      raise elabErr(e.loc, "in imported file '" & cpath & "': " & e.msg)
  drv.loading.add(cpath)
  try:
    result = drv.elabDeclsDir(decls, parentDir(cpath), cpath)
  finally:
    discard drv.loading.pop()
  drv.modHash[cpath] = h
  drv.elabCount[cpath] = drv.elabCount.getOrDefault(cpath, 0) + 1

proc elabCheckDir*(src: string, baseDir: string,
                   handlers: seq[ConvHandler] = @[]): seq[ElabDef] =
  ## Issue #131: like elabCheck, but `import "path.ep"` declarations resolve
  ## relative to `baseDir` instead of failing with "requires a file context".
  ## For embedded sources (e.g. eponymBlock) that live in a Nim file rather
  ## than an .ep file on disk. Returns the defs declared by `src` itself;
  ## raises ParseError or ElabError on failure.
  let decls = parseProgram(src)  # ParseError propagates
  var drv = initModuleDriver(handlers)
  drv.elabDeclsDir(decls, baseDir, "<eponymBlock>")

proc elabCheckFile*(path: string,
                    handlers: seq[ConvHandler] = @[]): seq[ElabDef] =
  ## Issue #49: elaborate a file on disk with `import` support (fresh driver).
  ## Like elabCheck, but `import "rel/path.ep"` declarations resolve relative
  ## to the file's directory. Raises ElabError (located) on failure.
  var drv = initModuleDriver(handlers)
  drv.elabFile(path)

proc elabPrelude*(src: string): tuple[globals: Globals, ms: MetaStore,
                                      supply: Supply] =
  ## Elaborate a prelude program once; returns reusable state so per-term
  ## benchmarks (issue #19) don't re-elaborate the prelude every iteration.
  let decls = parseProgram(src)
  var globals: Globals = initTable[string, GEntry]()
  var supply = Supply()
  var ms = initMetaStore()  # includes fresh convCache (Experiment 10)
  var dataInfos: Table[string, SurfDecl] = initTable[string, SurfDecl]()
  for d in decls:
    discard elabDecl(d, globals, supply, ms, dataInfos)
  (globals, ms, supply)

proc checkTermElab*(pre: PreTerm, ctx: Ctx, globals: Globals,
                    ms: var MetaStore, supply: var Supply,
                    expTy: Term): Term =
  ## Check a single pre-term against an expected type (benchmark hook for
  ## issue #19). Returns the elaborated term; raises ElabError if ill-typed.
  checkTm(pre, ctx, globals, ms, supply, expTy)

when isMainModule:
  import times
  # --- Experiment 2's programs still elaborate --------------------------------
  let defs = elabCheck("""
proc twice (A : ?) (f : A -> A) (x : A) : A =
  f (f x)
proc constFn (A : ?) (B : ?) (x : A) (y : B) : A =
  x
proc pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A =
  (snd p, fst p)
""")
  assert defs.len == 3
  echo "ok: twice, constFn, pairSwap elaborate and check"

  let defs2 = elabCheck("""
proc myId (A : ?) (x : A) : A =
  x
proc useId (A : ?) (x : A) : A =
  myId A x
""")
  assert defs2.len == 2
  echo "ok: later defs can mention earlier defs"

  let defs3 = elabCheck("""
proc withLet (A : ?) (x : A) : A =
  let y : A = x in y
""")
  assert defs3.len == 1
  echo "ok: annotated let elaborates"

  # --- Experiment 3: implicit arguments inferred -------------------------------
  let defs4 = elabCheck("""
proc polyId {A : ?} (x : A) : A =
  x
proc usePolyId : 1 =
  polyId <>
proc constI {A : ?} {B : ?} (x : A) (y : B) : A =
  x
proc useConstI : 1 =
  constI <> <>
proc pairSwapI {A : ?} {B : ?} (p : Sig (u : A). B) : Sig (v : B). A =
  (snd p, fst p)
proc usePairSwapI : Sig (v : 1). 1 =
  pairSwapI (<>, <>)
""")
  assert defs4.len == 6
  echo "ok: implicit arguments inferred for polyId, constI, pairSwapI"

  # --- Experiment 3: unannotated lambdas and lets infer ------------------------
  let defs5 = elabCheck("""
proc idU : Pi (A : ?). A -> A =
  lam A. lam x. x
proc letU : 1 =
  let f = lam x. x in f <>
""")
  assert defs5.len == 2
  echo "ok: unannotated lambda and unannotated let infer"

  # --- failures carry surface locations ---------------------------------------
  proc expectElabErr(src: string, frag: string) =
    try:
      discard elabCheck(src)
      assert false, "expected ElabError for: " & src
    except ElabError as e:
      assert frag in e.msg, "missing '" & frag & "' in: " & e.msg
      assert e.loc.line > 0
      echo "ok: ElabError [" & frag & "] at line " & $e.loc.line &
        ", col " & $e.loc.col & ": " & e.msg.splitLines()[0]

  expectElabErr("proc bad (A : ?) (x : A) : A =\n  1\n",
    "does not match expected type")
  expectElabErr("proc bad : ? =\n  x\n", "unbound variable 'x'")
  expectElabErr("proc bad : 1 =\n  (<>, <>)\n",
    "checked against a non-Sigma type")
  expectElabErr("proc bad (A : ?) (p : Sig (u : A). A) : ? =\n  fst (snd p, fst p)\n",
    "not convertible")
  expectElabErr("proc bad (A : ?) : ? =\n  _\n",
    "unsolved metavariable")
  expectElabErr("proc bad : ? =\n  lam x. x x\n",
    "expected a function type")
  expectElabErr("proc bad : 1 =\n  polyIdBad <>\n",
    "unbound variable 'polyIdBad'")

  # --- annotated surface lambdas elaborate; mismatches caught by check --------
  let defs6 = elabCheck("""
proc constLam : Pi (A : ?) . A -> A =
  lam (A : ?) . lam (x : A) . x
""")
  assert defs6.len == 1
  echo "ok: annotated surface lambda elaborates"
  expectElabErr("proc bad : ? =\n  lam (x : ?) . x\n",
    "expected a function type")

  # --- Issue #65: Pi binders in type annotations are in scope ---------------
  let defs65 = elabCheck("""
postulate foo65 : (A : ?) -> A -> A
proc bar65 : (A : ?) -> A -> A =
  lam (A : ?) . lam (x : A) . x
proc useFoo65 : 1 =
  foo65 1 <>
""")
  assert defs65.len == 2  # postulates elaborate but return no ElabDef
  echo "ok: inline Pi binders in type annotations (#65)"

  # --- parse errors propagate with locations ----------------------------------
  try:
    discard elabCheck("proc bad (A : ?) : =\n  x\n")
    assert false, "expected ParseError"
  except ParseError as e:
    assert e.loc.line > 0
    echo "ok: ParseError at line " & $e.loc.line & ": " & e.msg.splitLines()[0]

  # --- Experiment 4: postulate / elim / red; reduction fires ------------------
  let boolDefs = elabCheck("""
postulate Bool : ?
postulate true : Bool
postulate false : Bool
elim boolElim : Pi (C : Bool -> ?). C true -> C false -> Pi (b : Bool). C b
red boolElim C t f true  = t
red boolElim C t f false = f
proc not (b : Bool) : Bool =
  boolElim (lam (u : Bool). Bool) false true b
proc notTrue : Bool = not true
proc notFalse : Bool = not false
""")
  assert boolDefs.len == 3
  # not true reduces to false; not false reduces to true.
  # The postulate refIds come from the argument positions: `not true`
  # is tApp(R_not, R_true), `not false` is tApp(R_not, R_false).
  let trueId = boolDefs[1].tmTm.arg.refId
  let falseId = boolDefs[2].tmTm.arg.refId
  assert trueId != falseId
  let notTrueV = eval(boolDefs[1].tmTm, @[])
  assert notTrueV.whnfKind == wRef and notTrueV.whnfRefId == falseId and
    notTrueV.whnfSpineLen == 0, "not true should reduce to false"
  let notFalseV = eval(boolDefs[2].tmTm, @[])
  assert notFalseV.whnfKind == wRef and notFalseV.whnfRefId == trueId and
    notFalseV.whnfSpineLen == 0, "not false should reduce to true"
  echo "ok: Bool eliminator reduces (not true = false, not false = true)"

  # Nat: constructor with arguments; recursive rule; stuck scrutinee
  let natDefs = elabCheck("""
postulate Nat : ?
postulate zero : Nat
postulate suc : Nat -> Nat
elim natElim : Pi (C : Nat -> ?). C zero -> (Pi (n : Nat). C n -> C (suc n)) -> Pi (n : Nat). C n
red natElim C z s zero    = z
red natElim C z s (suc n) = s n (natElim C z s n)
proc two : Nat = suc (suc zero)
proc add (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) m (lam (p : Nat). lam (ih : Nat). suc ih) n
proc four : Nat = add two two
proc stuckTest (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) zero (lam (p : Nat). lam (ih : Nat). p) n
""")
  assert natDefs.len == 4
  let twoTm = natDefs[0].tmTm  # suc (suc zero)
  let sucId = twoTm.fn.refId
  let zeroId = twoTm.arg.arg.refId
  proc sucDepth(v: Value): int =
    if v.whnfKind == wRef and v.whnfRefId == sucId and v.whnfSpineLen == 1:
      1 + sucDepth(v.whnfSpineArg(0))
    elif v.whnfKind == wRef and v.whnfRefId == zeroId and v.whnfSpineLen == 0:
      0
    else: -1000
  let depth4 = sucDepth(eval(natDefs[2].tmTm, @[]))
  assert depth4 == 4, "add two two should reduce to suc^4 zero, got depth " & $depth4
  echo "ok: Nat eliminator reduces (add two two = 4); neutral scrutinee stays stuck"

  # red errors: duplicate rule, non-eliminator, wrong arity
  expectElabErr("""
postulate Bool : ?
postulate true : Bool
elim boolElim : Pi (C : Bool -> ?). C true -> Pi (b : Bool). C b
red boolElim C t true = t
red boolElim C t true = t
""", "duplicate reduction rule")
  expectElabErr("""
postulate Bool : ?
postulate true : Bool
postulate notElim : Bool -> Bool
red notElim x true = x
""", "not an eliminator")
  expectElabErr("""
postulate Bool : ?
postulate true : Bool
elim boolElim : Pi (C : Bool -> ?). C true -> Pi (b : Bool). C b
red boolElim C true = true
""", "takes 3 arguments")

  # --- Experiment 5: data declarations --------------------------------------
  # data Nat: non-indexed, desugars to postulate/elim/red
  let dataNatDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
proc two : Nat = suc (suc zero)
proc add (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) m (lam (p : Nat). lam (ih : Nat). suc ih) n
proc four : Nat = add two two
""")
  assert dataNatDefs.len == 3
  let dataTwoTm = dataNatDefs[0].tmTm
  let dataSucId = dataTwoTm.fn.refId
  let dataZeroId = dataTwoTm.arg.arg.refId
  proc dataSucDepth(v: Value): int =
    if v.whnfKind == wRef and v.whnfRefId == dataSucId and v.whnfSpineLen == 1:
      1 + dataSucDepth(v.whnfSpineArg(0))
    elif v.whnfKind == wRef and v.whnfRefId == dataZeroId and v.whnfSpineLen == 0:
      0
    else: -1000
  assert dataSucDepth(eval(dataNatDefs[2].tmTm, @[])) == 4
  echo "ok: data Nat desugars; eliminator computes (add two two = 4)"

  # data Vec: indexed family; the eliminator computes over indices
  let dataVecDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc v2 : Vec Nat (suc (suc zero)) =
  cons Nat (suc zero) (suc zero) (cons Nat zero zero (nil Nat))
proc lenIsTwo : Nat =
  vecElim Nat (lam (i : Nat). lam (v : Vec Nat i). Nat)
            zero
            (lam (i : Nat). lam (x : Nat). lam (xs : Vec Nat i). lam (ih : Nat). suc ih)
            (suc (suc zero)) v2
""")
  assert dataVecDefs.len == 2
  assert dataSucDepth(eval(dataVecDefs[1].tmTm, @[])) == 2
  echo "ok: data Vec (indexed) desugars; eliminator computes (length = 2)"

  # --- Issue #113: higher-order constructor arguments -----------------------
  # A strictly-positive higher-order argument (k : A -> Session) gets an
  # induction hypothesis under binders: ih : Pi (x:A). C (k x), and the
  # computation rule pushes the recursive call under the binders.
  let hoDefs = elabCheck("""
data HNat : ? where
| hzero : HNat
| hsuc (n : HNat) : HNat
data HTree : ? where
| hleaf : HTree
| hnode (k : HNat -> HTree) : HTree
proc hdepth (t : HTree) : HNat =
  hTreeElim (lam (u : HTree). HNat)
    hzero
    (lam (k : HNat -> HTree). lam (ih : Pi (x : HNat). HNat). hsuc (ih hzero))
    t
proc sampleTree : HTree =
  hnode (lam (x : HNat). hnode (lam (y : HNat). hleaf))
proc sampleDepth : HNat = hdepth sampleTree
proc hone : HNat = hsuc hzero
proc htwo : HNat = hsuc (hsuc hzero)
""")
  assert hoDefs.len == 5
  let hsucId = hoDefs[4].tmTm.fn.refId
  let hzeroId = hoDefs[4].tmTm.arg.arg.refId
  proc hoDepth(v: Value): int =
    if v.whnfKind == wRef and v.whnfRefId == hsucId and v.whnfSpineLen == 1:
      1 + hoDepth(v.whnfSpineArg(0))
    elif v.whnfKind == wRef and v.whnfRefId == hzeroId and v.whnfSpineLen == 0:
      0
    else: -1000
  assert hoDepth(eval(hoDefs[2].tmTm, @[])) == 2,
    "hdepth should reduce to hsuc (hsuc hzero)"
  echo "ok: higher-order constructor argument elaborates; eliminator " &
    "computes under binders (#113)"

  # Genuinely non-positive argument: family in a domain position.
  expectElabErr("""
data HNat113 : ? where
| hzero113 : HNat113
data Bad : ? where
| bad (k : (Bad -> HNat113) -> Bad) : Bad
""", "not strictly positive")
  # Nested occurrence: family under another type former, not a direct
  # application to indices.
  expectElabErr("""
data Box113 (A : ?) : ? where
| box113 (x : A) : Box113 A
data Nest : ? where
| nnil : Nest
| ncons (b : Box113 Nest) : Nest
""", "direct application to indices")
  echo "ok: positivity violations rejected with accurate messages (#113)"

  # --- Experiment 5b: conversion in checkTm -------------------------
  # The inferred-vs-expected check now compares up to reduction: `add`
  # (recursing on its first argument here) fires in types, so
  # `Vec A (add zero n)` is accepted where `Vec A n` is expected.
  # Before this change, syntactic unification rejected it — the
  # documented gap in Experiment 5's decision-log entry.
  let convDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc add (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) n (lam (p : Nat). lam (ih : Nat). suc ih) m
proc vnil : Vec Nat (add zero zero) =
  nil Nat
proc constNil (A : ?) (x : A) : Vec A (add zero zero) =
  nil A
proc append {A : ?} {m : Nat} {n : Nat} (xs : Vec A m) (ys : Vec A n)
    : Vec A (add m n) =
  vecElim A (lam (i : Nat). lam (v : Vec A i). Vec A (add i n))
            ys
            (lam (i : Nat). lam (x : A). lam (xs : Vec A i).
              lam (ih : Vec A (add i n)). cons A (add i n) x ih)
            m xs
""")
  assert convDefs.len == 4
  echo "ok: checkTm converts up to reduction (vnil, constNil, Vec append)"
  # ...but genuinely different indices are still rejected
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc add (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) n (lam (p : Nat). lam (ih : Nat). suc ih) m
proc bad : Vec Nat (add (suc zero) zero) =
  nil Nat
""", "not convertible")

  # data errors: constructor return must be the family
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Bad : ? where
| mk : Nat
""", "must be the family")

  # --- Experiment 12: propositional equality -------------------------
  # Eq as an indexed family; refl, J (eqElim), cong, plusReducesZ.
  # refl typechecks up to conversion (Experiment 5b), not just
  # syntactic equality.
  let eqDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
proc two : Nat = suc (suc zero)
proc add (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) n (lam (p : Nat). lam (ih : Nat). suc ih) m
proc four : Nat = suc (suc (suc (suc zero)))
proc r1 : Eq Nat zero zero = refl Nat zero
proc r2 : Eq Nat (add two two) four = refl Nat (add two two)
proc cong (A : ?) (B : ?) (f : A -> B) (x : A) (y : A) (p : Eq A x y)
    : Eq B (f x) (f y) =
  eqElim A x (lam (z : A). lam (q : Eq A x z). Eq B (f x) (f z))
         (refl B (f x)) y p
proc plusReducesZ (n : Nat) : Eq Nat n (add n zero) =
  natElim (lam (m : Nat). Eq Nat m (add m zero))
          (refl Nat zero)
          (lam (k : Nat). lam (ih : Eq Nat k (add k zero)).
            cong Nat Nat (lam (x : Nat). suc x) k (add k zero) ih)
          n
""")
  assert eqDefs.len == 7
  echo "ok: Eq/refl/J/cong/plusReducesZ (Experiment 12)"
  # refl rejects genuinely unequal terms — with a named noConfusion
  # reason (issue #80) instead of the old generic "not convertible".
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
proc bad : Eq Nat zero (suc zero) = refl Nat zero
""", "noConfusion")

  # --- Experiment 11: primitive efficient types ----------------------
  # postulate Int with integer literals and primitive ops (+, -, *)
  # that reduce via host computation (not unary s(s(z))).
  let intDefs = elabCheck("""
postulate Int : ?
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
proc fortyTwo : Int = 42
proc sum : Int = addInt 42 17
proc pf : Eq Int sum 59 = refl Int sum
proc diff : Int = subInt 100 58
proc pf2 : Eq Int diff 42 = refl Int diff
proc prod : Int = mulInt 6 7
proc pf3 : Eq Int prod 42 = refl Int prod
""")
  assert intDefs.len == 7
  echo "ok: primitive Int literals and ops compute (Experiment 11)"
  # data Nat still works for proofs alongside primitive Int
  let bothDefs = elabCheck("""
postulate Int : ?
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
proc n : Nat = suc (suc zero)
proc i : Int = 42
""")
  assert bothDefs.len == 2
  echo "ok: data Nat and primitive Int coexist"

  # --- Experiment 6: tactics and reflection -------------------------
  # `by` blocks run Nim tactics against the expected type.
  let tacDefs = elabCheck("""
postulate Int : ?
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
proc pf1 : Eq Int 42 42 = by refl
proc id (x : Int) : Int = by assumption
proc pf2 : Eq Int (addInt 20 22) 42 = by refl
""")
  assert tacDefs.len == 3
  echo "ok: by refl and by assumption tactics (Experiment 6)"
  # unknown tactic is an error
  expectElabErr("""
postulate Int : ?
proc bad : Int = by nosuchtac
""", "unknown tactic")

  # --- Experiment 9: QTT-lite erasure (basic) ------------------------
  # (0 x : T) marks an erased binder. The flag threads through to the
  # core Term; full usage checking and codegen erasure are future work.
  let erasedDefs = elabCheck("""
proc const (0 A : ?) (x : A) : A = x
proc id2 (0 A : ?) : A -> A = lam (x : A). x
""")
  assert erasedDefs.len == 2
  echo "ok: erased binders (0 x : T) elaborate (Experiment 9)"

  # --- Issue #66: quantity-aware judgments (in-elaboration enforcement) ----
  # Binder quantities are enforced at each lambda during elaboration, with
  # the binder's source location — not just in the #64 post-pass, which
  # reports at the declaration. Type annotations don't count as uses
  # (QTT: types are checked in the all-0 context).
  let qttDefs = elabCheck("""
proc linId (A : ?) : Pi (1 x : A). A =
  lam (1 x : A). x
""")
  assert qttDefs.len == 1
  echo "ok: linear binder used exactly once elaborates (#66)"
  expectElabErr("""
proc linDup (A : ?) (f : A -> A -> A) : Pi (1 x : A). A =
  lam (1 x : A). f x x
""", "used 2 times (expected exactly once)")
  expectElabErr("""
proc linUnused (A : ?) (y : A) : Pi (1 x : A). A =
  lam (1 x : A). y
""", "linear variable 'x' not used")
  expectElabErr("""
proc erasedUse (A : ?) : Pi (0 x : A). A =
  lam (0 x : A). x
""", "erased variable 'x' used")
  # Pi binders are NOT enforced in-judgment (#66 design): a postulate's
  # linear Pi declares use-site linearity; its codomain need not mention it
  let qttPiDefs = elabCheck("""
postulate B : ?
postulate useB : Pi (1 b : B). B
proc useBClient (b : B) : B = useB b
""")
  assert qttPiDefs.len == 1
  echo "ok: linear Pi binders not enforced at declaration (#66)"

  # --- Issue #66: conversion respects binder quantities ----------------
  # (1 x : A) -> B is not convertible with (ω x : A) -> B (or (0 x : A)
  # -> B): the quantity is part of the Pi/Sigma type, checked in
  # structuralEq on wPi/wSi.
  let qttQtyConvOk = elabCheck("""
postulate N : ?
postulate idN0 : Pi (0 x : N). N
proc sameQty : Pi (1 x : N). N = lam (1 x : N). x
proc sameQty0 : Pi (0 x : N). N = idN0
""")
  assert qttQtyConvOk.len == 2
  echo "ok: Pi conversion accepts matching quantities (#66)"
  expectElabErr("""
postulate N : ?
proc idN (x : N) : N = x
proc qtyMismatch : Pi (1 x : N). N = idN
""", "quantity mismatch")
  expectElabErr("""
postulate N : ?
postulate idN0 : Pi (0 x : N). N
proc qtyMismatch0 : Pi (x : N). N = idN0
""", "quantity mismatch")
  echo "ok: Pi conversion rejects mismatched quantities (#66)"

  # --- Issue #66: application-site quantity enforcement ------------------
  # A linear variable must not be passed to an erased (q0) parameter: the
  # 0-binder cannot consume it, so it would be silently discarded. The
  # binder-side check (countVarUses = 1) cannot catch this.
  let qttErasedAppOk = elabCheck("""
postulate N : ?
postulate z0 : Pi (0 x : N). N
proc useErased (y : N) : N = z0 y
""")
  assert qttErasedAppOk.len == 1
  echo "ok: unrestricted var into erased parameter accepted (#66)"
  expectElabErr("""
postulate N : ?
postulate z0 : Pi (0 x : N). N
proc badDrop (1 y : N) : N = z0 y
""", "silently discarded")
  expectElabErr("""
postulate N : ?
proc badDrop2 (1 y : N) (z : N) : N = (lam (0 w : N). z) y
""", "silently discarded")
  echo "ok: linear var into erased parameter rejected (#66)"

  # --- Issue #66: quantity polymorphism ----------------------------------
  # Surface `(q x : A)` binds a quantity variable, solved at the binding
  # lambda from the bound variable's use count: 0 -> q0, 1 -> q1, 2+ ->
  # qOmega. The core language only ever sees concrete quantities.
  let qttQVarDefs = elabCheck("""
postulate N : ?
proc qid {A : ?} (q x : A) : A =
  x
proc qconst {A : ?} {B : ?} (q x : A) (y : B) : A =
  x
proc qdup {A : ?} (q x : A) : Sig (u : A). A =
  (x, x)
proc qunused {A : ?} (q x : A) : 1 =
  <>
""")
  assert qttQVarDefs.len == 4
  echo "ok: quantity variables solve from use count (#66)"
  # One variable shared by two binders must agree on the solution.
  expectElabErr("""
postulate N : ?
proc qconf (q x : N) (q y : N) : Sig (u : N). N =
  (x, (y, y))
""", "requires quantity")
  echo "ok: conflicting quantity-variable solutions rejected (#66)"
  # A variable solved linear after being passed to a q0 parameter is the
  # same leak as a concrete linear variable: the app-site check runs while
  # the variable is unsolved, so the obligation is deferred to solve time.
  expectElabErr("""
postulate N : ?
postulate z0 : Pi (0 x : N). N
proc badQDrop (q y : N) : N = z0 y
""", "silently discarded")
  echo "ok: qty-var solved linear into erased parameter rejected (#66)"
  # But the same shape with 2+ uses solves to qOmega: discarding an
  # unrestricted variable is fine.
  let qttQVarOmegaDrop = elabCheck("""
postulate N : ?
postulate z0 : Pi (0 x : N). N
proc okQDrop (q y : N) : N = snd (z0 y, y)
""")
  assert qttQVarOmegaDrop.len == 1
  echo "ok: qty-var solved unrestricted into erased parameter accepted (#66)"

  # --- Issue #66: subject-side quantity tracking (Gamma |- t :^q A) ------
  # In checking mode the lambda's binder quantity is reconciled with the
  # expected Pi's *before* the body elaborates: a quantity variable is
  # solved from the expected type, an unannotated binder inherits it, and
  # an explicit mismatch is an error.
  let qttSubjDefs = elabCheck("""
postulate N : ?
postulate n0 : N
proc linId : Pi (1 x : N). N = lam (1 x : N). x
proc inheritLin : Pi (1 x : N). N = lam (x : N). x
proc qidLin : Pi (1 x : N). N = lam (q x : N). x
proc inheritErased : Pi (0 x : N). N = lam (x : N). n0
""")
  assert qttSubjDefs.len == 4
  echo "ok: checking-mode quantity reconciliation (#66)"
  # The documented gap: an explicitly linear lambda against an
  # unrestricted Pi is now rejected (was silently accepted).
  expectElabErr("""
postulate N : ?
proc badQtyLam : Pi (x : N). N = lam (1 x : N). x
""", "does not match the expected quantity")
  # An inherited linear binder is still use-once: dropping it is an error.
  expectElabErr("""
postulate N : ?
postulate n0 : N
proc badInheritDrop : Pi (1 x : N). N = lam (x : N). n0
""", "not used")
  expectElabErr("""
postulate N : ?
proc badInheritDup : Pi (1 x : N). Sig (u : N). N = lam (x : N). (x, x)
""", "used 2 times")
  # A quantity variable solved from the expected type is enforced, not
  # re-solved: double use under a linear Pi is an error.
  expectElabErr("""
postulate N : ?
proc qbadLinDup : Pi (1 x : N). Sig (u : N). N = lam (q x : N). (x, x)
""", "used 2 times")
  # An inherited erased binder must not be used in term position.
  expectElabErr("""
postulate N : ?
proc badInheritErased : Pi (0 x : N). N = lam (x : N). x
""", "erased variable 'x' used")
  # A variable shared by two binders must also agree with the expected
  # types it is checked against.
  expectElabErr("""
postulate N : ?
postulate n0 : N
proc qconfTy : N =
  let f : Pi (1 x : N). N = lam (q x : N). x in
  let g : Pi (x : N). N = lam (q x : N). x in
  f (g n0)
""", "requires quantity")
  echo "ok: checking-mode quantity mismatches rejected (#66)"

  # --- Experiment 41: conversion cache as a scoped handler ---------
  # The Experiment 10 cache is no longer a global switch: it is probed
  # only when cacheConvHandler is installed for a dynamic extent.
  # Elaborate a Vec-heavy corpus with and without the handler and check
  # identical results; wall-clock is reported for both.
  let vecCorpus = """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
def vappend : Pi {A : ?}. Pi {m : Nat}. Pi {n : Nat}. Vec A m -> Vec A n
  -> Vec A (add m n)
| nil ys = ys
| (cons k x xs) ys = cons A (add k n) x (vappend xs ys)
proc v1 : Vec Nat (suc (suc zero)) =
  vappend (cons Nat zero zero (nil Nat)) (cons Nat zero zero (nil Nat))
proc v2 : Vec Nat (suc (suc zero)) =
  vappend (cons Nat zero zero (nil Nat)) (cons Nat zero zero (nil Nat))
proc v3 : Vec Nat (suc (suc (suc (suc zero)))) =
  vappend v1 v2
proc v4 : Vec Nat (suc (suc (suc (suc zero)))) =
  vappend v1 v2
"""
  let tCache0 = cpuTime()
  let noCacheDefs = elabCheck(vecCorpus)
  let tCache1 = cpuTime()
  let cacheDefs = elabCheck(vecCorpus, @[cacheConvHandler()])
  let tCache2 = cpuTime()
  assert noCacheDefs.len == cacheDefs.len
  for i in 0 ..< noCacheDefs.len:
    assert noCacheDefs[i].name == cacheDefs[i].name,
      "cache handler changed declaration names"
  # Note: elaborated terms are alpha-equivalent but not string-identical:
  # a cache hit skips NbE, which skips freshPara calls, so later fresh
  # IDs are numbered differently. Accept/reject is identical, which is
  # the criterion that matters.
  echo "ok: cache handler identical results (" & $cacheDefs.len & " decls); " &
    "default=" & formatFloat(tCache1 - tCache0, ffDecimal, 3) & "s " &
    "cache=" & formatFloat(tCache2 - tCache1, ffDecimal, 3) & "s"

  # --- Experiment 41: Nat arithmetic as a scoped decision procedure --
  # `by arith` installs natArithHandler for the dynamic extent of the
  # tactic and the inferred-vs-expected check. It discharges open goals
  # the default conversion cannot: the eliminator is stuck on the
  # neutral first argument, while the handler normalizes linear
  # polynomials.
  let arithDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
proc addSucRight (n : Nat) (m : Nat)
    : Eq Nat (add n (suc m)) (suc (add n m)) =
  by arith
proc addZeroRight (n : Nat) : Eq Nat (add n zero) n =
  by arith
proc addComm (n : Nat) (m : Nat) : Eq Nat (add n m) (add m n) =
  by arith
proc addAssoc (a : Nat) (b : Nat) (c : Nat)
    : Eq Nat (add a (add b c)) (add (add a b) c) =
  by arith
""")
  assert arithDefs.len == 5
  echo "ok: arith handler discharges open Nat goals"
  # The same open goal fails with the default `refl` tactic — the gap is
  # real — and a false goal still fails under `by arith` (no overreach).
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
proc bad (n : Nat) (m : Nat) : Eq Nat (add n (suc m)) (suc (add n m)) =
  by refl
""", "not convertible")
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
proc bad : Eq Nat zero (suc zero) =
  by arith
""", "not convertible")
  echo "ok: arith handler is scoped (default still rejects; false goals rejected)"

  # --- Issue #32: clause-style definitions ---------------------------
  let clauseDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat

data Bool : ? where
| true : Bool
| false : Bool

def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)

def not : Bool -> Bool
| true = false
| false = true

def isEven : Nat -> Bool
| zero = true
| (suc n) = not (isEven n)

proc two : Nat = suc (suc zero)
proc four : Nat = add two two
""")
  assert clauseDefs.len == 5
  echo "ok: clause-style defs (add, not, isEven) elaborate"
  # Verify add computes: add two two = 4
  let fourTm = clauseDefs[4].tmTm
  let fourV = eval(fourTm, @[])
  let twoTm2 = clauseDefs[3].tmTm
  let sucId2 = twoTm2.fn.refId
  proc sucDepth2(v: Value): int =
    if v.whnfKind == wRef and v.whnfRefId == sucId2 and v.whnfSpineLen == 1:
      1 + sucDepth2(v.whnfSpineArg(0))
    elif v.whnfKind == wRef and v.whnfSpineLen == 0:
      0
    else: -1000
  assert sucDepth2(fourV) == 4, "clause-defined add should compute 2+2=4"
  echo "ok: clause-defined add computes (add two two = 4)"
  # Regression: `->` types give every binder the name `_`; the clause
  # compiler must not resolve all of them to the innermost one
  # (add two three was silently computing add three three = 6).
  let add23Defs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
proc two : Nat = suc (suc zero)
proc three : Nat = suc (suc (suc zero))
proc five : Nat = add two three
""")
  let fiveV = eval(add23Defs[3].tmTm, @[])
  let twoTm3 = add23Defs[1].tmTm
  let sucId3 = twoTm3.fn.refId
  proc sucDepth3(v: Value): int =
    if v.whnfKind == wRef and v.whnfRefId == sucId3 and v.whnfSpineLen == 1:
      1 + sucDepth3(v.whnfSpineArg(0))
    elif v.whnfKind == wRef and v.whnfSpineLen == 0:
      0
    else: -1000
  assert sucDepth3(fiveV) == 5, "add two three should be 5"
  echo "ok: clause-defined add distinguishes its arguments (add 2 3 = 5)"

  # Coverage error
  try:
    discard elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def bad : Nat -> Nat
| zero = zero
""")
    assert false, "should have raised coverage error"
  except ElabError as e:
    assert "missing case for constructor 'suc'" in e.msg
    echo "ok: missing coverage is a located error"

  # Overlap error
  try:
    discard elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def bad : Nat -> Nat
| zero = zero
| zero = zero
| (suc n) = n
""")
    assert false, "should have raised overlap error"
  except ElabError as e:
    assert "overlapping clauses" in e.msg
    echo "ok: overlapping clauses are a located error"

  # --- Issue #80: impossible clauses ----------------------------------
  # noConfusionConflictPre unit checks (surface-level rigid conflicts).
  var ctd80 = initTable[string, string]()
  ctd80["zero"] = "Nat"; ctd80["suc"] = "Nat"
  ctd80["nil"] = "Vec"; ctd80["cons"] = "Vec"
  let pz80 = mkVar("zero")
  let psn80 = mkApp(mkVar("suc"), mkVar("n"))
  let pssz80 = mkApp(mkVar("suc"), mkApp(mkVar("suc"), mkVar("zero")))
  let noBound80 = initHashSet[string]()
  let nc1 = noConfusionConflictPre(pz80, psn80, ctd80, noBound80)
  assert nc1.bad and "noConfusion" in nc1.reason, nc1.reason
  assert "'zero' and 'suc'" in nc1.reason, nc1.reason
  assert noConfusionConflictPre(psn80, pz80, ctd80, noBound80).bad  # symmetric
  # injectivity descent: suc (suc zero) vs suc n is fine (n opaque),
  # but suc (suc zero) vs suc zero finds zero-vs-suc under the spine
  assert not noConfusionConflictPre(pssz80, psn80, ctd80, noBound80).bad
  assert noConfusionConflictPre(pssz80,
    mkApp(mkVar("suc"), mkVar("zero")), ctd80, noBound80).bad
  # non-constructor heads and cross-datatype pairs never fire
  assert not noConfusionConflictPre(mkVar("n"), psn80, ctd80, noBound80).bad
  assert not noConfusionConflictPre(mkApp(mkVar("add"), mkVar("n")),
                                   pz80, ctd80, noBound80).bad
  assert not noConfusionConflictPre(pz80, mkVar("nil"), ctd80, noBound80).bad
  # shadowing: a bound variable named like a constructor is not one
  var shadow80 = initHashSet[string]()
  shadow80.incl("suc")
  assert not noConfusionConflictPre(pz80, mkVar("suc"), ctd80, shadow80).bad
  echo "ok: noConfusionConflictPre unit checks"
  # An impossible clause through method checking: the nil branch must
  # produce Vec Nat (suc zero) but `nil Nat : Vec Nat zero` — the
  # downstream unification failure is now a named noConfusion.
  try:
    discard elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
def badHead : Pi {n : Nat}. Vec Nat n -> Vec Nat (suc n)
| nil = nil Nat
| (cons k x xs) = cons Nat (suc (suc k)) x (badHead xs)
""")
    assert false, "should have raised noConfusion error"
  except ElabError as e:
    assert "noConfusion" in e.msg, e.msg
    echo "ok: impossible clause fails with named noConfusion"
  # A unification-time noConfusion: the implicit {m} is still a
  # metavariable when `Vec Nat zero` meets `Vec Nat (suc ?m)`, so the
  # conflict goes through unify's rigid-rigid case with the named reason.
  try:
    discard elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc k {m : Nat} (x : Vec Nat (suc m)) : Nat = zero
proc bad : Nat = k (nil Nat)
""")
    assert false, "should have raised noConfusion error"
  except ElabError as e:
    assert "noConfusion" in e.msg, e.msg
    echo "ok: unify surfaces named noConfusion through elaboration"
  # ...while a solvable implicit still solves (?m := zero).
  let impDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc k {m : Nat} (x : Vec Nat (suc m)) : Nat = zero
proc good : Nat = k (cons Nat zero zero (nil Nat))
""")
  assert impDefs.len == 2
  echo "ok: solvable implicit index still solves"

  # --- Issue #32: indexed patterns ------------------------------------
  # vappend over Vec: the scrutinee's index is refined per constructor
  # (nil: m := zero, cons: m := suc k); the motive abstracts over the index.
  let vappendDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
def vappend : Pi {A : ?}. Pi {m : Nat}. Pi {n : Nat}. Vec A m -> Vec A n
  -> Vec A (add m n)
| nil ys = ys
| (cons k x xs) ys = cons A (add k n) x (vappend xs ys)
proc v123 : Vec Nat (suc (suc (suc zero))) =
  vappend (cons Nat zero zero (nil Nat))
          (cons Nat (suc zero) (suc zero) (cons Nat zero zero (nil Nat)))
""")
  assert vappendDefs.len == 3
  echo "ok: indexed clause defs (vappend) elaborate"
  # vappend [0] [1,0] : Vec Nat 3 — must compute to [0,1,0].
  # cons spine: [A, n, x, xs]; nil spine: [A].
  let v123V = eval(vappendDefs[2].tmTm, @[])
  proc vecElems(v: Value): seq[int] =
    if v.whnfKind == wRef and v.whnfSpineLen == 4:
      let x = v.whnfSpineArg(2)
      var d = 0
      var xv = x
      while xv.whnfKind == wRef and xv.whnfSpineLen == 1:
        inc d
        xv = xv.whnfSpineArg(0)
      assert xv.whnfKind == wRef and xv.whnfSpineLen == 0, "vec elem not a Nat lit"
      @[d] & vecElems(v.whnfSpineArg(3))
    elif v.whnfKind == wRef and v.whnfSpineLen == 1:
      @[]
    else:
      assert false, "vappend result not a Vec value"
      @[]
  assert vecElems(v123V) == @[0, 1, 0], "vappend [0] [1,0] should be [0,1,0]"
  echo "ok: clause-defined vappend computes ([0] ++ [1,0] = [0,1,0])"
  # Index refinement is real: a RHS with the wrong index is rejected
  # (here over Vec Nat so the element typechecks and only the index is wrong)
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
def badAppend : Pi {m : Nat}. Pi {n : Nat}. Vec Nat m -> Vec Nat n
  -> Vec Nat (add m n)
| nil ys = cons Nat n zero ys
| (cons k x xs) ys = cons Nat (add k n) x (badAppend xs ys)
""", "not convertible")
  # Pattern variable shadowing a telescope binder is a located error
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
def badShadow : Pi {A : ?}. Pi {m : Nat}. Pi {n : Nat}. Vec A m -> Vec A n -> Vec A n
| nil ys = ys
| (cons n x xs) ys = ys
""", "shadows argument")

  # --- Issue #36: termination checking (structural recursion) --------
  # Corpus: terminating definitions accepted, non-terminating rejected.
  var termAccepted = 0
  var termRejected = 0
  template acc36(name, src: string) =
    try:
      discard elabCheck(src)
      inc termAccepted
    except ElabError as e:
      assert false, "termination corpus: " & name & " should be accepted: " & e.msg
  template rej36(name, src: string) =
    try:
      discard elabCheck(src)
      assert false, "termination corpus: " & name & " should be rejected"
    except ElabError:
      inc termRejected
  acc36("data Nat", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
""")
  acc36("clause add", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
""")
  acc36("clause double", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def double : Nat -> Nat
| zero = zero
| (suc n) = suc (suc (double n))
""")
  acc36("clause pred", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def pred : Nat -> Nat
| zero = zero
| (suc n) = n
""")
  acc36("clause mult", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
def mult : Nat -> Nat -> Nat
| zero n = zero
| (suc m) n = add n (mult m n)
""")
  acc36("clause isEven", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Bool : ? where
| true : Bool
| false : Bool
def not : Bool -> Bool
| true = false
| false = true
def isEven : Nat -> Bool
| zero = true
| (suc n) = not (isEven n)
""")
  acc36("data Bool", """
data Bool : ? where
| true : Bool
| false : Bool
""")
  acc36("manual structural red", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
elim dblElim : Pi (C : Nat -> ?). C zero -> (Pi (n : Nat). C n -> C (suc n)) -> Pi (n : Nat). C n
red dblElim C z s zero = z
red dblElim C z s (suc n) = s n (dblElim C z s n)
""")
  acc36("clause idNat", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def idNat : Nat -> Nat
| zero = zero
| (suc n) = suc (idNat n)
""")
  acc36("data List", """
data List (A : ?) : ? where
| nil : List A
| cons (x : A) (xs : List A) : List A
""")
  rej36("growing red rule", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
elim bad1 : Pi (C : Nat -> ?). C zero -> (Pi (n : Nat). C n -> C (suc n)) -> Pi (n : Nat). C n
red bad1 C z s (suc n) = bad1 C z s (suc (suc n))
""")
  rej36("self-loop red rule", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
elim bad2 : Pi (C : Nat -> ?). C zero -> (Pi (n : Nat). C n -> C (suc n)) -> Pi (n : Nat). C n
red bad2 C z s (suc n) = bad2 C z s (suc n)
""")
  rej36("base-case loop", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
elim bad3 : Pi (C : Nat -> ?). C zero -> (Pi (n : Nat). C n -> C (suc n)) -> Pi (n : Nat). C n
red bad3 C z s zero = bad3 C z s zero
""")
  rej36("non-subterm var", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
elim bad4 : Pi (C : Nat -> ?). C zero -> (Pi (n : Nat). C n -> C (suc n)) -> Pi (n : Nat). C n
red bad4 C z s (suc n) = bad4 C z s zero
""")
  # Note: bad4's RHS applies bad4 to `zero`, which is not a variable at all,
  # let alone a subterm. The check requires a variable from smallerVars.
  rej36("growing call under step arg", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
elim bad5 : Pi (C : Nat -> ?). C zero -> (Pi (n : Nat). C n -> C (suc n)) -> Pi (n : Nat). C n
red bad5 C z s (suc n) = s n (bad5 C z s (suc (suc n)))
""")
  # bad5 exercises the nested-spine traversal: the recursive call sits
  # inside the step argument and the scrutinee grows, so it is rejected.
  rej36("clause-level growing scrutinee", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def badc : Nat -> Nat
| zero = zero
| (suc n) = badc (suc (suc n))
""")
  # Clause-level: self-call on a constructed value, not a pattern subterm.
  rej36("clause-level self-loop", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def loopc : Nat -> Nat
| zero = zero
| (suc n) = loopc (suc n)
""")
  # Clause-level: self-call on the original scrutinee pattern.
  rej36("clause-level call on unrelated arg", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def badm : Nat -> Nat -> Nat
| zero m = m
| (suc n) m = badm m n
""")
  # Clause-level: recursive call with the scrutinee in a non-scrutinee
  # position (m, not n). Must be rejected, not silently mis-rewritten.
  assert termAccepted >= 10, "need >= 10 accepted, got " & $termAccepted
  assert termRejected >= 5, "need >= 5 rejected, got " & $termRejected
  echo "ok: termination corpus (", termAccepted, " accepted, ",
    termRejected, " rejected)"

  # --- Issue #49: multi-file programs via `import` ---------------------------
  let modDir = getTempDir() / "eponym_import_test"
  createDir(modDir)
  writeFile(modDir / "mynat.ep", """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
proc two : Nat = suc (suc zero)
""")
  writeFile(modDir / "mybool.ep", """
import "mynat.ep"
data Bool : ? where
| true : Bool
| false : Bool
proc twoIsNat : Nat = two
""")
  writeFile(modDir / "client.ep", """
import "mybool.ep"
proc four : Nat = two
proc isTrue (b : Bool) : Bool = b
""")
  writeFile(modDir / "cyc1.ep", "import \"cyc2.ep\"\nproc a : Nat = zero\n")
  writeFile(modDir / "cyc2.ep", "import \"cyc1.ep\"\nproc b : Nat = zero\n")
  writeFile(modDir / "missing.ep", "import \"nope.ep\"\n")

  # Basic: transitive imports, unqualified names in scope.
  var drv = initModuleDriver()
  let clientDefs = drv.elabFile(modDir / "client.ep")
  assert clientDefs.len == 2, "client declares four + isTrue"
  assert "two" in drv.globals and "Bool" in drv.globals and
    "twoIsNat" in drv.globals, "imported names visible unqualified"
  # elabCheckFile convenience entry point.
  let cfDefs = elabCheckFile(modDir / "client.ep")
  assert cfDefs.len == 2

  # Diamond: b and c both import d; d elaborates once.
  writeFile(modDir / "d.ep", "import \"mynat.ep\"\nproc d0 : Nat = zero\n")
  writeFile(modDir / "b.ep", "import \"d.ep\"\nimport \"mynat.ep\"\nproc b0 : Nat = d0\n")
  writeFile(modDir / "c.ep", "import \"d.ep\"\nimport \"mynat.ep\"\nproc c0 : Nat = d0\n")
  writeFile(modDir / "a.ep", "import \"b.ep\"\nimport \"c.ep\"\nproc a0 : Nat = b0\n")
  var drv2 = initModuleDriver()
  discard drv2.elabFile(modDir / "a.ep")
  assert drv2.elabCount[expandFilename(modDir / "d.ep")] == 1,
    "diamond import elaborates d.ep once"

  # Cycle: located error naming the files in the cycle.
  var drv3 = initModuleDriver()
  try:
    discard drv3.elabFile(modDir / "cyc1.ep")
    assert false, "cycle should have raised"
  except ElabError as e:
    assert "import cycle detected" in e.msg, e.msg
    assert "cyc1.ep" in e.msg and "cyc2.ep" in e.msg, e.msg

  # Missing file: located error with the importing chain.
  var drv4 = initModuleDriver()
  try:
    discard drv4.elabFile(modDir / "missing.ep")
    assert false, "missing import should have raised"
  except ElabError as e:
    assert "file not found" in e.msg, e.msg
    assert "nope.ep" in e.msg and "missing.ep" in e.msg, e.msg

  # Content-hash cache: re-elaborating the client on the same driver
  # skips the unchanged library files (elabCount frozen); wall-clock
  # of the second run is small.
  let t1 = cpuTime()
  var drv5 = initModuleDriver()
  discard drv5.elabFile(modDir / "client.ep")
  let tFirst = cpuTime() - t1
  let counts1 = drv5.elabCount
  let t2 = cpuTime()
  discard drv5.elabFile(modDir / "client.ep")
  let tSecond = cpuTime() - t2
  for k, v in counts1:
    assert drv5.elabCount[k] == v, "cache: " & k & " re-elaborated"
  echo "ok: import cache (first ", tFirst.formatFloat(ffDecimal, 3), "s, ",
    "cached ", tSecond.formatFloat(ffDecimal, 3), "s)"

  # elabCheck (string context) rejects import decls with a clear error.
  try:
    discard elabCheck("import \"x.ep\"\nproc p : Nat = zero\n")
    assert false, "string-context import should have raised"
  except ElabError as e:
    assert "elabCheckFile" in e.msg, e.msg

  removeDir(modDir)
  echo "ok: multi-file import (basic, diamond, cycle, missing, cache)"

  echo "--- all elaborator tests passed ---"
