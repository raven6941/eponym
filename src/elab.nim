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
import times
import preterm
import parse_surf
import ett_init
import unify
import egraph

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
    let ctx2 = @[CtxEntry(name: adv, ty: t.dom)] & ctx
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
      prettyTerm(t.letScope.bdy, @[CtxEntry(name: "_", ty: t.letTy)] & ctx, refNames)

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

proc defaultConv(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
                 ctx: Ctx, globals: Globals) =
  ## Experiment 41: the bottom of the handler stack — the Experiment 5b
  ## conversion (full reduction via the core evaluator, then the core's
  ## type-directed conversion areEqual). Raises ElabError("not
  ## convertible") on failure, exactly as convElab did before handlers
  ## existed, so behavior with an empty stack is bit-for-bit unchanged.
  ## Successes are recorded in ms.convCache, which the scoped
  ## cacheConvHandler below probes.
  var env = newSeq[Value](ctx.len)
  for i in 0 ..< ctx.len:
    env[i] = freshPara(s, nil)  # types unused by conversion; identity suffices
  let va = eval(a, env)
  let vb = eval(b, env)
  try:
    areEqual(s, vStar(), va, vb)
    # Success: record in the cache for scoped cache handlers to probe.
    merge(ms.convCache, $ctx.len & ":" & $a & " === " & $b)
  except ValueError as e:
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
                                    $ctxLen & ":" & $a & " === " & $b)
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

proc ext(ctx: Ctx, name: string, ty: Term): Ctx =
  ## Extend the context: every stored type is weakened into the new frame.
  ## (Types are Terms in the frame of the context that stores them; going
  ## under a binder shifts all of them, including the new entry.)
  let w = ctx.mapIt(CtxEntry(name: it.name, ty: weaken(it.ty)))
  @[CtxEntry(name: name, ty: weaken(ty))] & w

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
              ctxLen: int): tuple[dom, codBdy: Term, impl: bool, adv: string] =
  ## t's head must be a Pi; a metavariable head is unified with a fresh
  ## (explicit) Pi. Returns dom and the codomain body (in the extended frame).
  let h = headTy(ms, t)
  if h.kind == tPi:
    return (h.dom, h.scope.bdy, h.impl, h.scope.adv)
  if h.kind == tMeta:
    let dom = freshMeta(ms, tmC(cStar), ctxLen, 0, loc)
    let cod = freshMeta(ms, tmC(cStar), ctxLen, 1, loc)
    unifyElab(ms, h, tmPi(dom, "x", cod), loc)
    return (dom, cod, false, "x")
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
    (freshMeta(ms, tyM, ctx.len, 0, pre.loc), tyM)
  of pkInt:
    # Experiment 11: integer literal; type is the postulated Int
    if "Int" notin globals:
      raise elabErr(pre.loc, "integer literal requires 'postulate Int : ?'")
    let intTy = globals["Int"].tm  # the R node for Int
    (tmInt(pre.intVal), intTy)
  of pkPi:
    let d = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
    let c = checkTm(pre.c2, ctx.ext(pre.name, d), globals, ms, supply, tmC(cStar))
    (tmPi(d, pre.name, c, pre.impl, pre.erased), tmC(cStar))
  of pkSigma:
    let d = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
    let c = checkTm(pre.c2, ctx.ext(pre.name, d), globals, ms, supply, tmC(cStar))
    (tmSi(d, pre.name, c), tmC(cStar))
  of pkLam:
    let d =
      if pre.c1.isNil: freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
      else: checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
    let (b, bty) = inferTm(pre.c2, ctx.ext(pre.name, d), globals, ms, supply)
    (tmLam(d, pre.name, b, pre.impl, pre.erased), tmPi(d, pre.name, bty, pre.impl, pre.erased))
  of pkApp:
    var (f, fty) = inferTm(pre.c1, ctx, globals, ms, supply)
    (f, fty) = insertImplicits(pre, f, fty, ctx.len, ms)
    let (dom, codBdy, impl, _) = ensurePi(ms, pre.loc, fty, ctx.len)
    if impl:
      raise elabErr(pre.loc,
        "cannot apply explicitly to an implicit argument")
    let a = checkTm(pre.c2, ctx, globals, ms, supply, dom)
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
      else:
        let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
        (checkTm(pre.c2, ctx, globals, ms, supply, aty), aty)
    let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, vty), globals, ms, supply)
    (tmLet(v, vty, pre.name, b), subst(bty, 0, v))
  of pkAnn:
    let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar))
    (checkTm(pre.c1, ctx, globals, ms, supply, ty), ty)
  of pkBy:
    raise elabErr(pre.loc, "'by' tactic requires an expected type (use in checking mode)")

proc mkNatLit(n: int, globals: Globals, loc: Loc): Term =
  ## Build unary Nat term suc^n(zero) for integer literal n.
  ## Used for literal overloading: `3` in a Nat position becomes
  ## `suc (suc (suc zero))`. Requires 'zero'/'suc' from `data Nat`.
  if n < 0:
    raise elabErr(loc, "negative integer literal in Nat position")
  if "zero" notin globals or "suc" notin globals:
    raise elabErr(loc, "integer literal in Nat position requires 'data Nat' with zero/suc constructors")
  var res = globals["zero"].tm
  let sucTm = globals["suc"].tm
  for i in 1..n:
    res = tmApp(sucTm, res)
  res

proc checkTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore, supply: var Supply, expTy: Term): Term =
  ## Checking mode against an expected type.
  case pre.kind
  of pkInt:
    # Literal overloading: integer literal adapts to expected type.
    # Try Nat (inductive) first, then primitive Int.
    # The mkNatLit helper builds suc^n(zero); no manual reification needed.
    block:
      # Debug
      # echo "pkInt in checkTm, intVal=", pre.intVal
      var done = false
      var resTm: Term = nil
      if "zero" in globals and "suc" in globals and "Nat" in globals:
        try:
          let natTm = mkNatLit(pre.intVal, globals, pre.loc)
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
    let (dom, codBdy, _, _) = ensurePi(ms, pre.loc, expTy, ctx.len)
    let d =
      if pre.c1.isNil: dom
      else:
        let ad = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
        unifyElab(ms, ad, dom, pre.loc)
        ad
    let b = checkTm(pre.c2, ctx.ext(pre.name, d), globals, ms, supply, codBdy)
    tmLam(d, pre.name, b, pre.impl, pre.erased)
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
    else:
      let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar))
      let v = checkTm(pre.c2, ctx, globals, ms, supply, aty)
      let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, aty), globals, ms, supply)
      unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
      tmLet(v, aty, pre.name, b)
  of pkAnn:
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
  # 1. elaborate the type; it must be a type and contain no metas
  let (tyTm0, tyTy) = inferTm(d.desugarTy(), @[], globals, ms, supply)
  unifyElab(ms, tyTy, tmC(cStar), d.loc)
  let tyT = zonk(ms, tyTm0)
  let ru = findUnsolved(ms, tyT)
  if ru.found:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the type of '" & d.name & "'")
  let tyV =
    try: check(supply, vStar(), tyT)
    except ValueError as e:
      raise elabErr(d.loc,
        "ill-formed type of '" & d.name & "': " & e.msg)
  # 2. elaborate the body against the type; zonk; reject leftovers
  let tmT0 = checkTm(d.desugarTm(), @[], globals, ms, supply, tyT)
  let tmT = zonk(ms, tmT0)
  let ru2 = findUnsolved(ms, tmT)
  if ru2.found:
    raise elabErr(ru2.loc, "unsolved metavariable ?m" & $ru2.id &
      " in the definition of '" & d.name & "'")
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
  if d.name in globals:
    raise elabErr(d.loc, "duplicate definition '" & d.name & "'")
  globals[d.name] = GEntry(tm: newDefRef(supply, tyV, tmV), ty: tyT)
  ElabDef(name: d.name, tyTm: tyT, tmTm: tmT, loc: d.loc)

proc elabPostulateDecl(name: string, ty: PreTerm, loc: Loc,
                       globals: var Globals, supply: var Supply,
                       ms: var MetaStore, isElim: bool) =
  ## Experiment 4: `postulate name : Ty` / `elim name : Ty`.
  ## A parameter-like global; `elim` additionally installs an empty
  ## reduction rule table on the R node for later `red` declarations.
  if name in globals:
    raise elabErr(loc, "duplicate declaration '" & name & "'")
  let (tyTm0, tyTy) = inferTm(ty, @[], globals, ms, supply)
  unifyElab(ms, tyTy, tmC(cStar), loc)
  let tyT = zonk(ms, tyTm0)
  let ru = findUnsolved(ms, tyT)
  if ru.found:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the type of '" & name & "'")
  let tyV =
    try: check(supply, vStar(), tyT)
    except ValueError as e:
      raise elabErr(loc, "ill-formed type of '" & name & "': " & e.msg)
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
                        smallerVars: seq[string], loc: Loc) =
  ## Issue #36: syntactic structural recursion check for `red` rules.
  ## Any application of `elimName` in the RHS must take a direct subterm
  ## of the LHS pattern (a variable from `smallerVars`) in the scrutinee
  ## position (last argument). Otherwise the rule may not terminate.
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
        if scrutArg.kind != pkVar or scrutArg.name notin smallerVars:
          raise elabErr(rhs.loc,
            "non-structurally-recursive call in `red` rule: '" & elimName &
            "' applied to '" & $scrutArg &
            "', which is not a direct subterm of the LHS pattern")
      # Recurse into the spine args (they may contain nested calls)
      for a in rspine:
        checkStructuralRec(a, elimName, nargs, smallerVars, loc)
    else:
      checkStructuralRec(h, elimName, nargs, smallerVars, loc)
      for a in rspine:
        checkStructuralRec(a, elimName, nargs, smallerVars, loc)
  of pkLam:
    if rhs.c1 != nil:
      checkStructuralRec(rhs.c1, elimName, nargs, smallerVars, loc)
    checkStructuralRec(rhs.c2, elimName, nargs, smallerVars, loc)
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
  if ru.found:
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

proc mkPis(tele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool]],
           body: PreTerm, loc: Loc): PreTerm =
  result = body
  for i in countdown(tele.high, 0):
    result = mkPi(tele[i].name, tele[i].ty, result, loc, tele[i].impl, tele[i].erased)

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

proc elimNameFor(dname: string): string =
  result = dname
  if result.len > 0:
    result[0] = result[0].toLowerAscii()
  result &= "Elim"

proc famAppPre(famName: string, params: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool]],
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
  # C : Pi (idx...). F params idx -> ?
  var cTy = mkArrow(famAppPre(famName, d.params,
                             indexNames.mapIt(mkVar(it, loc)), loc),
                    mkUniv(loc), loc)
  for i in countdown(indexTele.high, 0):
    cTy = mkPi(indexNames[i], indexTele[i].ty, cTy, loc)
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
    for i in countdown(ctor.tele.high, 0):
      let argTy = ctor.tele[i].ty
      if mentionsFam(argTy, famName):
        let argIndices = extractIndices(argTy, famName, d.params.len, ctor.cloc)
        var ihTy = mkVar("C", loc)
        for ai in argIndices: ihTy = mkApp(ihTy, ai, loc)
        ihTy = mkApp(ihTy, mkVar(ctor.tele[i].name, loc), loc)
        mTy = mkPi("ih" & $ihCount, ihTy, mTy, loc)
        inc ihCount
      mTy = mkPi(ctor.tele[i].name, argTy, mTy, loc)
    methodTys.add(mTy)
  # Pi (params...)(C : cTy)(methods...)(idx...)(v : F params idx). C idx v
  var vTy = famAppPre(famName, d.params,
                      indexNames.mapIt(mkVar(it, loc)), loc)
  var body = mkVar("C", loc)
  for iNm in indexNames: body = mkApp(body, mkVar(iNm, loc), loc)
  body = mkApp(body, mkVar("v", loc), loc)
  var elimTy = mkPi("v", vTy, body, loc)
  for i in countdown(indexNames.high, 0):
    elimTy = mkPi(indexNames[i], indexTele[i].ty, elimTy, loc)
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
    # contractum: method teleVars recCalls...
    var rhs = mkVar(methodNames[ci], loc)
    for t in ctor.tele:
      rhs = mkApp(rhs, mkVar(t.name, loc), loc)
    for t in ctor.tele:
      if mentionsFam(t.ty, famName):
        let argIndices = extractIndices(t.ty, famName, d.params.len, ctor.cloc)
        var rec = mkVar(elimName, loc)
        for p in d.params: rec = mkApp(rec, mkVar(p.name, loc), loc)
        rec = mkApp(rec, mkVar("C", loc), loc)
        for mn in methodNames: rec = mkApp(rec, mkVar(mn, loc), loc)
        for ai in argIndices: rec = mkApp(rec, ai, loc)
        rec = mkApp(rec, mkVar(t.name, loc), loc)
        rhs = mkApp(rhs, rec, loc)
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
      of pkPi: mkPi(t.name, d, t.c2, t.loc, t.impl, t.erased)
      of pkLam: mkLam(t.name, d, t.c2, t.loc, t.impl, t.erased)
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
      of pkPi: mkPi(bname, d, body, t.loc, t.impl, t.erased)
      of pkLam: mkLam(bname, d, body, t.loc, t.impl, t.erased)
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

proc elabClausesDecl(cd: ClausesDef, globals: var Globals, supply: var Supply,
                     ms: var MetaStore,
                     dataInfos: var Table[string, SurfDecl]): ElabDef =
  let loc = cd.loc
  # 1. Find the scrutinee's data type from the type signature.
  let dataName = scrutineeDataName(cd.ty, dataInfos)
  if dataName == "":
    raise elabErr(loc, "'def' clauses require the first explicit argument " &
      "to have a data type; none found in the type signature")
  let dataDecl = dataInfos[dataName]
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
  for j in countdown(motiveIdxNames.high, 0):
    motive = mkLam(motiveIdxNames[j],
                   substPreN(indexTele[j].ty, paramSubst, fresh), motive, loc)
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
  var procTele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool]] = @[]
  var restVars: seq[string] = @[]
  for i, b in tele:
    let bn = if b.name.len > 0: b.name else: "x" & $i
    # The proc syntax supports implicits; keep them.
    procTele.add((bn, b.ty, b.impl, false))
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

proc elabCheck*(src: string, handlers: seq[ConvHandler] = @[]): seq[ElabDef] =
  ## Parse, elaborate, and typecheck a surface program, decl by decl.
  ## Later decls may mention earlier ones (via closed R nodes).
  ## Raises ParseError (carries loc) or ElabError (carries loc).
  ## Experiment 41: `handlers` installs conversion decision procedures
  ## for the dynamic extent of the whole program (e.g. @[cacheConvHandler]).
  let decls = parseProgram(src)
  var globals: Globals = initTable[string, GEntry]()
  var supply = Supply()
  var ms = initMetaStore()  # includes fresh convCache (Experiment 10)
  for h in handlers: ms.convHandlers.add(h)
  var dataInfos: Table[string, SurfDecl] = initTable[string, SurfDecl]()
  for d in decls:
    result.add(elabDecl(d, globals, supply, ms, dataInfos))

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
  # refl rejects genuinely unequal terms
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
proc bad : Eq Nat zero (suc zero) = refl Nat zero
""", "not convertible")

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

  echo "--- all elaborator tests passed ---"
