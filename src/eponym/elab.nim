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
import abilities   # Issue #177: ambient abilities (Frank-style)
import eponym_init
import unify
import egraph
import usage_check  # Issue #64: linear usage verification
import mutual_termination  # Issue #42: mutual-block call-graph termination check
import elab_prof      # Issue #55: phase timers (zero-cost when -d:elabProfile off)
import elab_trace     # Issue #83: structured elaboration trace (runtime flag)

type
  ElabError* = object of CatchableError
    loc*: Loc

proc elabErr(loc: Loc, msg: string): ref ElabError =
  let e = newException(ElabError,
    "line " & $loc.line & ", col " & $loc.col & ": " & msg)
  e.loc = loc
  e

proc unsolvedMetaHint(): string =
  ## Issue #186: actionable hint appended to every unsolved-metavariable
  ## error. The hole's site is reported by the caller; the hint tells the
  ## user what to do about it.
  "; nothing in the program determines this hole's value — " &
    "add a type annotation or fill in the hole explicitly"

proc sanitizeKernelMsg*(msg: string): string =
  ## Issue #34: the kernel evaluator's conversion errors embed raw
  ## `$`-rendered terms (R123 refIds, `:$` application syntax, de Bruijn
  ## V-indices) that leak elaborator internals to users. The elaborator
  ## already reports the name-aware pretty-printed types alongside these
  ## messages, so drop the raw dump and keep the failure kind. Apply at
  ## every site where a kernel ValueError message reaches a user-facing
  ## ElabError.
  if msg.startsWith("neutral mismatch: "): "neutral mismatch"
  elif msg.startsWith("mismatch: "): "mismatch"
  else: msg

proc unifyElab(ms: var MetaStore, a, b: Term, loc: Loc) =
  profilePhase(epUnify):
      ## unify, translating UnifyError into ElabError (adds the source location).
      traceGuard(tcUnify, "unify", trunc($a) & "  ~  " & trunc($b))
      try:
        unify(ms, a, b, loc)
      except UnifyError as e:
        traceEvt(tcUnify, "unify.fail", e.msg)
        raise elabErr(loc, e.msg)

proc flushDeferredElab(ms: var MetaStore, loc: Loc) =
  ## Issue #56: declaration-final pre-unification pass. Suspended goals
  ## are retried once more; leftovers become an ambiguity error showing
  ## the stuck constraint. Hole-tolerant tooling mode leaves them
  ## pending (flushDeferred checks allowHoles itself).
  try:
    flushDeferred(ms, loc)
  except UnifyError as e:
    traceEvt(tcUnify, "unify.flush-fail", e.msg)
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
    peg*: Ability                # Issue #177: the signature's peg ([?aN]
                                 # freshened per signature, generalized;
                                 # nil for interface markers)
    cmdIface*: string            # Issue #177: interface name if a command
    isIface*: bool               # Issue #177: `interface` declaration marker
  Globals* = Table[string, GEntry]

# Forward declaration for use in tactics. Returns the validated evidence
# Term when an evidence-returning handler (issue #45) discharged the goal,
# nil otherwise.
proc convElab(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
              ctx: Ctx, globals: Globals, goalTy: Term = nil,
              expLoc: Loc = noLoc): Term

# --- Issue #177: ambient abilities (Frank-style) ---------------------------
#
# The ambient ability is threaded through checkTm/inferTm as `ab`
# (nil = [] = pure). Every operator (tPi) the elaborator builds is stamped
# with the ambient at its construction site — Frank's "the peg is a
# checking-mode input". Signatures freshen one implicit effect variable
# ?aN per signature (omitted brackets mean [?aN]); `[]` is closed/pure.
#
# Design note: the discipline is a pure *predicate* (pegCompatible).
# Ability variables are never solved during elaboration — an earlier
# revision freshened ?aN per use and instantiated the copy to the ambient
# (Frank-literal), but measurement showed ~1.2x pure-code overhead for an
# instantiation no elaborator rule ever observed (pegs gate checks; they
# never flow into terms). The Command rule is a membership test of the
# command's interface in the ambient.

type AbMember* = enum amYes, amNo, amStuck

proc abMemberAb(iface: string, ab: Ability): AbMember =
  ## Frank's Command rule premise: is `iface` in the ambient ability?
  ## amStuck when the ambient ends in an ability variable — terminal,
  ## since ability variables are never solved (cf. Klister's resumable
  ## stuck tasks: there is nothing here to resume on).
  if ab.isNil: return amNo
  if iface in ab.ifaces: return amYes
  if ab.tailOpen: return amStuck
  amNo

proc checkPeg(opPeg, ambient: Ability, loc: Loc) =
  ## Frank's App rule as a predicate: the operator's peg must be
  ## compatible with the ambient (pegCompatible). Never mutates.
  if opPeg == ambient: return  # same object: all Pis built under one
                               # ambient share its Ability (common case)
  if not pegCompatible(opPeg, ambient):
    raise elabErr(loc, "ability mismatch: operator requires peg " & $opPeg &
      " but the ambient ability is " & $ambient)

proc setPeg(t: Term, peg: Ability): Term =
  ## Re-stamp the peg of a tPi (the Command rule pegs the operator type
  ## at the ambient ability).
  assert t.kind == tPi
  tmPi(t.dom, t.scope.adv, t.scope.bdy, t.impl, t.erased, t.qty, peg)

proc sigAmbient(d: SurfDef, globals: Globals, ms: var MetaStore): Ability =
  ## Issue #177: the ambient ability for elaborating a `proc` signature
  ## and body: the annotated peg, or a fresh ?aN (Frank's implicit effect
  ## polymorphism: omitted brackets mean [ε]).
  if d.hasPeg:
    for n in d.pegNames:
      if n notin globals or not globals[n].isIface:
        raise elabErr(d.loc, "unknown interface '" & n & "' in peg")
    return abClosed(d.pegNames)
  freshAbMeta(ms)

# --- Basic tactics (Experiment 6) ------------------------------------

# Forward declaration (issue #186): defined below; used by tactic-failure
# messages to render the goal the tactic was run against.
proc prettyTerm*(t: Term, ctx: Ctx, refNames: Table[int, string],
                records: Table[string, seq[string]] =
                  initTable[string, seq[string]]()): string

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
  # Issue #186: name the goal so the user can compare it against the
  # hypotheses actually in scope.
  var refNames = initTable[int, string]()
  for name, g in globals:
    if g.tm.kind == tR: refNames[g.tm.refId] = name
  raise elabErr(loc, "assumption: no hypothesis matches the goal " &
    prettyTerm(goal, ctx, refNames))

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
    var refNames = initTable[int, string]()
    for name, g in globals:
      if g.tm.kind == tR: refNames[g.tm.refId] = name
    raise elabErr(loc, "refl: goal is not an equality (got " &
      prettyTerm(goal, ctx, refNames) & ")")
  let eqHead = spine[3]
  let aTy = spine[2]
  let x = spine[1]
  let y = spine[0]
  # Check head is Eq (a tR node)
  if eqHead.kind != tR:
    raise elabErr(loc, "refl: goal head is not Eq")
  # Check x and y are convertible via full conversion (Experiment 5b)
  let ev =
    try:
      convElab(ms, supply, x, y, loc, ctx, globals, aTy)
    except ElabError as e:
      raise elabErr(loc, "refl: sides are not convertible: " & e.msg)
  if not ev.isNil:
    # Issue #45: an evidence-returning handler discharged the goal — splice
    # its bare-core-validated proof as the tactic's result. The old `refl`
    # below would not survive elabDefDecl's bare-core re-check for
    # non-definitional goals (that is exactly what the evidence is for).
    return ev
  # Build refl A x : Eq A x x
  if "refl" notin globals:
    raise elabErr(loc, "refl: 'refl' not in scope")
  let reflTm = globals["refl"].tm
  tmApp(tmApp(reflTm, aTy), x)

# (initTactics removed: built-ins are dispatched directly in pkBy case)

proc recordSkeletonName(t: Term, records: Table[string, seq[string]]): string =
  ## Issue #37, step 4: if `t` is an iterated Sigma whose binder names end
  ## in the unit type and match a registered record declaration's field
  ## list, return the record name; else "". Lets the pretty-printer render
  ## record types with field names instead of raw `Si` nesting. (Records
  ## are transparent iterated Sigmas by design, so only the skeleton —
  ## binder names plus the `1` tail — identifies them. Two records sharing
  ## an identical field-name list are pathological; the first registered
  ## wins.)
  if t.isNil or t.kind != tSi or records.len == 0: return ""
  var names: seq[string] = @[]
  var cur = t
  while not cur.isNil and cur.kind == tSi:
    names.add(cur.scope.adv)
    cur = cur.scope.bdy
  if cur.isNil or cur.kind != tC or cur.c != cOne: return ""
  for rname, fields in records:
    if fields == names: return rname
  ""

proc prettyTerm*(t: Term, ctx: Ctx, refNames: Table[int, string],
                records: Table[string, seq[string]] =
                  initTable[string, seq[string]]()): string =
  ## User-facing pretty-printer: uses names from the context and globals
  ## instead of internal IDs (R1, V6, ?m3). `records` maps record names to
  ## field names (MetaStore.recordFields); an iterated Sigma matching a
  ## record skeleton prints as `R{f: T, ...}` rather than raw `Si`.
  if t == nil: return "<nil>"
  case t.kind
  of tR:
    if t.refId in refNames: refNames[t.refId] else: "R" & $t.refId
  of tV:
    if t.idx < ctx.len and ctx[t.idx].name != "_": ctx[t.idx].name
    else: "V" & $t.idx
  of tC: $t.c
  of tType: "Type " & $t.lvl  # Issue #52
  of tInt: $t.intVal
  of tNatLit: $t.natLitVal
  of tNatSing: $t.natSingVal  # Issue #74
  of tPrim: $t.primOp
  of tSi:
    # Issue #37, step 4: a Sigma matching a registered record skeleton
    # prints with field names (`Point{x: Nat, y: Nat}`), never as raw `Si`.
    let rname = recordSkeletonName(t, records)
    if rname != "":
      var parts: seq[string] = @[]
      var cur = t
      var ctx2 = ctx
      while cur.kind == tSi:
        let adv = if cur.scope.adv != "_": cur.scope.adv else: "_"
        parts.add(adv & ": " &
          prettyTerm(cur.dom, ctx2, refNames, records))
        ctx2 = @[CtxEntry(name: adv, ty: cur.dom, qty: cur.qty)] & ctx2
        cur = cur.scope.bdy
      rname & "{" & parts.join(", ") & "}"
    else:
      let adv = if t.scope.adv != "_": t.scope.adv else: "_"
      let kindStr =
        if t.erased: "Si(0 "
        elif t.impl: "Si{"
        else: "Si("
      let ctx2 = @[CtxEntry(name: adv, ty: t.dom, qty: t.qty)] & ctx
      kindStr & prettyTerm(t.dom, ctx, refNames, records) & ", " & adv & ". " &
        prettyTerm(t.scope.bdy, ctx2, refNames, records) & ")"
  of tPi, tLam:
    let adv = if t.scope.adv != "_": t.scope.adv else: "_"
    let kindStr =
      if t.kind == tPi:
        if t.erased: "Pi(0 "
        elif t.impl: "Pi{"
        else: "Pi("
      else:
        if t.erased: "L(0 "
        elif t.impl: "L{"
        else: "L("
    let ctx2 = @[CtxEntry(name: adv, ty: t.dom, qty: t.qty)] & ctx
    kindStr & prettyTerm(t.dom, ctx, refNames, records) & ", " & adv & ". " &
      prettyTerm(t.scope.bdy, ctx2, refNames, records) & ")"
  of tMeta: "?_"
  of tPair:
    "P(" & prettyTerm(t.pFst, ctx, refNames, records) & ", " &
      prettyTerm(t.pSnd, ctx, refNames, records) & ")"
  of tApp:
    # Issue #186: flatten application spines so types read like the surface
    # syntax (`(Vec Nat (suc zero))`) instead of nested binary applications
    # (`(((Vec Nat) (suc zero)))`). A lone tApp still parenthesizes once.
    var args: seq[Term] = @[]
    var head = t
    while head.kind == tApp:
      args.add(head.arg)
      head = head.fn
    var parts: seq[string] = @[prettyTerm(head, ctx, refNames, records)]
    for i in countdown(args.high, 0):
      parts.add(prettyTerm(args[i], ctx, refNames, records))
    "(" & parts.join(" ") & ")"
  of tFst: "(" & prettyTerm(t.sub, ctx, refNames, records) & ".1)"
  of tSnd: "(" & prettyTerm(t.sub, ctx, refNames, records) & ".2)"
  of tAbsurd: "(absurd " & prettyTerm(t.sub, ctx, refNames, records) & ")"
  of tLet:
    "let " & prettyTerm(t.letVal, ctx, refNames, records) & " in " &
      prettyTerm(t.letScope.bdy, @[CtxEntry(name: "_", ty: t.letTy, qty: qOmega)] & ctx, refNames, records)

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
  of tR, tV, tC, tType, tInt, tPrim, tMeta, tNatSing: false
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
  of tR, tV, tC, tType, tInt, tPrim, tMeta, tNatSing: t
  of tPi, tSi, tLam:
    mkBinder(t.kind, expandNatLit(t.dom, zeroTm, sucTm),
             Scope(adv: t.scope.adv,
                   bdy: expandNatLit(t.scope.bdy, zeroTm, sucTm)),
             t.impl, t.qty, t.peg)
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

proc expLocSuffix(expLoc: Loc): string =
  ## Issue #46: when the call site knows where the expected type was
  ## written, name that program point in the conversion-failure message,
  ## so the error carries two source locations (the inferred term's site
  ## is the ElabError's own loc). noLoc = unknown: suffix omitted and
  ## the message is byte-identical to before.
  if expLoc == noLoc: ""
  else: " (expected type written at line " & $expLoc.line &
    ", col " & $expLoc.col & ")"

proc defaultConv(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
                 ctx: Ctx, globals: Globals, expLoc: Loc = noLoc) =
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
    let reason = noConfusionMsg(ms, nc.c1, nc.c2)
    traceEvt(tcConv, "conv.noconfusion", reason)  # Issue #83: the fast-fail point
    raise elabErr(loc, "inferred type " & prettyTerm(a, ctx, refNames, ms.recordFields) &
      " does not match expected type " & prettyTerm(b, ctx, refNames, ms.recordFields) &
      expLocSuffix(expLoc) & ": " & reason)
  var env = newSeq[Value](ctx.len)
  for i in 0 ..< ctx.len:
    env[i] = freshPara(s, nil)  # types unused by conversion; identity suffices
  let va = eval(a, env)
  let vb = eval(b, env)
  # Issue #74/#223: singleton subsumption — the elaborator's only
  # subtyping, and it is directional (inferred <: expected), so it lives
  # here, not in the kernel's symmetric conversion. tNatSing(k) widens
  # to Nat, covariant through Pi codomains and Sigma components
  # (mirroring the singleton part of `subsumes`), and is equal only to
  # tNatSing(k). When no singleton rule fires, fall through to the
  # areEqual below, which fails with the standard "not convertible"
  # message.
  let natVal = if "Nat" in globals: eval(globals["Nat"].tm, env)
               else: nil
  if subsumeSing(s, va, vb, natVal):
    merge(ms.convCache, convKey(ctx.len, a, b))
    return
  try:
    # Issue #84: the inferred-vs-expected check uses the directional q0
    # ≤ ω subsumption (an inferred-erased binder is usable where an
    # unrestricted one is expected), so inferred-precise types
    # interoperate with ω-annotated code. The def-declaration re-check
    # (elabDefDecl step 3) passes the same flag — it audits this check,
    # so it must implement the same relation.
    areEqual(s, vStar(), va, vb, qtySubsumption = true)
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
        areEqual(s, vStar(), eval(a2, env), eval(b2, env),
                 qtySubsumption = true)
        merge(ms.convCache, convKey(ctx.len, a2, b2))
        return
      except ValueError:
        discard
    var refNames = initTable[int, string]()
    for name, g in globals:
      if g.tm.kind == tR: refNames[g.tm.refId] = name
    traceEvt(tcConv, "conv.fail", sanitizeKernelMsg(e.msg))  # Issue #83
    raise elabErr(loc, "inferred type " & prettyTerm(a, ctx, refNames, ms.recordFields) &
      " does not match expected type " & prettyTerm(b, ctx, refNames, ms.recordFields) &
      expLocSuffix(expLoc) & ": not convertible (" & sanitizeKernelMsg(e.msg) & ")")

proc closeParams*(s: var Supply, ctx: Ctx): seq[Term] =
  ## Issue #45: the fresh rigid postulate refs closing a context. The goal
  ## and the evidence must be closed over the *same* refs — closing them
  ## with two independent sets makes the core's check fail with a neutral
  ## mismatch between the two sets — so this is computed once and shared
  ## (see validateEvidence).
  result = newSeq[Term](ctx.len)
  var i = ctx.len - 1
  while i >= 0:
    var ty = ctx[i].ty
    var j = ctx.len - 1
    while j > i:
      ty = subst(ty, j, result[j])
      dec j
    result[i] = newPostulateRef(s, eval(ty, @[]))
    dec i

proc closeOverCtx*(t: Term, ctx: Ctx, params: seq[Term]): Term =
  ## Issue #45: replace every free `tV(i)` (i < ctx.len) by the
  ## corresponding rigid ref from `params` (computed once by closeParams
  ## and shared between the goal and the evidence being validated).
  ## Descending substitution: replacing V_j for j from high to low never
  ## disturbs the not-yet-replaced lower indices.
  result = t
  var i = ctx.len - 1
  while i >= 0:
    result = subst(result, i, params[i])
    dec i

proc univLevelOfTy(s: var Supply, ms: var MetaStore, t: Term, ctx: Ctx): int =
  ## Issue #52: the universe level classifying the elaborated type-term `t`
  ## (a term whose type is definitionally a universe). Closes `t` over the
  ## context with fresh rigid refs and asks the core for its type —
  ## mirroring the core's own Pi/Sigma formation rule
  ## (`max(univIdx(infer dom), univIdx(infer cod))`). Legacy `?`-classified
  ## types stay at level 0, as do terms the core cannot classify (an
  ## unsolved hole under allowHoles, or a non-universe): the elaborator
  ## never invents levels.
  try:
    # Issue #84: `t` is elaborator output; classify with the same
    # conversion relation the elaborator used (directional q0 ≤ ω), so a
    # nested inferred-q0/expected-qOmega application does not spuriously
    # fall back to level 0.
    univIdx(infer(s, closeOverCtx(zonk(ms, t), ctx, closeParams(s, ctx)),
                 qtySubsumption = true))
  except ValueError:
    0

proc ensureIsUniverse(ms: var MetaStore, s: var Supply, tyTy: Term, loc: Loc,
                      what: string) =
  ## Issue #52: the classifier of an ascribed type must be a universe —
  ## `?` or any `Type l`. (The old `unifyElab(tyTy, ?)` only admitted
  ## level 0, so `Type l` — whose classifier is `Type (l+1)` — would be
  ## wrongly rejected.) A classifier with unsolved metas keeps the legacy
  ## unify path: a hole there is solved to `?` exactly as before.
  let tyTyZ = zonk(ms, tyTy)
  if findUnsolved(ms, tyTyZ).found:
    unifyElab(ms, tyTyZ, tmC(cStar), loc)
    return
  let v =
    try: eval(tyTyZ, @[])
    except ValueError as e:
      raise elabErr(loc, what & " is not a type (" & sanitizeKernelMsg(e.msg) & ")")
  if v.whnf.kind == wType or (v.whnf.kind == wConst and v.whnf.c == cStar):
    return
  raise elabErr(loc, what & " is not a type")

proc validateEvidence(ms: var MetaStore, s: var Supply, a, b, goalTy,
                      ev: Term, loc: Loc, ctx: Ctx, globals: Globals): Term =
  ## Issue #45: validate a handler's evidence with the bare core.
  ## The handler claims `ev : Eq goalTy a b`. Handlers are popped for the
  ## validation (bare-core conversion only), the goal and evidence are
  ## closed over the context with fresh rigid refs, and the core's own
  ## `check` verifies the claim. Failure raises a located ElabError —
  ## bogus evidence is rejected, never silently trusted.
  ## Returns the zonked (open) evidence for splicing into the elaborated
  ## term (e.g. by tacRefl); the closed copy is check-only.
  if ev.isNil:
    raise elabErr(loc, "conversion handler returned cvDischargedEv with nil evidence")
  if goalTy.isNil:
    raise elabErr(loc, "conversion handler returned evidence but the goal " &
      "type is unknown (internal error: convElab call site did not pass goalTy)")
  if "Eq" notin globals:
    raise elabErr(loc, "conversion handler returned evidence but 'Eq' is not in scope")
  let ev1 = zonk(ms, ev)
  let ru = findUnsolved(ms, ev1)
  if ru.found:
    raise elabErr(loc, "conversion handler evidence mentions unsolved metavariable")
  let eqTm = globals["Eq"].tm
  let goal = tmApp(tmApp(tmApp(eqTm, goalTy), a), b)
  # The goal and the evidence are closed over the *same* fresh rigid refs
  # (closeParams computes the set once); two independent closings would
  # give the evidence's type different refIds than the goal's.
  let params = closeParams(s, ctx)
  let closedGoal = closeOverCtx(goal, ctx, params)
  let closedEv = closeOverCtx(ev1, ctx, params)
  let saved = ms.convHandlers
  ms.convHandlers = @[]
  try:
    discard check(s, eval(closedGoal, @[]), closedEv)
  except ValueError as e:
    raise elabErr(loc, "conversion handler evidence rejected by the core: " &
      sanitizeKernelMsg(e.msg))
  finally:
    ms.convHandlers = saved
  ev1

proc convElab(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
              ctx: Ctx, globals: Globals, goalTy: Term = nil,
              expLoc: Loc = noLoc): Term =
  profilePhase(epConv):
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
      ## Issue #46: `expLoc` is the source location where the expected
      ## type was written, when the call site knows it (noLoc = unknown).
      ## It flows only to defaultConv's failure message; the handler
      ## protocol is unchanged, and unknown origins keep the old message
      ## byte-identical.
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
      if a == b: return nil
      traceEvt(tcConv, "conv.goal", trunc($a) & "  ~  " & trunc($b))
      let a1 = zonk(ms, a)
      let b1 = zonk(ms, b)
      if findUnsolved(ms, a1).found or findUnsolved(ms, b1).found:
        traceEvt(tcConv, "conv.unify", "unsolved metas: unify instead of convert")
        unifyElab(ms, a1, b1, loc)
        return nil
      # Issue #52: cumulativity fast path (subtyping, not equality). A term
      # whose type is `Type i` checks against an expected `Type j` when
      # i <= j; the legacy `?` is the bottom universe on the inferred side
      # and the top sort on the expected side ("is a type" positions admit
      # any universe) — mirroring the core's directional rule in `check`.
      # Handlers never see these goals, exactly as the core's `check`
      # applies cumulativity without consulting them.
      block cumul:
        var env = newSeq[Value](ctx.len)
        for i in 0 ..< ctx.len: env[i] = freshPara(s, nil)
        let va = eval(a1, env)
        let vb = eval(b1, env)
        let aLvl =
          try: univIdx(va)
          except ValueError: -1  # inferred side is not a universe: not ours
        if aLvl < 0: break cumul
        let bIsStar = vb.whnf.kind == wConst and vb.whnf.c == cStar
        if bIsStar:
          # `?` stays the top sort for "is a type" positions: any universe checks.
          traceEvt(tcConv, "conv.cumul", "Type " & $aLvl & " <= ?")
          return nil
        let bLvl =
          try: univIdx(vb)
          except ValueError: -1
        if bLvl >= 0 and aLvl <= bLvl:
          traceEvt(tcConv, "conv.cumul", "Type " & $aLvl & " <= Type " & $bLvl)
          return nil
        # Level violation (aLvl > bLvl): fall through to the handler
        # stack and defaultConv for the standard "not convertible" error.
      var i = ms.convHandlers.high
      while i >= 0:
        let h = ms.convHandlers[i]
        let r = h.decide(ms, s, a1, b1, loc, ctx.len, goalTy)
        case r.verdict
        of cvDischarged:
          traceEvt(tcConv, "conv.handler",
                   "convHandlers[" & $i & "] discharged")
          if not h.coreValid:
            # A domain handler extended conversion beyond the core: record it
            # so elabDefDecl can relax the core re-check for this definition.
            inc ms.extDischarges
          return nil
        of cvDischargedEv:
          # Issue #45: evidence-returning discharge. The core revalidates the
          # evidence with no handlers installed; trust is NOT extended, so
          # extDischarges is untouched and elabDefDecl's bare-core re-check
          # stays in force for this definition. The validated evidence is
          # returned for splicing (tacRefl uses it as the tactic's proof term).
          traceEvt(tcConv, "conv.handler",
                   "convHandlers[" & $i & "] discharged-with-evidence")
          return validateEvidence(ms, s, a1, b1, goalTy, r.evidence, loc, ctx, globals)
        of cvDeclined:
          discard
        dec i
      traceEvt(tcConv, "conv.default", "no handler discharged")
      defaultConv(ms, s, a1, b1, loc, ctx, globals, expLoc)
      nil

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
         ctxLen: int, goalTy: Term): ConvResult {.closure.} =
      # Issue #4: count every probe and every hit (never affects verdicts).
      ms.convCacheProbes.inc
      let (hit, _) = areEqualCached(ms.convCache,
                                    convKey(ctxLen, a, b))
      if hit:
        ms.convCacheHits.inc
        ConvResult(verdict: cvDischarged)
      else: ConvResult(verdict: cvDeclined)
  ConvHandler(decide: decide, coreValid: true)

type NatPoly = object
  cst*: int
  coeff*: Table[string, int]  # atom key -> coefficient

proc polyAdd(a, b: NatPoly): NatPoly =
  result.cst = a.cst + b.cst
  result.coeff = a.coeff
  for k, v in b.coeff:
    result.coeff.mgetOrPut(k, 0) += v

proc spineOf*(t: Term): tuple[head: Term, args: seq[Term]] =
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

# --- Issue #45: evidence synthesis for natArithHandler -------------------
#
# The Andromeda endgame for the Nat decision procedure: instead of trusting
# it, the handler returns a proof Term the bare core revalidates. The four
# linear-arithmetic lemmas (addZeroR/addSucR/addComm/addAssoc) are
# synthesized once per handler construction as closed Terms via Nat's
# eliminator and Eq's eliminator (J), each verified with the bare core
# with no handlers installed — so there is no circularity with the
# `by arith` corpus. Per-goal evidence is a transitivity chain of
# congruence + lemma steps over a proof-carrying normalization to a
# canonical form (sorted summand list).
#
# All terms below are built with de Bruijn indices (vv(i), innermost-first);
# shiftN re-weakens an embedded term under additional binders.

proc appN*(f: Term, args: seq[Term]): Term =
  result = f
  for a in args: result = tmApp(result, a)

proc shiftN*(t: Term, n: int): Term =
  ## Weaken t under n additional binders.
  result = t
  for _ in 0 ..< n: result = weaken(result)

type ExoticArithShape* = object of CatchableError
  ## normEvArith's escape hatch: a zero/suc/add-headed term in a shape the
  ## proof-carrying normalizer does not cover (e.g. add applied to more
  ## than 2 arguments — a leniency of normNat). The handler falls back to
  ## the trusted discharge for these.

type ArithLemmas* = object
  ok*: bool           # false: synthesis failed; use the trusted path
  failReason*: string # why, for diagnostics
  natT*, zeroT*, sucT*, addT*: Term
  eqT*, reflT*, natElimT*, eqElimT*: Term
  addZeroR*, addSucR*, addComm*, addAssoc*: Term  # closed proof terms

proc eqNatAt*(L: ArithLemmas, x, y: Term): Term =
  appN(L.eqT, @[L.natT, x, y])

proc reflAtN*(L: ArithLemmas, x: Term): Term =
  appN(L.reflT, @[L.natT, x])

proc addAt*(L: ArithLemmas, x, y: Term): Term = appN(L.addT, @[x, y])
proc sucAt*(L: ArithLemmas, x: Term): Term = tmApp(L.sucT, x)

proc congAt*(L: ArithLemmas, f, x, y, p: Term): Term =
  ## J-based congruence: from p : Eq Nat x y derive Eq Nat (f x) (f y).
  ## motive = lam (z:Nat). lam (q : Eq Nat x z). Eq Nat (f x) (f z).
  let x1 = shiftN(x, 1)
  let x2 = shiftN(x, 2)
  let f2 = shiftN(f, 2)
  let motive = tmLam(L.natT, "z",
    tmLam(L.eqNatAt(x1, vv(0)), "q",
      L.eqNatAt(tmApp(f2, x2), tmApp(f2, vv(1)))))
  let base = L.reflAtN(tmApp(f, x))
  appN(L.eqElimT, @[L.natT, x, motive, base, y, p])

proc symAt*(L: ArithLemmas, x, y, p: Term): Term =
  ## From p : Eq Nat x y derive Eq Nat y x.
  ## motive = lam (z:Nat). lam (q : Eq Nat x z). Eq Nat z x.
  ## NB: the domain of q is under (ctx, z) — one binder — so x needs
  ## shiftN(x, 1) there (x1); the body under (ctx, z, q) needs shiftN(x, 2).
  let x1 = shiftN(x, 1)
  let x2 = shiftN(x, 2)
  let motive = tmLam(L.natT, "z",
    tmLam(L.eqNatAt(x1, vv(0)), "q",
      L.eqNatAt(vv(1), x2)))
  let base = L.reflAtN(x)
  appN(L.eqElimT, @[L.natT, x, motive, base, y, p])

proc transAt*(L: ArithLemmas, x, y, z, p, q: Term): Term =
  ## From p : Eq Nat x y and q : Eq Nat y z derive Eq Nat x z.
  ## motive = lam (w:Nat). lam (r : Eq Nat x w). Eq Nat w z -> Eq Nat x z.
  ## NB: the domain of r is under (ctx, w) — one binder — so x needs
  ## shiftN(x, 1) there (x1); the r-body under (ctx, w, r) needs shiftN(x, 2)
  ## (x2, z2); and the inner Pi's body under (ctx, w, r, _) needs
  ## shiftN(x, 3) (x3, z3).
  let x1 = shiftN(x, 1)
  let x2 = shiftN(x, 2)
  let z2 = shiftN(z, 2)
  let x3 = shiftN(x, 3)
  let z3 = shiftN(z, 3)
  let motive = tmLam(L.natT, "w",
    tmLam(L.eqNatAt(x1, vv(0)), "r",
      tmPi(L.eqNatAt(vv(1), z2), "_", L.eqNatAt(x3, z3))))
  let base = tmLam(L.eqNatAt(x, z), "s", vv(0))
  appN(L.eqElimT, @[L.natT, x, motive, base, y, p, q])

proc addHeadLam*(L: ArithLemmas, fixed: Term): Term =
  ## lam (w:Nat). add fixed w
  tmLam(L.natT, "w", L.addAt(shiftN(fixed, 1), vv(0)))

proc addArgLam*(L: ArithLemmas, fixed: Term): Term =
  ## lam (w:Nat). add w fixed
  tmLam(L.natT, "w", L.addAt(vv(0), shiftN(fixed, 1)))

proc sucLamOf*(L: ArithLemmas): Term =
  tmLam(L.natT, "v", L.sucAt(vv(0)))

proc buildAddZeroR*(L: ArithLemmas): tuple[ty, tm: Term] =
  ## addZeroR : Pi (n:Nat). Eq Nat (add n zero) n, by induction on n.
  ## Step: C (suc k) needs Eq Nat (suc (add k zero)) (suc k) — cong suc ih,
  ## since add (suc k) zero unfolds definitionally to suc (add k zero).
  let C = tmLam(L.natT, "m", L.eqNatAt(L.addAt(vv(0), L.zeroT), vv(0)))
  let mz = L.reflAtN(L.zeroT)  # add zero zero ≡ zero
  let ihTy = L.eqNatAt(L.addAt(vv(0), L.zeroT), vv(0))  # C k, under (k)
  let msBody = L.congAt(L.sucLamOf(), L.addAt(vv(1), L.zeroT), vv(1), vv(0))
  let ms = tmLam(L.natT, "k", tmLam(ihTy, "ih", msBody))
  let tm = tmLam(L.natT, "n", appN(L.natElimT, @[C, mz, ms, vv(0)]))
  let ty = tmPi(L.natT, "n", L.eqNatAt(L.addAt(vv(0), L.zeroT), vv(0)))
  (ty, tm)

proc buildAddSucR*(L: ArithLemmas): tuple[ty, tm: Term] =
  ## addSucR : Pi (m:Nat)(n:Nat). Eq Nat (add n (suc m)) (suc (add n m)),
  ## by induction on n with m as an outer parameter.
  # Positions: under (m, n): m = vv(1), n = vv(0);
  # C's body under (m, n, k): m = vv(2); ms body under (m, n, k, ih): m = vv(3).
  let C = tmLam(L.natT, "k",
    L.eqNatAt(L.addAt(vv(0), L.sucAt(vv(2))), L.sucAt(L.addAt(vv(0), vv(2)))))
  let mz = L.reflAtN(L.sucAt(vv(1)))  # add zero (suc m) ≡ suc m ≡ suc (add zero m)
  # ihTy is the domain of the ih binder: under (m, n, k), so m = vv(2)
  # (not vv(3) — that is the body depth under (m, n, k, ih)).
  let ihTy = L.eqNatAt(L.addAt(vv(0), L.sucAt(vv(2))),
                       L.sucAt(L.addAt(vv(0), vv(2))))
  let msBody = L.congAt(L.sucLamOf(),
    L.addAt(vv(1), L.sucAt(vv(3))), L.sucAt(L.addAt(vv(1), vv(3))), vv(0))
  let ms = tmLam(L.natT, "k", tmLam(ihTy, "ih", msBody))
  let tm = tmLam(L.natT, "m",
    tmLam(L.natT, "n", appN(L.natElimT, @[C, mz, ms, vv(0)])))
  let ty = tmPi(L.natT, "m", tmPi(L.natT, "n",
    L.eqNatAt(L.addAt(vv(0), L.sucAt(vv(1))), L.sucAt(L.addAt(vv(0), vv(1))))))
  (ty, tm)

proc buildAddComm*(L: ArithLemmas): tuple[ty, tm: Term] =
  ## addComm : Pi (m:Nat)(n:Nat). Eq Nat (add n m) (add m n),
  ## by induction on n with m outer.
  # Base: C zero = Eq Nat (add zero m) (add m zero):
  #   trans (refl m) (sym (addZeroR m)).
  # Step: C (suc k) via trans (cong suc ih) (sym (addSucR k m)).
  let C = tmLam(L.natT, "k",
    L.eqNatAt(L.addAt(vv(0), vv(2)), L.addAt(vv(2), vv(0))))
  let m1 = vv(1)  # under (m, n)
  let mz = L.transAt(L.addAt(L.zeroT, m1), m1, L.addAt(m1, L.zeroT),
    L.reflAtN(m1),
    L.symAt(L.addAt(m1, L.zeroT), m1, appN(L.addZeroR, @[m1])))
  let m3 = vv(3); let k1 = vv(1)  # under (m, n, k, ih)
  # ihTy is the domain of ih: under (m, n, k), so k = vv(0), m = vv(2).
  let ihTy = L.eqNatAt(L.addAt(vv(0), vv(2)), L.addAt(vv(2), vv(0)))
  let step1 = L.congAt(L.sucLamOf(), L.addAt(k1, m3), L.addAt(m3, k1), vv(0))
  let step2 = L.symAt(L.addAt(m3, L.sucAt(k1)), L.sucAt(L.addAt(m3, k1)),
    appN(L.addSucR, @[k1, m3]))  # addSucR k m : Eq (add m (suc k)) (suc (add m k))
  let msBody = L.transAt(L.sucAt(L.addAt(k1, m3)), L.sucAt(L.addAt(m3, k1)),
    L.addAt(m3, L.sucAt(k1)), step1, step2)
  let ms = tmLam(L.natT, "k", tmLam(ihTy, "ih", msBody))
  let tm = tmLam(L.natT, "m",
    tmLam(L.natT, "n", appN(L.natElimT, @[C, mz, ms, vv(0)])))
  let ty = tmPi(L.natT, "m", tmPi(L.natT, "n",
    L.eqNatAt(L.addAt(vv(0), vv(1)), L.addAt(vv(1), vv(0)))))
  (ty, tm)

proc buildAddAssoc*(L: ArithLemmas): tuple[ty, tm: Term] =
  ## addAssoc : Pi (b:Nat)(c:Nat)(a:Nat).
  ##   Eq Nat (add a (add b c)) (add (add a b) c), by induction on a.
  # Base: both sides unfold to add b c. Step: cong suc ih.
  # C's body under (b, c, a, k): k = vv(0), a = vv(1), c = vv(2), b = vv(3).
  let C = tmLam(L.natT, "k",
    L.eqNatAt(L.addAt(vv(0), L.addAt(vv(3), vv(2))),
              L.addAt(L.addAt(vv(0), vv(3)), vv(2))))
  let mz = L.reflAtN(L.addAt(vv(2), vv(1)))  # under (b, c, a)
  let b4 = vv(4); let c3 = vv(3); let k1 = vv(1)  # under (b, c, a, k, ih)
  # ihTy is the domain of ih: under (b, c, a, k), so k = vv(0), b = vv(3),
  # c = vv(2) (not the body-depth indices b4/c3/k1).
  let ihTy = L.eqNatAt(L.addAt(vv(0), L.addAt(vv(3), vv(2))),
                       L.addAt(L.addAt(vv(0), vv(3)), vv(2)))
  let msBody = L.congAt(L.sucLamOf(),
    L.addAt(k1, L.addAt(b4, c3)), L.addAt(L.addAt(k1, b4), c3), vv(0))
  let ms = tmLam(L.natT, "k", tmLam(ihTy, "ih", msBody))
  let tm = tmLam(L.natT, "b", tmLam(L.natT, "c", tmLam(L.natT, "a",
    appN(L.natElimT, @[C, mz, ms, vv(0)]))))
  let ty = tmPi(L.natT, "b", tmPi(L.natT, "c", tmPi(L.natT, "a",
    L.eqNatAt(L.addAt(vv(0), L.addAt(vv(2), vv(1))),
              L.addAt(L.addAt(vv(0), vv(2)), vv(1))))))
  (ty, tm)

proc checkLemma(s: var Supply, ty, tm: Term, name: string) =
  ## Verify a synthesized lemma with the bare core (no handlers installed):
  ## the handler's evidence is only as trustworthy as these proofs.
  try:
    discard check(s, eval(ty, @[]), tm)
  except ValueError as e:
    when defined(arithDebug):
      echo "LEMMA ", name, " FAILED"
      echo "  ty: ", $ty
      echo "  tm: ", $tm
    raise newException(ValueError, "lemma '" & name &
      "' rejected by the bare core: " & sanitizeKernelMsg(e.msg))

proc needRef(globals: Globals, name: string): Term =
  if name notin globals:
    raise newException(ValueError, "'" & name & "' not in scope")
  let t = globals[name].tm
  if t.kind != tR:
    raise newException(ValueError, "'" & name & "' is not a reference")
  t

proc buildArithLemmas*(globals: Globals, s: var Supply): ArithLemmas =
  ## Synthesize the four linear-arithmetic lemmas as closed Terms and
  ## verify each with the bare core. ok=false (with failReason) when a
  ## prerequisite is missing or a proof does not check — the handler then
  ## keeps the trusted discharge path.
  try:
    result.natT = needRef(globals, "Nat")
    result.zeroT = needRef(globals, "zero")
    result.sucT = needRef(globals, "suc")
    result.addT = needRef(globals, "add")
    result.natElimT = needRef(globals, "natElim")
    result.eqT = needRef(globals, "Eq")
    result.reflT = needRef(globals, "refl")
    result.eqElimT = needRef(globals, "eqElim")
    let zr = buildAddZeroR(result)
    checkLemma(s, zr.ty, zr.tm, "addZeroR")
    result.addZeroR = zr.tm
    let sr = buildAddSucR(result)
    checkLemma(s, sr.ty, sr.tm, "addSucR")
    result.addSucR = sr.tm
    let cm = buildAddComm(result)
    checkLemma(s, cm.ty, cm.tm, "addComm")
    result.addComm = cm.tm
    let asc = buildAddAssoc(result)
    checkLemma(s, asc.ty, asc.tm, "addAssoc")
    result.addAssoc = asc.tm
    result.ok = true
  except CatchableError as e:
    result.ok = false
    result.failReason = e.msg

type
  ArithUnit = tuple[key: string, tm: Term, isOne: bool]
    ## One summand of the canonical form: an atom (variable or opaque
    ## subterm, keyed exactly like normNat's polynomial atoms) or a unit
    ## of the constant part (`suc zero`, sorted last).
  ArithNorm* = object
    poly*: NatPoly
    units*: seq[ArithUnit]  # canonical (sorted) order
    canon*: Term            # right-nested adds of the units
    proof*: Term            # Eq Nat t canon

proc canonArith*(L: ArithLemmas, units: seq[ArithUnit]): Term =
  result = L.zeroT
  for i in countdown(units.high, 0):
    result = L.addAt(units[i].tm, result)

proc oneUnit*(L: ArithLemmas): ArithUnit =
  (key: "", tm: L.sucAt(L.zeroT), isOne: true)

proc sucPushArith*(L: ArithLemmas, us: seq[ArithUnit]): Term =
  ## Eq Nat (suc (canon us)) (canon (us ++ [1])): push the suc rightward
  ## through the adds with addSucR. Base case is definitional
  ## (add (suc zero) zero unfolds to suc zero).
  if us.len == 0:
    return L.reflAtN(L.sucAt(L.zeroT))
  let u = us[0]
  let rest = us[1 .. ^1]
  let cRest = canonArith(L, rest)
  let step = L.symAt(L.addAt(u.tm, L.sucAt(cRest)),
                     L.sucAt(L.addAt(u.tm, cRest)),
                     appN(L.addSucR, @[cRest, u.tm]))
  let rec = sucPushArith(L, rest)
  let tailCanon = canonArith(L, rest & oneUnit(L))
  let congRec = L.congAt(L.addHeadLam(u.tm), L.sucAt(cRest), tailCanon, rec)
  L.transAt(L.sucAt(L.addAt(u.tm, cRest)), L.addAt(u.tm, L.sucAt(cRest)),
            L.addAt(u.tm, tailCanon), step, congRec)

proc peelArith*(L: ArithLemmas, us1, us2: seq[ArithUnit]):
    tuple[units: seq[ArithUnit], proof: Term] =
  ## Eq Nat (add (canon us1) (canon us2)) (canon (us1 ++ us2)): reassociate
  ## with addAssoc, peeling us1's summands one at a time.
  if us1.len == 0:
    let c2 = canonArith(L, us2)
    return (us2, L.reflAtN(c2))  # add zero c2 ≡ c2, definitionally
  let u = us1[0]
  let rest1 = us1[1 .. ^1]
  let c1r = canonArith(L, rest1)
  let c2 = canonArith(L, us2)
  let assoc = L.symAt(L.addAt(u.tm, L.addAt(c1r, c2)),
                      L.addAt(L.addAt(u.tm, c1r), c2),
                      appN(L.addAssoc, @[c1r, c2, u.tm]))
  let (catR, pRec) = peelArith(L, rest1, us2)
  let pRecC = L.congAt(L.addHeadLam(u.tm), L.addAt(c1r, c2),
                       canonArith(L, catR), pRec)
  let cat = us1 & us2
  (cat, L.transAt(L.addAt(L.addAt(u.tm, c1r), c2),
                  L.addAt(u.tm, L.addAt(c1r, c2)),
                  canonArith(L, cat), assoc, pRecC))

proc unitLess(a, b: ArithUnit): bool =
  ## Canonical order: atoms by key first, constant ones last.
  if a.isOne != b.isOne: return b.isOne
  a.key < b.key

proc swapAtArith*(L: ArithLemmas, prefix: seq[ArithUnit], x, y: ArithUnit,
                 rest: seq[ArithUnit]): Term =
  ## Eq Nat (canon (prefix++[x,y]++rest)) (canon (prefix++[y,x]++rest)):
  ## one adjacent swap, via addAssoc + addComm + addAssoc under the prefix.
  let R = canonArith(L, rest)
  let s1 = appN(L.addAssoc, @[y.tm, R, x.tm])
  let s2 = L.congAt(L.addArgLam(R), L.addAt(x.tm, y.tm), L.addAt(y.tm, x.tm),
                    appN(L.addComm, @[y.tm, x.tm]))
  let s3 = L.symAt(L.addAt(y.tm, L.addAt(x.tm, R)),
                   L.addAt(L.addAt(y.tm, x.tm), R),
                   appN(L.addAssoc, @[x.tm, R, y.tm]))
  let core = L.transAt(L.addAt(x.tm, L.addAt(y.tm, R)),
                       L.addAt(L.addAt(y.tm, x.tm), R),
                       L.addAt(y.tm, L.addAt(x.tm, R)),
                       L.transAt(L.addAt(x.tm, L.addAt(y.tm, R)),
                                 L.addAt(L.addAt(x.tm, y.tm), R),
                                 L.addAt(L.addAt(y.tm, x.tm), R), s1, s2), s3)
  var fbody = vv(0)
  for i in countdown(prefix.high, 0):
    fbody = L.addAt(shiftN(prefix[i].tm, 1), fbody)
  let f = tmLam(L.natT, "w", fbody)
  let X = L.addAt(x.tm, L.addAt(y.tm, R))
  let Y = L.addAt(y.tm, L.addAt(x.tm, R))
  L.congAt(f, X, Y, core)

proc sortArith*(L: ArithLemmas, units: seq[ArithUnit]):
    tuple[units: seq[ArithUnit], proof: Term] =
  ## Insertion sort into canonical order; each adjacent swap contributes
  ## its proof, chained with transitivity.
  var us = units
  var pf = L.reflAtN(canonArith(L, units))
  for i in 1 ..< us.len:
    var j = i
    while j > 0 and unitLess(us[j], us[j-1]):
      let sw = swapAtArith(L, us[0 ..< j-1], us[j-1], us[j], us[j+1 .. ^1])
      var us2 = us
      let tmp = us2[j-1]; us2[j-1] = us2[j]; us2[j] = tmp
      pf = L.transAt(canonArith(L, units), canonArith(L, us),
                     canonArith(L, us2), pf, sw)
      us = us2
      dec j
  (us, pf)

proc mergeArith*(L: ArithLemmas, us1, us2: seq[ArithUnit]):
    tuple[units: seq[ArithUnit], proof: Term] =
  ## Eq Nat (add (canon us1) (canon us2)) (canon (sorted (us1 ++ us2))).
  let (cat, pcat) = peelArith(L, us1, us2)
  let (srt, psrt) = sortArith(L, cat)
  (srt, L.transAt(L.addAt(canonArith(L, us1), canonArith(L, us2)),
                  canonArith(L, cat), canonArith(L, srt), pcat, psrt))

proc normEvArith*(L: ArithLemmas, t: Term): ArithNorm =
  ## Proof-carrying Nat normalization: the polynomial (computed exactly as
  ## normNat computes it), the canonical term, and a proof
  ## `Eq Nat t canon`. Raises ExoticArithShape for zero/suc/add-headed
  ## terms in shapes the prover does not cover (the caller then falls back
  ## to the trusted discharge, preserving the old behavior).
  let (head, args) = spineOf(t)
  if head.kind == tR and head.refId == L.zeroT.refId:
    if args.len != 0: raise newException(ExoticArithShape, "zero with args")
    let c = canonArith(L, @[])
    return ArithNorm(poly: NatPoly(cst: 0, coeff: initTable[string, int]()),
                     units: @[], canon: c, proof: L.reflAtN(c))
  if head.kind == tR and head.refId == L.sucT.refId:
    if args.len != 1: raise newException(ExoticArithShape, "suc arity")
    let r = normEvArith(L, args[0])
    let units = r.units & oneUnit(L)
    let c = canonArith(L, units)
    let p1 = L.congAt(L.sucLamOf(), args[0], r.canon, r.proof)
    let push = sucPushArith(L, r.units)
    let proof = L.transAt(L.sucAt(args[0]), L.sucAt(r.canon), c, p1, push)
    var poly = r.poly
    poly.cst += 1
    return ArithNorm(poly: poly, units: units, canon: c, proof: proof)
  if head.kind == tR and head.refId == L.addT.refId:
    if args.len > 2: raise newException(ExoticArithShape, "add arity")
    if args.len == 2:
      # args is innermost-first: args[1] is the first argument.
      let x = args[1]; let y = args[0]
      let r1 = normEvArith(L, x)
      let r2 = normEvArith(L, y)
      let c1 = r1.canon; let c2 = r2.canon
      let s1 = L.congAt(L.addArgLam(y), x, c1, r1.proof)
      let s2 = L.congAt(L.addHeadLam(c1), y, c2, r2.proof)
      let q12 = L.transAt(L.addAt(x, y), L.addAt(c1, y), L.addAt(c1, c2),
                          s1, s2)
      let (mus, mpf) = mergeArith(L, r1.units, r2.units)
      let c = canonArith(L, mus)
      let proof = L.transAt(L.addAt(x, y), L.addAt(c1, c2), c, q12, mpf)
      return ArithNorm(poly: polyAdd(r1.poly, r2.poly), units: mus,
                       canon: c, proof: proof)
    # else: partial application — an opaque atom, exactly like normNat.
  # Opaque atom (variables and non-Nat subterms), keyed like normNat.
  # The canonical form is `add t zero`, so the proof is not reflexivity:
  # sym (addZeroR t) : Eq t (add t zero).
  var co = initTable[string, int]()
  let k = if t.kind == tV: "v" & $t.idx else: "t:" & $t
  co[k] = 1
  let u: ArithUnit = (key: k, tm: t, isOne: false)
  let c = canonArith(L, @[u])
  ArithNorm(poly: NatPoly(cst: 0, coeff: co), units: @[u],
            canon: c, proof: L.symAt(c, t, appN(L.addZeroR, @[t])))

proc buildArithEvidence*(L: ArithLemmas, a, b: Term):
    tuple[found: bool, evidence: Term] =
  ## Prove `Eq Nat a b` for Nat-fragment sides with equal normal forms:
  ## a ≡ canon(a) ≡ canon(b) ≡ b. The middle step is reflexivity — both
  ## canonical terms are built deterministically from the same sorted
  ## summand multiset, so they are structurally identical (checked via
  ## the rendering; the bare core revalidates the whole chain anyway).
  ## Raises ExoticArithShape when a side is outside the covered fragment.
  let ra = normEvArith(L, a)
  let rb = normEvArith(L, b)
  if ra.poly.cst != rb.poly.cst or ra.poly.coeff != rb.poly.coeff:
    return (false, nil)
  let ca = ra.canon
  let cb = rb.canon
  if $ca != $cb:
    raise newException(ExoticArithShape, "canonical forms differ")
  let cab = L.reflAtN(ca)  # : Eq Nat ca cb, by structural identity
  let ev = L.transAt(a, ca, b, ra.proof,
                     L.transAt(ca, cb, b, cab, L.symAt(b, cb, rb.proof)))
  (true, ev)

proc isEqSpineGoal(a, b: Term, eqId: int): bool =
  ## Shape check mirroring natConv's Eq-congruence case (type-vs-type
  ## goals like `Eq Nat x x` vs `Eq Nat x y`): those stay on the trusted
  ## path — evidence for Eq-of-Eq needs double-J congruence (future work).
  if eqId < 0: return false
  let (ha, aa) = spineOf(a)
  let (hb, bb) = spineOf(b)
  ha.kind == tR and hb.kind == tR and ha.refId == eqId and
    hb.refId == eqId and aa.len == bb.len and aa.len >= 3

proc natArithHandler*(globals: Globals, s: var Supply): ConvHandler =
  ## Experiment 41: a tiny domain-specific decision procedure for linear
  ## Nat equations over {zero, suc, add}, installed with dynamic scope
  ## (see the `arith` tactic). It discharges goals the default conversion
  ## cannot — e.g. `add n (suc m) === suc (add n m)` with neutral n, m,
  ## where the core's NbE gets stuck on the neutral first argument — by
  ## normalizing both sides to c + Σ kᵢ·xᵢ and comparing.
  ##
  ## Issue #45: evidence-returning discharge. At construction the four
  ## linear-arithmetic lemmas (addZeroR/addSucR/addComm/addAssoc) are
  ## synthesized as closed Terms via Nat's eliminator and verified with
  ## the bare core (no handlers installed — no circularity with the
  ## `by arith` corpus). Each goal's evidence is a transitivity chain of
  ## congruence + lemma steps over a proof-carrying normalization; the
  ## bare core revalidates it (see validateEvidence), so installing the
  ## handler extends automation, not trust. Goals outside the evidence
  ## path's reach (Eq-congruence type goals, exotic add/suc shapes, or a
  ## failed lemma synthesis) keep the old trusted cvDischarged behavior.
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
  let lemmas = buildArithLemmas(globals, s)
  result.coreValid = false
  result.decide =
    proc(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
         ctxLen: int, goalTy: Term): ConvResult {.closure.} =
      if addId < 0 or zeroId < 0 or sucId < 0:
        return ConvResult(verdict: cvDeclined)  # no Nat/add in scope: nothing to decide
      if lemmas.ok and not goalTy.isNil and not isEqSpineGoal(a, b, eqId):
        try:
          let r = buildArithEvidence(lemmas, a, b)
          if r.found:
            return ConvResult(verdict: cvDischargedEv, evidence: r.evidence)
          return ConvResult(verdict: cvDeclined)
        except ExoticArithShape:
          discard  # fall through to the trusted path below
      # Trusted fast path (Experiment 41): normalization decides, and the
      # core re-check is relaxed via extDischarges. Reached when lemma
      # synthesis failed, the goal type is unknown, for Eq-congruence
      # type goals, and for exotic shapes the evidence builder skips.
      if natConv(a, b, zeroId, sucId, addId, eqId):
        ConvResult(verdict: cvDischarged)
      else: ConvResult(verdict: cvDeclined)

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
  traceEvt(tcQty, "qty.solve", vname & " := " & $q)
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
        " time(s) in term position: erased (quantity-0) variables may only " &
        "be used in types")
  of q1:
    if n == 0:
      raise elabErr(loc, "linear variable '" & name &
        "' not used (expected exactly once): a linear binder must be used " &
        "exactly once in the body")
    elif n > 1:
      raise elabErr(loc, "linear variable '" & name & "' used " & $n &
        " times (expected exactly once): use the variable exactly once in " &
        "the body")
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
  traceEvt(tcQty, "qty.check",
           name & " :^" & (if qty.isVar: "qvar(" & qty.vname & ")"
                           else: $qty.q))
  if qty.isVar:
    let zb = zonk(ms, body)
    # A body that still mentions unsolved metas can't be counted reliably
    # (a hole may later solve to a use); the post-pass re-checks at the end
    # of the declaration, when metas are solved or reported. The variable
    # then keeps its default (qOmega, see zonkQty).
    if hasUnresolvedMetas(zb): return
    let n = countVarUses(zb)
    # Issue #84 (conservative inference): a `#q`-prefixed variable is an
    # *inferred default* (unannotated binder, see parse_surf.parseBinder),
    # not a user-written `(q x : A)`. Inferred defaults solve 0 -> q0
    # (erasure) and otherwise -> qOmega. They never solve to q1: the
    # kernel (#66) converts Pi binder quantities exactly, so an inferred
    # q1 would not convert against the qOmega positions the existing
    # corpus was written with (e.g. `myid A : Pi (x:A)[q1]. A` against
    # `vmap`'s `Pi (x:A)[qOmega]. A` domain). Linearity inference (q1) is
    # future work, pending either kernel quantity subsumption or a
    # quantity-precise corpus. User-written qvars keep the full rule.
    let inferred = if n == 0: q0
                   elif qty.vname.len > 2 and qty.vname[0 .. 1] == "#q": qOmega
                   elif n == 1: q1
                   else: qOmega
    solveQVar(ms, qty.vname, inferred, loc)
    flushQvarPending(ms, qty.vname)
    return
  enforceQtyCount(qty.q, body, loc, name, ms)

proc reconcileInferredQty(tyPre, tmPre: PreTerm, tmT0, tmTy: Term,
                          ms: var MetaStore) =
  ## Issue #84: reconcile the quantity-first inference with the ascribed
  ## type before either is zonked. Walks four spines in parallel — the
  ## ascribed type (pkPi), the inferred type (tPi), the body surface
  ## (pkLam, for usage-site locations) and the elaborated body (tLam) —
  ## which mirror each other while the walk advances; anything else (arity
  ## or non-quantity mismatch) falls through to the generic conversion
  ## check.
  ## - Ascribed quantity variable: solve it from the inference
  ##   (solveQVar). A variable the body's inference already solved
  ##   (telescope binders share theirs with the body) agrees by
  ##   construction, so this is a no-op; an unsolved one — an unannotated
  ##   binder written only in the ascribed type — is solved positionally
  ##   ("unannotated" means "infer", wherever the binder is written). A
  ##   genuine conflict raises solveQVar's error.
  ## - Ascribed qOmega: never conflicts — it is the "don't care" quantity
  ##   (`A -> B` desugars to an omega Pi). An inferred q0 is widened to
  ##   qOmega in both the term and the inferred type, so `N -> N` keeps
  ##   accepting bodies that ignore the argument, exactly as on main (the
  ##   kernel's checking rule ignores lambda/Pi quantities; only the
  ##   elaborator's exact conversion needs them to agree).
  ## - Ascribed explicit 0/1 disagreeing with the inference: an error naming
  ##   the binder and the usage sites that forced the inference — instead
  ##   of the generic conversion "quantity mismatch", whose printed types
  ##   do not even show binder quantities.
  var tp = tyPre
  var tt = tmTy
  var bp = tmPre
  var bt = tmT0
  while tp.kind == pkPi and tt.kind == tPi and
        bp.kind == pkLam and bt.kind == tLam:
    if tp.qty.isVar:
      solveQVar(ms, tp.qty.vname, tt.qty, tp.loc)
    elif tp.qty.q == qOmega:
      if tt.qty == q0:
        bt.qty = qOmega
        tt.qty = qOmega
    elif tp.qty.q != tt.qty:
      let uses = collectBinderUseLocs(bp.c2, bp)
      let useMsg =
        if uses.len == 0: "the body never uses '" & bp.name & "'"
        else: "the body uses '" & bp.name & "' " & $uses.len & " time(s) at " &
          uses[0 ..< min(uses.len, 5)].mapIt("line " & $it.line &
            ", col " & $it.col).join("; ") &
          (if uses.len > 5: "; and " & $(uses.len - 5) & " more" else: "")
      raise elabErr(tp.loc,
        "quantity mismatch for binder '" & bp.name & "': the ascribed type " &
        "requires quantity " & $tp.qty.q & ", but " & useMsg &
        ", inferring quantity " & $tt.qty &
        " (unannotated binders infer 0 when unused, \u03c9 otherwise; " &
        "quantity 1 is never inferred \u2014 to demand linearity, annotate " &
        "the body's binder explicitly, e.g. `lam (1 " & bp.name &
        " : T). \u2026`)")
    tp = tp.c2
    tt = tt.scope.bdy
    bp = bp.c2
    bt = bt.scope.bdy

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
  of tR, tC, tType, tMeta, tInt, tNatLit, tNatSing:
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
                loc: Loc, ab: Ability,
                ms: var MetaStore): tuple[tm, ty: Term] =
  for i, e in ctx:
    if e.name == name: return (vv(i), e.ty)
  # Experiment 11: primitive Int operations
  if name in ["addInt", "subInt", "mulInt"] and "Int" in globals:
    let intTy = globals["Int"].tm
    # Issue #177: primops are pure operators; peg at the ambient like a lambda.
    let opTy = tmPi(intTy, "_", tmPi(intTy, "_", intTy, peg = ab), peg = ab)
    let op = case name
      of "addInt": opAdd
      of "subInt": opSub
      else: opMul
    return (tmPrim(op, opTy), opTy)
  if name in globals:
    let g = globals[name]
    if g.isIface:
      raise elabErr(loc, "interface '" & name & "' is not a term")
    if g.cmdIface != "":
      # Issue #177, Command rule: `c : A -> B in I` used under ambient
      # `ab` requires `I` in `ab`; the operator type is pegged at `ab`.
      case abMemberAb(g.cmdIface, ab)
      of amYes:
        if g.ty.kind != tPi:
          raise elabErr(loc, "command '" & name & "' has a non-function type")
        return (g.tm, setPeg(g.ty, ab))
      of amNo:
        raise elabErr(loc, "command '" & name & "' requires interface '" &
          g.cmdIface & "' but the ambient ability is " & $ab)
      of amStuck:
        raise elabErr(loc, "command '" & name & "' requires interface '" &
          g.cmdIface & "', but the ambient ability is not yet known " &
          "(stuck on " & $ab & ")")
    # Ordinary global: the signature's peg must be compatible with the
    # ambient. No freshening: ability variables are never solved, so the
    # stored type is returned unchanged.
    checkPeg(g.peg, ab, loc)
    return (g.tm, g.ty)
  raise elabErr(loc, "unbound variable '" & name & "'")

proc headTy(ms: MetaStore, t: Term): Term  # forward (mutual with fireRedTerm)

proc fireRedTerm(ms: MetaStore, rule: RedRule, args: seq[Term]): Term =
  ## Term-level mirror of core fireRed (eponym_init): one head-iota step for
  ## an eliminator RedRef. `args` is the application spine, outermost-first,
  ## with args.len == rule.nargs; args[0] is the scrutinee (last applied).
  ## Returns nil when the rule is stuck (scrutinee not constructor-headed),
  ## in which case the application stays neutral.
  ## Issue #88: headTy must see through eliminator reduction so that types
  ## computed by elimination (e.g. `mapCont U0 A B`) expose their Pi head.
  let scrut = headTy(ms, zonk(ms, args[0]))
  var sargs: seq[Term] = @[]
  var sf = scrut
  while sf.kind == tApp:
    sargs.add(sf.arg)
    sf = sf.fn
  if sf.kind != tR or sf.refId notin rule.cases:
    return nil
  # constructor args, application order, skipping the already-bound params
  # (Experiment 5: params are elim variables, not fresh ctor variables)
  var cargs: seq[Term] = @[]
  for i in rule.nParams ..< sargs.len:
    cargs.add(sargs[sargs.len - 1 - i])
  for ca in cargs:
    if ca.kind in {tFst, tSnd, tAbsurd}:
      return nil  # the core stays neutral on projected scrutinee args
  # substSpine spine, innermost-first: reversed ctor args, then reversed
  # elim args (excluding the scrutinee) — the same order as core fireRed
  var spine: seq[Term] = @[]
  for i in countdown(cargs.high, 0):
    spine.add(zonk(ms, cargs[i]))
  for i in 1 .. args.high:
    spine.add(zonk(ms, args[i]))
  substSpine(rule.cases[sf.refId], spine)

proc headTy(ms: MetaStore, t: Term): Term =
  ## Head-normalize a type for the elaborator: zonk, unfold definitions,
  ## head-beta, head-iota for constructor-headed eliminator redexes
  ## (Issue #88: types computed by elimination must expose their head).
  ## Purely syntactic; the core's eval is never involved.
  var cur = zonk(ms, t)
  while true:
    case cur.kind
    of tApp:
      # Flatten the spine to expose the head: firing iota needs the whole
      # argument list (nargs check + scrutinee), which the old one-argument
      # recursion could never see.
      var args: seq[Term] = @[]
      var f = cur
      while f.kind == tApp:
        args.add(f.arg)
        f = f.fn
      let fh = headTy(ms, f)
      if fh.kind == tLam and args.len >= 1:
        var r = zonk(ms, subst(fh.scope.bdy, 0, args[^1]))
        for i in countdown(args.high - 1, 0):
          r = tmApp(r, args[i])
        cur = r
      elif fh.kind == tR and not fh.refVal.isNil and
           fh.refVal.whnf.kind == wRed and
           args.len == fh.refVal.whnf.rule.nargs:
        let inst = fireRedTerm(ms, fh.refVal.whnf.rule, args)
        if inst.isNil:
          var r = fh
          for i in countdown(args.high, 0):
            r = tmApp(r, zonk(ms, args[i]))
          return r
        cur = zonk(ms, inst)
      else:
        var r = fh
        for i in countdown(args.high, 0):
          r = tmApp(r, zonk(ms, args[i]))
        return r
    of tR:
      if not cur.refVal.isNil and cur.refVal.whnf.kind == wRed:
        # Eliminator reference: newRedRef sets refVal.syn to the ref itself,
        # so unfolding would loop forever (this hung #88's use sites).
        # A bare RedRef is neutral for headTy; iota fires in the tApp case.
        return cur
      if cur.refIsDefn and not cur.refVal.isNil:
        cur = zonk(ms, cur.refVal.syn)
      else:
        return cur
    else:
      return cur

proc ensurePi(ms: var MetaStore, loc: Loc, t: Term,
              ctxLen: int, ab: Ability): tuple[dom, codBdy: Term, impl: bool,
              adv: string, qty: Quantity, peg: Ability] =
  ## t's head must be a Pi; a metavariable head is unified with a fresh
  ## (explicit) Pi. Returns dom, the codomain body (in the extended frame),
  ## the binder's quantity (Issue #66: part of the Pi type), and the
  ## operator peg (Issue #177). A Pi invented for a meta head is pegged at
  ## the ambient ability, like a lambda.
  let h = headTy(ms, t)
  if h.kind == tPi:
    return (h.dom, h.scope.bdy, h.impl, h.scope.adv, h.qty, h.peg)
  if h.kind == tMeta:
    let dom = freshMeta(ms, tmC(cStar), ctxLen, 0, loc)
    let cod = freshMeta(ms, tmC(cStar), ctxLen, 1, loc)
    unifyElab(ms, h, tmPi(dom, "x", cod, peg = ab), loc)
    return (dom, cod, false, "x", qOmega, ab)
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
  var inserted = 0
  while true:
    let h = headTy(ms, fty)
    if h.kind == tPi and h.impl:
      let m = freshMeta(ms, h.dom, ctxLen, 0, pre.loc)
      f = tmApp(f, m)
      fty = subst(h.scope.bdy, 0, m)
      inc inserted
    else:
      break
  if inserted > 0:
    # Issue #83: only insertions are events; a no-op walk is not interesting.
    traceEvt(tcImplicit, "implicit.insert",
             $inserted & " for " & $pre.kind & " @" &
             $pre.loc.line & ":" & $pre.loc.col)
  (f, fty)

type MetaSnapshot = object
  ## The mutable elaboration state a trial check may disturb (Issue #201).
  entries: Table[int, MetaEntry]
  nextId: int
  holesLen: int
  qvarNames: Table[string, int]
  qvarSols: seq[QtySol]
  qvarPending: Table[string, seq[tuple[varName: string, loc: Loc]]]
  extDischarges: int

proc snapshotMeta(ms: MetaStore): MetaSnapshot =
  ## Capture the mutable state. The qvarPending table is deep-copied: a
  ## shallow table copy would share the pending-entry seqs, so a trial
  ## append would leak into the snapshot.
  var pending = initTable[string, seq[tuple[varName: string, loc: Loc]]]()
  for k, v in ms.qvarPending: pending[k] = @v
  MetaSnapshot(entries: ms.entries, nextId: ms.nextId, holesLen: ms.holes.len,
               qvarNames: ms.qvarNames, qvarSols: ms.qvarSols,
               qvarPending: pending, extDischarges: ms.extDischarges)

proc restoreMeta(ms: var MetaStore, snap: MetaSnapshot) =
  ## Roll back to a snapshot. Abandoned trial metas vanish (their ids are
  ## recycled via nextId) so they can never surface as spurious
  ## "unsolved metavariable" errors; trial hole records are truncated.
  ms.entries = snap.entries
  ms.nextId = snap.nextId
  ms.holes.setLen(snap.holesLen)
  ms.qvarNames = snap.qvarNames
  ms.qvarSols = snap.qvarSols
  ms.qvarPending = snap.qvarPending
  ms.extDischarges = snap.extDischarges

proc inferTm*(pre: PreTerm, ctx: Ctx, globals: Globals,
              ms: var MetaStore, supply: var Supply,
              ab: Ability): tuple[tm, ty: Term]
proc checkTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore, supply: var Supply, expTy: Term,
             ab: Ability, expLoc: Loc = noLoc): Term

proc inferTm*(pre: PreTerm, ctx: Ctx, globals: Globals,
              ms: var MetaStore, supply: var Supply,
              ab: Ability): tuple[tm, ty: Term] =
  profilePhase(epInfer):
      ## Synthesis mode.
      traceGuard(tcInfer, "infer",
                 $pre.kind & " @" & $pre.loc.line & ":" & $pre.loc.col)
      case pre.kind
      of pkVar:
        # Issue #201: no eager implicit insertion here. A bare variable
        # keeps its implicit Pis; application sites (pkApp) resolve them
        # against each argument (explicit when it checks, inserted when
        # not), and checkTm's fallthrough inserts before converting.
        resolveVar(ctx, globals, pre.name, pre.loc, ab, ms)
      of pkUniv: (tmC(cStar), tmC(cStar))
      of pkUnivN:
        # Issue #52: `Type l : Type (l+1)` (the core rule, eponym_init.infer).
        (tmType(pre.intVal), tmType(pre.intVal + 1))
      of pkUnitTy: (tmC(cOne), tmC(cStar))
      of pkUnitV: (tmC(cVoid), tmC(cOne))
      of pkEmptyTy: (tmC(cZero), tmC(cStar))
      of pkHole:
        let tyM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
        let holeTm = freshMeta(ms, tyM, ctx.len, 0, pre.loc)
        # Issue #58: record the hole for LSP hover — goal type + binder context.
        var hctx: seq[tuple[name: string, ty: Term]] = @[]
        for e in ctx: hctx.add((e.name, e.ty))
        ms.holes.add(HoleInfo(holeLoc: pre.loc, holeGoal: tyM, holeCtx: hctx,
                              holeAb: ab))  # Issue #177
        (holeTm, tyM)
      of pkInt:
        # Experiment 11: integer literal; type is the postulated Int
        if "Int" notin globals:
          raise elabErr(pre.loc, "integer literal requires 'postulate Int : ?'")
        let intTy = globals["Int"].tm  # the R node for Int
        (tmInt(pre.intVal), intTy)
      of pkPi:
        let d = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar), ab)
        let c = checkTm(pre.c2, ctx.ext(pre.name, d, pre.qty), globals, ms, supply, tmC(cStar), ab)
        # Issue #52: Pi formation takes the max of the domain/codomain
        # universe levels (the core rule); legacy `?`-classified types
        # contribute level 0.
        let lvl = max(univLevelOfTy(supply, ms, d, ctx),
                      univLevelOfTy(supply, ms, c, ctx.ext(pre.name, d, pre.qty)))
        (tmPi(d, pre.name, c, pre.impl, pre.erased, zonkQty(ms, pre.qty), ab), tmType(lvl))
      of pkSigma:
        let d = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar), ab)
        let c = checkTm(pre.c2, ctx.ext(pre.name, d), globals, ms, supply, tmC(cStar), ab)
        # Issue #52: Sigma formation takes the max of the domain/codomain
        # universe levels (the core rule), like Pi.
        let lvl = max(univLevelOfTy(supply, ms, d, ctx),
                      univLevelOfTy(supply, ms, c, ctx.ext(pre.name, d)))
        (tmSi(d, pre.name, c), tmType(lvl))
      of pkLam:
        let d =
          if pre.c1.isNil: freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
          else: checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar), ab)
        let (b, bty) = inferTm(pre.c2, ctx.ext(pre.name, d, pre.qty), globals, ms, supply, ab)
        enforceBinderQty(pre.qty, b, pre.loc, pre.name, ms)  # Issue #66
        # zonkQty after enforcement: a variable is solved by now (or defaults).
        let bq = zonkQty(ms, pre.qty)
        (tmLam(d, pre.name, b, pre.impl, pre.erased, bq, ab), tmPi(d, pre.name, bty, pre.impl, pre.erased, bq, ab))
      of pkApp:
        var (f, fty) = inferTm(pre.c1, ctx, globals, ms, supply, ab)
        # Issue #201: leading `{ }` implicit binders accept explicit
        # positional arguments. Resolve them against this argument one at
        # a time: if the argument checks against an implicit domain it is
        # consumed explicitly (no insertion); otherwise a fresh meta is
        # inserted for that binder and the argument is retried against the
        # next binder. A failed trial is rolled back so insertion (and the
        # eventual real check) sees clean state; genuine argument errors
        # resurface when the argument is checked against the next binder.
        var a: Term = nil
        var aPeg: Ability = ab
        var consumed = false
        while not consumed:
          let h = headTy(ms, fty)
          if h.kind != tPi or not h.impl: break
          let snap = snapshotMeta(ms)
          var ok = false
          try:
            a = checkTm(pre.c2, ctx, globals, ms, supply, h.dom, ab)
            ok = true
          except ElabError:
            restoreMeta(ms, snap)
          if ok:
            aPeg = h.peg
            if h.qty == q0:
              checkErasedArg(a, ctx, pre.loc, ms)  # Issue #66
            f = tmApp(f, a)
            fty = subst(h.scope.bdy, 0, a)
            consumed = true
          else:
            let m = freshMeta(ms, h.dom, ctx.len, 0, pre.loc)
            f = tmApp(f, m)
            fty = subst(h.scope.bdy, 0, m)
        if consumed:
          # Issue #177, App rule: the operator's peg must be compatible
          # with the ambient (pure predicate).
          checkPeg(aPeg, ab, pre.loc)
          (f, fty)
        else:
          let (dom, codBdy, impl, _, qty, fpeg) = ensurePi(ms, pre.loc, fty, ctx.len, ab)
          if impl:
            raise elabErr(pre.loc,
              "cannot apply explicitly to an implicit argument")
          # Issue #177, App rule: the operator's peg must be compatible
          # with the ambient (pure predicate).
          checkPeg(fpeg, ab, pre.loc)
          let a2 = checkTm(pre.c2, ctx, globals, ms, supply, dom, ab)
          if qty == q0:
            checkErasedArg(a2, ctx, pre.loc, ms)  # Issue #66: no linear var into 0-param
          (tmApp(f, a2), subst(codBdy, 0, a2))
      of pkPair:
        # Non-dependent Sigma with metavariable components (as the core's cPair).
        let aM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
        let bM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
        let a = checkTm(pre.c1, ctx, globals, ms, supply, aM, ab)
        let b = checkTm(pre.c2, ctx, globals, ms, supply, bM, ab)
        (tmPair(a, b, "_", weaken(bM)), tmSi(aM, "_", weaken(bM)))
      of pkFst:
        let (p, pty) = inferTm(pre.c1, ctx, globals, ms, supply, ab)
        let (dom, _, _) = ensureSi(ms, pre.loc, pty, ctx.len)
        (tmFst(p), dom)
      of pkSnd:
        let (p, pty) = inferTm(pre.c1, ctx, globals, ms, supply, ab)
        let (_, codBdy, _) = ensureSi(ms, pre.loc, pty, ctx.len)
        (tmSnd(p), subst(codBdy, 0, tmFst(p)))
      of pkProj:
        # Issue #37: `e.f` — resolve against the record table via the
        # un-unfolded head of the scrutinee's type.
        let (p, pty) = inferTm(pre.c1, ctx, globals, ms, supply, ab)
        var head = pty
        while head.kind == tApp: head = head.fn
        let rname =
          if head.kind == tR and ms.refNames.hasKey(head.refId):
            ms.refNames[head.refId]
          else: ""
        if rname == "" or not ms.recordFields.hasKey(rname):
          raise elabErr(pre.loc, "projection '." & pre.name &
            "' on non-record type")
        let pname = rname & "." & pre.name
        if pname notin globals:
          raise elabErr(pre.loc, "record '" & rname & "' has no field '" &
            pre.name & "'")
        let ge = globals[pname]
        let (dom, pcodBdy, _, _, _, fpeg) = ensurePi(ms, pre.loc, ge.ty,
                                                    ctx.len, ab)
        discard convElab(ms, supply, pty, dom, pre.loc, ctx, globals,
                         tmC(cStar))
        checkPeg(fpeg, ab, pre.loc)
        (tmApp(ge.tm, p), subst(pcodBdy, 0, p))
      of pkLet:
        let (v, vty) =
          if pre.c1.isNil: inferTm(pre.c2, ctx, globals, ms, supply, ab)
          elif sharesQtyVar(pre.c1, pre.c2):
            # Issue #66/#84: quantity variables in the annotation are solved
            # from the value (shared variable names); infer the value first,
            # then elaborate the annotation. With disjoint variables there
            # is nothing to solve, so keep the normal order.
            let (vi, vtyi) = inferTm(pre.c2, ctx, globals, ms, supply, ab)
            let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar), ab)
            discard convElab(ms, supply, vtyi, aty, pre.loc, ctx, globals, tmC(cStar))
            (vi, aty)
          else:
            let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar), ab)
            (checkTm(pre.c2, ctx, globals, ms, supply, aty, ab), aty)
        let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, vty), globals, ms, supply, ab)
        (tmLet(v, vty, pre.name, b), subst(bty, 0, v))
      of pkAnn:
        if sharesQtyVar(pre.c2, pre.c1):
          # Issue #66/#84: as for pkLet above — infer the term first so
          # quantity variables shared with the ascribed type are solved
          # before it elaborates.
          let (t, tty) = inferTm(pre.c1, ctx, globals, ms, supply, ab)
          let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar), ab)
          # Issue #46: the expected type is the elaboration of pre.c2, so its
          # source location is the expected-type origin for the error message.
          discard convElab(ms, supply, tty, ty, pre.loc, ctx, globals, tmC(cStar), pre.c2.loc)
          (t, ty)
        else:
          let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar), ab)
          (checkTm(pre.c1, ctx, globals, ms, supply, ty, ab), ty)
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
             ms: var MetaStore, supply: var Supply, expTy: Term,
             ab: Ability, expLoc: Loc = noLoc): Term =
  profilePhase(epCheck):
      ## Checking mode against an expected type.
      ## Issue #46: expLoc is the source location where expTy was written,
      ## when known (noLoc = unknown). It is threaded to convElab so a
      ## conversion failure names both program points; recursive calls
      ## propagate it unless a nearer ascription supplies a better origin.
      traceGuard(tcCheck, "check",
                 $pre.kind & " <= " & $expTy.kind &
                 " @" & $pre.loc.line & ":" & $pre.loc.col)
      case pre.kind
      of pkInt:
        # Literal overloading: integer literal adapts to expected type.
        # Try Nat (inductive) first, then primitive Int.
        # Issue #74: a Nat literal's *inferred* type is the singleton
        # tNatSing(n); check-mode subsumption (defaultConv) widens it to
        # Nat on demand, or matches it against a singleton exactly.
        # In type position (expected ?), the literal *is* the singleton
        # type (Scala 3 literal-type style): `def f : (d : 2) -> Nat`.
        # mkNatLit builds the O(1) primitive tNatLit; no manual reification needed.
        block:
          # Debug
          # echo "pkInt in checkTm, intVal=", pre.intVal
          var done = false
          var resTm: Term = nil
          if expTy.kind == tC and expTy.c == cStar and "Nat" in globals:
            if pre.intVal < 0:
              raise elabErr(pre.loc, "negative integer literal in Nat position")
            resTm = tmNatSing(pre.intVal)
            done = true
          if "Nat" in globals and not done:
            try:
              let natTm = mkNatLit(pre.intVal, pre.loc)
              # Issue #74: the literal's inferred type is the singleton
              # tNatSing(n) — except when the expected type still has
              # unsolved metas (infer-mode positions, e.g. pair
              # components checked against fresh metas): there we widen
              # eagerly to Nat, preserving the old behavior and the
              # P2c compositionality contract. Precision applies when
              # the expected type is known.
              let infTy =
                if findUnsolved(ms, zonk(ms, expTy)).found: globals["Nat"].tm
                else: tmNatSing(pre.intVal)
              discard convElab(ms, supply, infTy, expTy, pre.loc, ctx, globals, tmC(cStar), expLoc)
              resTm = natTm
              done = true
            except ElabError as e:
              # Issue #74: keep the Nat-path error: when the expected type
              # is Nat-like (a singleton or Nat itself), the mismatch (e.g.
              # "inferred type 3 does not match expected type 2") is the
              # honest message — the Int fallback below would otherwise
              # claim Nat is missing when it is not.
              if "Int" notin globals:
                raise e
              # else: fall through to the Int attempt; if that also fails
              # its error is raised, otherwise the Nat error is moot.
              try:
                let intTy = globals["Int"].tm
                discard convElab(ms, supply, intTy, expTy, pre.loc, ctx, globals, tmC(cStar), expLoc)
                resTm = tmInt(pre.intVal)
                done = true
              except ElabError:
                raise e
          if not done:
            if "Int" notin globals:
              raise elabErr(pre.loc, "integer literal requires 'postulate Int : ?' or 'data Nat'")
            let intTy = globals["Int"].tm
            discard convElab(ms, supply, intTy, expTy, pre.loc, ctx, globals, tmC(cStar), expLoc)
            resTm = tmInt(pre.intVal)
          resTm
      of pkLam:
        let (dom, codBdy, _, _, piQty, _) = ensurePi(ms, pre.loc, expTy, ctx.len, ab)
        let d =
          if pre.c1.isNil: dom
          else:
            let ad = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar), ab)
            # Issue #88: ascribed domains are checked by conversion, not
            # syntactic unification. unifyElab cannot see through definitions
            # (unifyHead deliberately does no delta-unfolding), so an
            # ascription that is definitionally equal to the expected domain
            # — e.g. a concrete Pi against a motive-computed `mapCont U0 A B`
            # (delta + iota away) — was wrongly rejected with
            # "cannot unify tPi with tApp". convElab compares up to full
            # reduction via the kernel evaluator and falls back to unification
            # while metas remain unsolved, so meta-solving behavior here is
            # unchanged.
            discard convElab(ms, supply, ad, dom, pre.loc, ctx, globals,
                             tmC(cStar), pre.loc)
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
        let b = checkTm(pre.c2, ctx.ext(pre.name, d, bQty), globals, ms, supply, codBdy, ab, expLoc)
        enforceBinderQty(bQty, b, pre.loc, pre.name, ms)  # Issue #66
        # DEBUG
        # echo "DEBUG checkTm pkLam: pre.qty=", pre.qty, " name=", pre.name
        tmLam(d, pre.name, b, pre.impl, pre.erased, zonkQty(ms, bQty), ab)
      of pkPair:
        let h = headTy(ms, expTy)
        if h.kind == tSi:
          let a = checkTm(pre.c1, ctx, globals, ms, supply, h.dom, ab, expLoc)
          let b = checkTm(pre.c2, ctx, globals, ms, supply, subst(h.scope.bdy, 0, a), ab, expLoc)
          tmPair(a, b, h.scope.adv, h.scope.bdy)
        elif h.kind == tMeta:
          let (dom, codBdy, adv) = ensureSi(ms, pre.loc, expTy, ctx.len)
          let a = checkTm(pre.c1, ctx, globals, ms, supply, dom, ab, expLoc)
          let b = checkTm(pre.c2, ctx, globals, ms, supply, subst(codBdy, 0, a), ab, expLoc)
          tmPair(a, b, adv, codBdy)
        else:
          raise elabErr(pre.loc, "pair " & $pre &
            " checked against a non-Sigma type")
      of pkLet:
        if pre.c1.isNil:
          let (v, vty) = inferTm(pre.c2, ctx, globals, ms, supply, ab)
          let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, vty), globals, ms, supply, ab)
          unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
          tmLet(v, vty, pre.name, b)
        elif sharesQtyVar(pre.c1, pre.c2):
          # Issue #66/#84: quantity variables shared with the annotation
          # are solved from the value; infer the value first.
          let (v, vty) = inferTm(pre.c2, ctx, globals, ms, supply, ab)
          let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar), ab)
          discard convElab(ms, supply, vty, aty, pre.loc, ctx, globals, tmC(cStar), pre.c1.loc)
          let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, aty), globals, ms, supply, ab)
          unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
          tmLet(v, aty, pre.name, b)
        else:
          let aty = checkTm(pre.c1, ctx, globals, ms, supply, tmC(cStar), ab)
          let v = checkTm(pre.c2, ctx, globals, ms, supply, aty, ab, pre.c1.loc)
          let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, aty), globals, ms, supply, ab)
          unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
          tmLet(v, aty, pre.name, b)
      of pkAnn:
        if sharesQtyVar(pre.c2, pre.c1):
          # Issue #66/#84: as for pkLet above — infer the term first so
          # quantity variables shared with the ascribed type are solved
          # before it elaborates.
          let (t, tty) = inferTm(pre.c1, ctx, globals, ms, supply, ab)
          let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar), ab)
          # Issue #46: the expected type is the elaboration of pre.c2, so its
          # source location is the expected-type origin for the error message.
          discard convElab(ms, supply, tty, ty, pre.loc, ctx, globals, tmC(cStar), pre.c2.loc)
          unifyElab(ms, ty, expTy, pre.loc)
          t
        else:
          let ty = checkTm(pre.c2, ctx, globals, ms, supply, tmC(cStar), ab)
          let t = checkTm(pre.c1, ctx, globals, ms, supply, ty, ab, pre.c2.loc)
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
          withConvHandler(ms, natArithHandler(globals, supply),
            tacRefl(expTy, ctx, globals, ms, supply, pre.loc))
        else: raise elabErr(pre.loc, "unknown tactic '" & pre.name &
          "'; known tactics: refl, assumption, arith")
      else:
        var (t, ty) = inferTm(pre, ctx, globals, ms, supply, ab)
        # Issue #201: the insertion inferTm's pkVar used to do now lives
        # at the infer-then-convert boundary, so check-mode uses of bare
        # implicits-headed variables keep their old behaviour.
        (t, ty) = insertImplicits(pre, t, ty, ctx.len, ms)
        discard convElab(ms, supply, ty, expTy, pre.loc, ctx, globals, tmC(cStar), expLoc)
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
  let ab = sigAmbient(d, globals, ms)  # Issue #177: ambient ability
  # 1. elaborate the type; it must be a type and contain no metas
  let tyPre = d.desugarTy()
  let tmPre = d.desugarTm()
  # Issue #84: quantity-first elaboration (infer the body, solving shared
  # quantity variables from usage, then elaborate the type) applies only
  # when the type and body share a variable — the proc-telescope case —
  # and the body is inferrable. Otherwise the usual order: elaborate the
  # type, then check the body against it (unannotated binders inherit
  # quantities from the expected type; `by`/literal bodies need checking).
  # (The quantity-first order cannot use checking-only constructs: a `by`
  # tactic body or an integer literal needing Nat from the expected type
  # raises the usual "requires an expected type" error.)
  let qtyFirst = sharesQtyVar(tyPre, tmPre) and not bodyNeedsCheck(tmPre)
  var tmT0: Term
  var tmTy0: Term
  if qtyFirst:
    let inferred = inferTm(tmPre, @[], globals, ms, supply, ab)
    tmT0 = inferred.tm
    # Issue #84: reconcile the inference with the ascribed type before
    # zonking (zonk rebuilds binder nodes, so widening must happen here):
    # solve unshared ascribed quantity variables positionally, widen
    # inferred q0 to an ascribed qOmega, and report explicit-quantity
    # conflicts with the binder named and the usage sites.
    reconcileInferredQty(tyPre, tmPre, tmT0, inferred.ty, ms)
    tmTy0 = zonk(ms, inferred.ty)
  let (tyTm0, tyTy) = inferTm(tyPre, @[], globals, ms, supply, ab)
  ensureIsUniverse(ms, supply, tyTy, d.loc, "the type of '" & d.name & "'")
  let tyT = zonk(ms, tyTm0)
  let ru = findUnsolved(ms, tyT)
  if ru.found and not ms.allowHoles:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the type of '" & d.name & "'" & unsolvedMetaHint())
  let tyV =
    if ru.found:
      # allowHoles (issue #58): the type mentions holes, so the core
      # cannot value it; registration is skipped below and this dummy
      # is never read.
      vStar()
    else:
      # Issue #84: the ascribed type is elaborator output (its nested
      # applications were validated with the directional q0 ≤ ω
      # subsumption), so the well-formedness audit uses the same relation.
      try: check(supply, vStar(), tyT, qtySubsumption = true)
      except ValueError as e:
        raise elabErr(d.loc,
          "ill-formed type of '" & d.name & "': " & sanitizeKernelMsg(e.msg))
  # 2. elaborate the body against the type; zonk; reject leftovers
  if qtyFirst:
    # Issue #46: the expected type is the elaboration of tyPre, so its
    # source location is the expected-type origin for the error message.
    # (Issue #84: inferred/ascribed quantity reconciliation already ran
    # above, before zonking.)
    discard convElab(ms, supply, tmTy0, tyT, d.loc, @[], globals, tmC(cStar), tyPre.loc)
  else:
    # Issue #46: the expected type is the elaboration of tyPre, so its
    # source location is the expected-type origin for the error message.
    tmT0 = checkTm(tmPre, @[], globals, ms, supply, tyT, ab, tyPre.loc)
  let tmT = zonk(ms, tmT0)
  flushDeferredElab(ms, d.loc)  # Issue #56: report stuck pre-unification goals
  let ru2 = findUnsolved(ms, tmT)
  if ru2.found and not ms.allowHoles:
    raise elabErr(ru2.loc, "unsolved metavariable ?m" & $ru2.id &
      " in the definition of '" & d.name & "'" & unsolvedMetaHint())
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
        # Issue #84: as above — the type is elaborator output, so the
        # well-formedness audit uses the subsumption relation.
        try: check(supply, vStar(), tyT, qtySubsumption = true)
        except ValueError as e:
          raise elabErr(d.loc,
            "ill-formed type of '" & d.name & "': " & sanitizeKernelMsg(e.msg))
      let tm = newPostulateRef(supply, tyV)  # Issue #139: register the name
      globals[d.name] = GEntry(tm: tm, ty: tyT, peg: ab)
      ms.refNames[tm.refId] = d.name
    return ElabDef(name: d.name, tyTm: tyT, tmTm: tmT, loc: d.loc)
  # 3. the core verifies the zonked (meta-free) terms — unless a
  # domain handler extended conversion for this definition (see above).
  # Issue #84: the re-check audits the elaborator, so it implements the
  # same inferred-vs-expected relation — including the directional q0 ≤ ω
  # subsumption (an inferred-erased binder is usable where an
  # unrestricted one is expected). Without the flag the elaborator would
  # accept programs the audit then rejects.
  let tmV =
    if ms.extDischarges != extBefore:
      eval(tmT, @[])
    else:
      try: check(supply, tyV, tmT, qtySubsumption = true)
      except ValueError as e:
        raise elabErr(d.loc, "definition '" & d.name &
          "' does not check against its declared type: " & sanitizeKernelMsg(e.msg) &
          "\n  expected: " & $d.desugarTy() &
          "\n  body:     " & $d.desugarTm())
  let dtm = newDefRef(supply, tyV, tmV)  # Issue #139: register the name
  globals[d.name] = GEntry(tm: dtm, ty: tyT, peg: ab)
  ms.refNames[dtm.refId] = d.name
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
  let ab = freshAbMeta(ms)  # Issue #177: signatures freshen one ?aN
  let (tyTm0, tyTy) = inferTm(ty, @[], globals, ms, supply, ab)
  ensureIsUniverse(ms, supply, tyTy, loc, "the type of postulate '" & name & "'")
  let tyT = zonk(ms, tyTm0)
  flushDeferredElab(ms, loc)  # Issue #56: report stuck pre-unification goals
  let ru = findUnsolved(ms, tyT)
  if ru.found and not ms.allowHoles:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the type of '" & name & "'" & unsolvedMetaHint())
  let tyV =
    if ru.found:
      # allowHoles (issue #58): the type mentions holes; the core cannot
      # value it and registration is skipped below — dummy never read.
      vStar()
    else:
      # Issue #84: the postulate's type is elaborator output (nested
      # applications were validated with the directional q0 ≤ ω
      # subsumption), so the well-formedness audit uses the same relation.
      try: check(supply, vStar(), tyT, qtySubsumption = true)
      except ValueError as e:
        raise elabErr(loc, "ill-formed type of '" & name & "': " & sanitizeKernelMsg(e.msg))
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
  globals[name] = GEntry(tm: tm, ty: tyT, isElim: isElim, elimNargs: nargs,
                         peg: ab)
  ms.refNames[tm.refId] = name  # Issue #139: name-resolving pretty-printer

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
  let ab: Ability = nil  # Issue #177: reduction rules are pure (ambient [])
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
  let (rhsTm0, _) = inferTm(rhs, ctx, globals, ms, supply, ab)
  let rhsTm = zonk(ms, rhsTm0)
  flushDeferredElab(ms, loc)  # Issue #56: report stuck pre-unification goals
  let ru = findUnsolved(ms, rhsTm)
  if ru.found and not ms.allowHoles:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the contractum of a red rule" &
      unsolvedMetaHint())
  try:
    attachRedCase(g.tm, cg.tm.refId, rhsTm, nParams)
  except ValueError as e:
    raise elabErr(loc, sanitizeKernelMsg(e.msg))

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
  of pkFst, pkSnd, pkProj: mentionsFam(pre.c1, famName)
  of pkLet: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName) or
             mentionsFam(pre.c3, famName)
  of pkAnn: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  else: false

proc substPreN(t: PreTerm, subs: seq[(string, PreTerm)],
               fresh: var int): PreTerm
proc substPre*(t: PreTerm, name: string, repl: PreTerm,
              fresh: var int): PreTerm
proc substPreSeq(ts: seq[PreTerm], subs: seq[(string, PreTerm)],
                 fresh: var int): seq[PreTerm]

proc checkFamIndices(idxs: seq[PreTerm], famName, ctorName, where: string,
                     loc: Loc) =
  ## Issue #33: the family may not occur inside its own index terms —
  ## neither in a constructor's return-type indices nor in the indices of
  ## a family-headed argument type. An occurrence there is not strictly
  ## positive: it smuggles the family into a term position of its own
  ## defining equation (cf. the domain-position check in splitCtorArg).
  ## Rejected conservatively; a full nested-inductive-through-indices
  ## analysis is left for a follow-up (see decisions.org).
  for idx in idxs:
    if mentionsFam(idx, famName):
      raise elabErr(loc, "constructor '" & ctorName & "': the family '" &
        famName & "' occurs in " & where & " (not strictly positive)")

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
  # Issue #33: the family may not occur inside the indices of a
  # family-headed argument type either (not strictly positive).
  checkFamIndices(spine[1 + nParams .. ^1], famName, ctorName,
                  "an index of argument '" & argName & "'", loc)
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


proc elimNameFor*(dname: string): string =
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
  profilePhase(epData):
      ## Experiment 5: desugar `data` to postulate/elim/red.
      ## Records the SurfDecl in dataInfos for coverage checking (issue #32).
      let loc = d.daloc
      # name clash check for the generated binders
      # Issue #213: the family name itself must be checked too, not just
      # parameters and constructor binders — `data C` collides with the
      # generated motive binder `C` and otherwise fails later with a
      # confusing conversion error far from the real cause.
      if d.dname == "C":
        raise elabErr(loc, "data family may not be named 'C' (reserved for the motive)")
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
        let retIdxs = extractIndices(ctor.retTy, d.dname, d.params.len,
                                     ctor.cloc)
        # Issue #33: reject family occurrences in the return-type indices
        # (not strictly positive; see checkFamIndices).
        checkFamIndices(retIdxs, d.dname, ctor.name,
                        "an index of the return type", ctor.cloc)
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
        supply.natTypeRefId = globals[d.dname].tm.refId
        for ctor in d.ctors:
          let ctm = globals[ctor.name].tm
          if ctm.kind == tR:
            if ctor.name == "zero": supply.natZeroRefId = ctm.refId
            elif ctor.name == "suc": supply.natSucRefId = ctm.refId

proc elabRecordDecl(d: SurfDecl, globals: var Globals, supply: var Supply,
                    ms: var MetaStore) =
  profilePhase(epData):
      ## Issue #37: desugar `record R:` with `| f : T` fields to:
      ##   def R : ? = Sig (f0:T0). ... . 1          (transparent Sigma)
      ##   def mkR (f0:T0) ... : R = (f0, (..., <>)) (positional constructor)
      ##   def R.fi (p : R) : Ti[...] = <accessor>   (named projections)
      ## `e.f` (pkProj) resolves through ms.recordFields at elaboration.
      ## Constructor syntax decision (issue step 3): positional tuple
      ## lifting (`mkPoint x y`); named `(x := ...)` construction is left
      ## for a follow-up if the positional form proves awkward.
      let loc = d.recloc
      let rname = d.rname
      # the iterated Sigma type, right-nested over the unit type
      var sigTy = mkUnitTy(loc)
      for i in countdown(d.fields.high, 0):
        sigTy = mkSigma(d.fields[i].name, d.fields[i].ty, sigTy,
                        d.fields[i].floc)
      discard elabDefDecl(SurfDef(name: rname, tele: @[], retTy: mkUniv(loc),
                                  body: sigTy, loc: loc),
                          globals, supply, ms)
      # positional constructor
      var ctorBody: PreTerm = mkUnitV(loc)
      for i in countdown(d.fields.high, 0):
        ctorBody = mkPair(mkVar(d.fields[i].name, d.fields[i].floc),
                          ctorBody, loc)
      var tele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool,
                           qty: Qty]] = @[]
      for f in d.fields:
        tele.add((f.name, f.ty, false, false, toQty(qOmega)))
      discard elabDefDecl(SurfDef(name: "mk" & rname, tele: tele,
                                  retTy: mkVar(rname, loc), body: ctorBody,
                                  loc: loc),
                          globals, supply, ms)
      # named projections; earlier field types are substituted with their
      # projections of `p` so dependent fields get dependent types.
      # The record is registered before the projections elaborate: a
      # later field's type may itself project an earlier field (`p.n`).
      var pnames: seq[string] = @[]
      for f in d.fields: pnames.add(f.name)
      ms.registerRecord(rname, pnames)
      for i, f in d.fields:
        let pname = rname & "." & f.name
        var retTy = f.ty
        var fresh = 0
        for j in 0 ..< i:
          retTy = substPre(retTy, d.fields[j].name,
                           mkProj(mkVar("p", loc), d.fields[j].name, loc),
                           fresh)
        var acc: PreTerm = mkVar("p", loc)
        for _ in 0 ..< i: acc = mkSnd(acc, loc)
        acc = mkFst(acc, loc)
        let ptele: seq[tuple[name: string, ty: PreTerm, impl: bool,
                              erased: bool, qty: Qty]] =
          @[("p", mkVar(rname, loc), false, false, toQty(qOmega))]
        discard elabDefDecl(SurfDef(name: pname, tele: ptele, retTy: retTy,
                                    body: acc, loc: f.floc),
                            globals, supply, ms)

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
  of pkFst, pkSnd, pkProj:
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
  of pkFst, pkSnd, pkProj:
    allNamesPreAux(t.c1, acc)
  else: discard

proc allNamesPre(t: PreTerm): HashSet[string] =
  result = initHashSet[string]()
  allNamesPreAux(t, result)

proc substPre*(t: PreTerm, name: string, repl: PreTerm,
              fresh: var int): PreTerm =
  ## Capture-avoiding substitution of free variable `name` by `repl`.
  ## Exported for the adequacy property suite (issue #38).
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
  of pkProj:
    mkProj(substPre(t.c1, name, repl, fresh), t.name, t.loc)
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

proc isIhName(nm: string): bool =
  ## Issue #78: generated induction-hypothesis binders are `ih0`, `ih1`,
  ## ... — freshened catch-all binders must avoid that shape.
  if nm.len > 2 and nm[0] == 'i' and nm[1] == 'h':
    for c in nm[2 .. ^1]:
      if c notin {'0' .. '9'}: return false
    return true
  false

proc replaceRecCalls(rhs: PreTerm, fname: string, recVar: string,
                    ihName: string, dropRest: bool = false): PreTerm =
  ## Replace `fname recVar rest...` (recursive call on recVar in the
  ## scrutinee position) with `ihName rest...` (IH application).
  ## When `dropRest` (nested induction hypothesis, whose type is the
  ## stripped tail `Ret` with the rest binders free rather than
  ## `Pi rest. Ret`), the trailing rest arguments are dropped: the IH
  ## variable already has the right type mentioning the enclosing rest
  ## binders. (Limitation: a nested recursive call whose rest arguments
  ## are not exactly the enclosing rest binders is miscompiled; such
  ## programs are rare and this path did not exist before #78.)
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
        if not dropRest:
          for j in 1 ..< spine.len:
            res = mkApp(res, replaceRecCalls(spine[j], fname, recVar, ihName,
                                             dropRest), rhs.loc)
        return res
    # Not a structural recursive call; recurse into children
    result = rhs
    result.c1 = replaceRecCalls(rhs.c1, fname, recVar, ihName, dropRest)
    result.c2 = replaceRecCalls(rhs.c2, fname, recVar, ihName, dropRest)
  of pkLam:
    result = rhs
    result.c2 = replaceRecCalls(rhs.c2, fname, recVar, ihName, dropRest)
    if rhs.c1 != nil:
      result.c1 = replaceRecCalls(rhs.c1, fname, recVar, ihName, dropRest)
  of pkPi:
    result = rhs
    result.c1 = replaceRecCalls(rhs.c1, fname, recVar, ihName, dropRest)
    result.c2 = replaceRecCalls(rhs.c2, fname, recVar, ihName, dropRest)
  of pkPair:
    result = rhs
    result.c1 = replaceRecCalls(rhs.c1, fname, recVar, ihName, dropRest)
    result.c2 = replaceRecCalls(rhs.c2, fname, recVar, ihName, dropRest)
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
    of pkFst, pkSnd, pkProj:
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
# --- Issue #78: clause-matrix compilation (nested patterns) -------------------
# `elabClausesDecl` compiles clause matrices to nested case splits
# (Maranget/Augustsson style): each split node is one eliminator
# application reusing #32's clause-to-eliminator construction; nested
# constructor patterns in argument positions compile to nested splits
# inside method bodies. Multi-column (multi-argument) matching: the
# first column with a constructor pattern is split, so match columns
# (post-scrutinee explicit arguments) split inside the top methods.

type
  MatrixCol = object
    ## One column under match: the scrutinee term plus its data type.
    term: PreTerm
    dataName: string
    isData: bool
    matchCol: bool    # a post-scrutinee explicit-argument column (vs the
                      # scrutinee or a constructor-argument column)
    params: seq[PreTerm]    # actual parameter terms for the eliminator
    idxTerms: seq[PreTerm]  # scrutinee index terms (variables)
    argTy: PreTerm          # the scrutinee's type (for nested columns)
  MatrixRow = object
    ## One clause row: patterns for the active columns (the scrutinee
    ## column first, then one column per post-scrutinee explicit
    ## argument, in telescope order) and the right-hand side.
    pats: seq[PreTerm]
    rhs: PreTerm
    cloc: Loc
    src: int          # index into cd.clauses
    catchVar: string  # catch-all variable replaced by the ctor app ("" if none)
  TailCtx = object
    ## The fixed method tail for one outer constructor: canonical rest
    ## binders, their types, the motive-body type `Pi rest. Ret[...]` (with
    ## this constructor's index refinement applied), and `retTy`, the same
    ## body with the `Pi rest` prefix stripped. The top split's methods bind
    ## the rest binders in their lambda nest (`restBound = false`); nested
    ## splits sit under those binders (`restBound = true`), use `retTy` for
    ## their motive/IH types, and do not re-bind.
    restNames: seq[string]
    restTys: seq[PreTerm]
    tailTy: PreTerm
    retTy: PreTerm
    restBound: bool
  ClauseCtx = ref object
    ## Everything the recursive compiler needs from `elabClausesDecl`.
    cdName: string
    loc: Loc
    dataInfos: Table[string, SurfDecl]
    ctorToData: Table[string, string]
    tele: seq[tuple[name: string, ty: PreTerm, impl: bool]]
    teleNames: HashSet[string]
    sPos: int
    paramSubst: seq[(string, PreTerm)]
    motiveIdxNames: seq[string]
    cBody: PreTerm
    cBodyRet: PreTerm  # cBody with the `Pi rest` prefix stripped
    scrIdxVars: seq[string]
    usedNames: HashSet[string]
    allPatVars: HashSet[string]
    fresh: int
    ihFresh: int
    recPairs: seq[tuple[rv: string, ihn: string, nested: bool]]
      # (pattern var, IH name, nested?) per method. A nested IH has the
      # stripped tail type `Ret` (the rest binders are already bound by an
      # enclosing method), so a recursive call `f v rest...` on it rewrites
      # to just `ihn` (the rest arguments are dropped); a top-level IH has
      # type `Pi rest. Ret` and keeps them.

proc copyPre(t: PreTerm): PreTerm =
  ## Deep copy. PreTerm is a ref object and `replaceRecCalls` mutates in
  ## place, so rows fanning out to several constructors need owned copies.
  if t.isNil: return nil
  PreTerm(loc: t.loc, kind: t.kind, name: t.name, impl: t.impl,
          erased: t.erased, qty: t.qty, intVal: t.intVal,
          c1: copyPre(t.c1), c2: copyPre(t.c2), c3: copyPre(t.c3))

proc copyPres(ts: seq[PreTerm]): seq[PreTerm] =
  result = @[]
  for t in ts: result.add(copyPre(t))

proc patKindOf(pat: PreTerm, ctorToData: Table[string, string]):
    tuple[isCtor: bool, name: string, args: seq[PreTerm]] =
  ## Like patHeadName, but nested constructor heads are classified against
  ## every known datatype (a nested `suc` is a constructor even when the
  ## node being split is over a different datatype). A bare variable
  ## naming a known constructor is a nullary constructor pattern.
  if pat.kind == pkVar:
    if ctorToData.hasKey(pat.name):
      return (true, pat.name, @[])
    return (false, pat.name, @[])
  var h = pat
  var args: seq[PreTerm] = @[]
  while h.kind == pkApp:
    args.add(h.c2)
    h = h.c1
  if h.kind == pkVar and ctorToData.hasKey(h.name):
    var rargs: seq[PreTerm] = @[]
    for i in countdown(args.high, 0): rargs.add(args[i])
    return (true, h.name, rargs)
  (false, "", @[])

proc collectPatVarSeq(pat: PreTerm, ctorToData: Table[string, string],
                      acc: var seq[string]) =
  ## Pattern variable names at every nesting depth (constructor heads are
  ## not variables, even bare nullary ones).
  let (isCtor, _, args) = patKindOf(pat, ctorToData)
  if isCtor:
    for a in args: collectPatVarSeq(a, ctorToData, acc)
  elif pat.kind == pkVar:
    acc.add(pat.name)
  # wildcards and ill-shaped patterns: handled by the coverage check

proc subsumesPat(p, q: PreTerm, ctorToData: Table[string, string]): bool
  ## Does pattern p subsume pattern q (every value matched by q is matched
  ## by p)? A variable/wildcard subsumes anything; a constructor pattern
  ## subsumes the same head with recursively subsuming arguments.

proc subsumesNests(ps, qs: seq[PreTerm],
                   ctorToData: Table[string, string]): bool =
  if ps.len != qs.len: return false
  for k in 0 ..< ps.len:
    if not subsumesPat(ps[k], qs[k], ctorToData): return false
  true

proc subsumesPat(p, q: PreTerm, ctorToData: Table[string, string]): bool =
  let (ip, hp, ap) = patKindOf(p, ctorToData)
  if not ip:
    # A genuine variable/wildcard subsumes anything (a bare pkVar naming
    # a constructor was classified as a constructor above).
    return p.kind == pkVar or p.kind == pkHole
  let (iq, hq, aq) = patKindOf(q, ctorToData)
  iq and hp == hq and subsumesNests(ap, aq, ctorToData)

proc subsumesAll(p: PreTerm, dataInfos: Table[string, SurfDecl],
                 ctorToData: Table[string, string]): bool =
  ## The pattern matches every value of its type: variables/wildcards, or
  ## a constructor pattern whose datatype has exactly this one constructor
  ## (so every value is headed by it) applied to recursively match-all
  ## patterns. (A bare `zero` is *not* match-all for Nat: it misses `suc`.)
  let (isCtor, head, args) = patKindOf(p, ctorToData)
  if not isCtor:
    return p.kind == pkVar or p.kind == pkHole
  let d2 = ctorToData.getOrDefault(head, "")
  if d2 == "" or not dataInfos.hasKey(d2): return false
  if dataInfos[d2].ctors.len != 1: return false
  for a in args:
    if not subsumesAll(a, dataInfos, ctorToData): return false
  true

proc ctorNamesOf(dd: SurfDecl): seq[string] =
  result = @[]
  for c in dd.ctors: result.add(c.name)

proc checkMatrixCoverage(rows: seq[MatrixRow], dd: SurfDecl,
                         dataInfos: Table[string, SurfDecl],
                         ctorToData: Table[string, string], ctxMsg: string,
                         loc: Loc): seq[seq[MatrixRow]] =
  ## Per-constructor row lists (in dd.ctors order) for one split node.
  ## Overlap is by subsumption: a constructor-headed row overlaps iff an
  ## earlier row for the same head subsumes its nested patterns (so
  ## `| (suc zero)` then `| (suc (suc n))` is fine, but `| (suc x)` then
  ## `| (suc zero)` is an overlap). A variable/wildcard row is redundant
  ## iff every constructor is already fully covered. Raises on overlap,
  ## redundancy, missing cases, unknown constructors, bad arities, and
  ## ill-shaped patterns.
  result = newSeq[seq[MatrixRow]](dd.ctors.len)
  let ctorNames = ctorNamesOf(dd)
  var covered = initTable[string, seq[int]]()
  for cn in ctorNames: covered[cn] = @[]
  proc ctorIndex(nm: string): int =
    for i, c in dd.ctors:
      if c.name == nm: return i
    -1
  proc allWildNests(nested: seq[PreTerm]): bool =
    for p in nested:
      if not subsumesAll(p, dataInfos, ctorToData): return false
    true
  for ri, row in rows:
    let (isCtor, headName, nargs) = patKindOf(row.pats[0], ctorToData)
    if isCtor:
      let ci = ctorIndex(headName)
      if ci < 0:
        raise elabErr(row.cloc, "'" & headName & "' is not a constructor of '" &
          dd.dname & "'" & ctxMsg)
      if nargs.len != dd.ctors[ci].tele.len:
        raise elabErr(row.cloc, "constructor '" & headName & "' takes " &
          $dd.ctors[ci].tele.len & " arguments but pattern has " & $nargs.len)
      # Overlap against every earlier row. A constructor-headed earlier row
      # overlaps iff it subsumes this row's nested patterns *and* every
      # other column; a variable/wildcard earlier row overlaps iff it
      # subsumes this row on all columns. (For a single column this is the
      # old per-constructor check.)
      for qj in 0 ..< ri:
        let q = rows[qj]
        let (qIsCtor, qHead, qNargs) = patKindOf(q.pats[0], ctorToData)
        var subsumed = false
        if qIsCtor and qHead == headName:
          subsumed = subsumesNests(qNargs, nargs, ctorToData) and
            subsumesNests(q.pats[1 .. ^1], row.pats[1 .. ^1], ctorToData)
        elif not qIsCtor:
          subsumed = subsumesNests(q.pats, row.pats, ctorToData)
        if subsumed:
          raise elabErr(row.cloc, "overlapping clauses: '" & headName &
            "' already covered by the clause at " & $q.cloc.line & ":" &
            $q.cloc.col & ctxMsg)
      covered[headName].add(ri)
    else:
      if row.pats[0].kind != pkVar and row.pats[0].kind != pkHole:
        raise elabErr(row.cloc, "pattern must be a constructor pattern, a " &
          "variable, or a wildcard `_`" & ctxMsg)
      # A variable/wildcard row is redundant iff every constructor is
      # already covered *for the values this row matches*: a constructor
      # counts as covered when an earlier row covers its head with
      # match-all nested patterns (or is itself a catch-all) and subsumes
      # this row on every other column. Single-column subsumption on the
      # other columns is vacuous, recovering the old check.
      var newCover = 0
      for cn in ctorNames:
        var full = false
        for qj in 0 ..< ri:
          let q = rows[qj]
          let (qIsCtor, qHead, qNargs) = patKindOf(q.pats[0], ctorToData)
          let coversHead = (not qIsCtor) or
            (qHead == cn and allWildNests(qNargs))
          if coversHead and
             subsumesNests(q.pats[1 .. ^1], row.pats[1 .. ^1], ctorToData):
            full = true
            break
        if not full:
          covered[cn].add(ri)
          inc newCover
      if newCover == 0:
        raise elabErr(row.cloc, "redundant clause: every constructor is " &
          "already covered by an earlier clause" & ctxMsg)
  for ci, ctor in dd.ctors:
    if covered[ctor.name].len == 0:
      raise elabErr(loc, "missing case for constructor '" & ctor.name &
        "' of '" & dd.dname & "'" & ctxMsg)
    for qj in covered[ctor.name]:
      result[ci].add(rows[qj])

proc specializeRows(rows: seq[MatrixRow], dd: SurfDecl, ci: int,
                    ctorToData: Table[string, string],
                    loc: Loc): seq[MatrixRow] =
  ## Rows for constructor dd.ctors[ci]: constructor-headed rows contribute
  ## their nested argument patterns; variable/wildcard rows contribute
  ## fresh wildcards and record a catch-all substitution.
  let ctor = dd.ctors[ci]
  for row in rows:
    let (isCtor, headName, nargs) = patKindOf(row.pats[0], ctorToData)
    if isCtor:
      doAssert headName == ctor.name
      doAssert nargs.len == ctor.tele.len  # checked by coverage
      var npats = nargs
      for p in row.pats[1 .. ^1]: npats.add(p)
      result.add(MatrixRow(pats: npats,
                           rhs: copyPre(row.rhs), cloc: row.cloc,
                           src: row.src, catchVar: ""))
    else:
      var npats: seq[PreTerm] = @[]
      for _ in ctor.tele: npats.add(mkHole(loc))
      for p in row.pats[1 .. ^1]: npats.add(p)
      let cv = if row.pats[0].kind == pkVar: row.pats[0].name else: ""
      result.add(MatrixRow(pats: npats,
                           rhs: copyPre(row.rhs), cloc: row.cloc,
                           src: row.src, catchVar: cv))

proc analyzeColType(ctx: ClauseCtx, col: MatrixCol): tuple[params: seq[PreTerm],
    idxTerms: seq[PreTerm]] =
  ## Decompose a nested column's scrutinee type `D params idxs`. Index
  ## terms must be variables (rigid indices under a nested match are
  ## rejected with a clear error rather than miscompiled).
  let dd = ctx.dataInfos[col.dataName]
  let spine = flattenAppSpine(col.argTy)
  let nParams = dd.params.len
  let (indexTele, _) = flattenPiPre(dd.indexTy)
  if spine.len == 0 or spine[0].kind != pkVar or
     spine[0].name != col.dataName or
     spine.len - 1 != nParams + indexTele.len:
    raise elabErr(ctx.loc, "'def' clauses: nested match scrutinee has " &
      "malformed type (expected '" & col.dataName & "' applied to " &
      $nParams & " parameter(s) and " & $indexTele.len & " indice(s))")
  var params: seq[PreTerm] = @[]
  for i in 1 .. nParams: params.add(spine[i])
  var idxTerms: seq[PreTerm] = @[]
  for i in 1 + nParams ..< spine.len:
    if spine[i].kind != pkVar:
      raise elabErr(ctx.loc, "'def' clauses: nested match on '" &
        col.dataName & "' requires variable indices")
    idxTerms.add(spine[i])
  (params, idxTerms)

proc buildNestedMotive(ctx: ClauseCtx, dd: SurfDecl,
                       paramSubstI: seq[(string, PreTerm)],
                       paramsI: seq[PreTerm], tail: TailCtx): PreTerm =
  ## Motive for a nested split: `lam idxs. lam (_ : D params idxs). BODY`.
  ## Nested splits are always under a method that already binds the rest
  ## (`tail.restBound`), so BODY is the stripped `tail.retTy`. The body is
  ## constant in the indices (the outer constructor's index refinement is
  ## already applied), but the eliminator still takes them.
  let (indexTele, _) = flattenPiPre(dd.indexTy)
  var midxNames: seq[string] = @[]
  for i in 0 ..< indexTele.len:
    var nm = "midxn" & $i
    var k = 0
    while nm in ctx.usedNames:
      nm = "midxn" & $i & "_" & $k
      inc k
    ctx.usedNames.incl(nm)
    midxNames.add(nm)
  var scrTy = mkVar(dd.dname, ctx.loc)
  for pt in paramsI: scrTy = mkApp(scrTy, pt, ctx.loc)
  for mn in midxNames: scrTy = mkApp(scrTy, mkVar(mn, ctx.loc), ctx.loc)
  result = mkLam("_motive", scrTy, tail.retTy, ctx.loc)
  # Issue #112: dependent index telescopes substitute old->new in order.
  var idxSubst: seq[(string, PreTerm)] = @[]
  var indexTysSub: seq[PreTerm] = @[]
  for j in 0 ..< indexTele.len:
    indexTysSub.add(substPreN(substPreN(indexTele[j].ty, paramSubstI,
                                        ctx.fresh), idxSubst, ctx.fresh))
    idxSubst.add((indexTele[j].name, mkVar(midxNames[j], ctx.loc)))
  for j in countdown(midxNames.high, 0):
    result = mkLam(midxNames[j], indexTysSub[j], result, ctx.loc)

proc freshIhName(ctx: ClauseCtx, loc: Loc): string =
  ## A globally fresh IH binder name; a user pattern variable with the
  ## generated shape is a hard error (it would be silently misread).
  while true:
    let nm = "ih" & $ctx.ihFresh
    inc ctx.ihFresh
    if nm in ctx.allPatVars:
      raise elabErr(loc, "pattern variable '" & nm &
        "' clashes with a generated induction hypothesis name; " &
        "rename the pattern variable")
    if nm notin ctx.usedNames:
      ctx.usedNames.incl(nm)
      return nm

proc assembleLeaf(ctx: ClauseCtx, cols: seq[MatrixCol], rows: seq[MatrixRow],
                  tail: TailCtx): PreTerm =
  ## No column has a constructor pattern: the first row matches everything
  ## left in this branch (later rows are shadowed here). Substitute variable
  ## patterns by their column terms. The rest arguments are bound by the
  ## enclosing method (see compileBranch), so no binding happens here.
  let row = rows[0]
  var rhs = row.rhs
  for i, col in cols:
    let p = row.pats[i]
    if p.kind == pkVar:
      rhs = substPre(rhs, p.name, col.term, ctx.fresh)
    elif p.kind != pkHole:
      raise elabErr(row.cloc, "'def' clauses: cannot pattern-match on '" &
        $p & "': the argument type is not a data type")
  result = rhs

proc compileMatrixNode(ctx: ClauseCtx, cols: seq[MatrixCol],
                       rows: seq[MatrixRow], tail: TailCtx,
                       ctxMsg: string): PreTerm
  ## Compile one split node: the first column with a constructor pattern
  ## becomes one eliminator application; otherwise assemble the leaf.

proc compileBranch(ctx: ClauseCtx, dd: SurfDecl, ci: int,
                   cols: seq[MatrixCol], rows: seq[MatrixRow], tail: TailCtx,
                   hasTail: bool, ctxMsg: string): PreTerm =
  ## Compile the method(s) for constructor dd.ctors[ci] of the split on
  ## cols[0]. `hasTail=false` only for the top split: then the rest
  ## binders are canonicalized and the tail type computed here; nested
  ## splits inherit the enclosing constructor's tail.
  let ctor = dd.ctors[ci]
  var sub0 = specializeRows(rows, dd, ci, ctx.ctorToData, ctx.loc)
  # Parameter substitution for this data type.
  var paramSubstI: seq[(string, PreTerm)] = @[]
  for i, p in dd.params: paramSubstI.add((p.name, cols[0].params[i]))
  # Canonical constructor-argument binders. Positions where every row
  # agrees on one variable keep the user's name; anything else (nested
  # patterns, wildcards, disagreement) gets a fresh name, with each row's
  # pattern variable substituted accordingly.
  var argNames: seq[string] = @[]
  var chosen = initHashSet[string]()
  for i, te in ctor.tele:
    var agreeName = ""
    var ok = true
    for r in sub0:
      let p = r.pats[i]
      if p.kind == pkVar:
        if agreeName == "": agreeName = p.name
        elif agreeName != p.name: ok = false
      else: ok = false
    var nm: string
    if ok and agreeName != "" and agreeName notin chosen:
      nm = agreeName
    else:
      let base = if te.name.len > 0: te.name else: "carg"
      nm = base
      var k = 0
      while nm in ctx.usedNames or isIhName(nm) or nm in chosen:
        nm = base & "'" & $k
        inc k
      ctx.usedNames.incl(nm)
    chosen.incl(nm)
    argNames.add(nm)
  # Name substitution: constructor tele names := argument binders.
  var nameSubst: seq[(string, PreTerm)] = @[]
  for i, te in ctor.tele:
    nameSubst.add((te.name, mkVar(argNames[i], ctx.loc)))
  # Constructor return indices, with params and tele names substituted.
  var retIdx = substPreSeq(extractIndices(ctor.retTy, dd.dname,
                                          dd.params.len, ctor.cloc),
                           paramSubstI, ctx.fresh)
  retIdx = substPreSeq(retIdx, nameSubst, ctx.fresh)
  # Issue #80: impossible-clause check — the constructor's return indices
  # must be compatible with the scrutinee's indices.
  var bound80 = ctx.teleNames
  for an in argNames: bound80.incl(an)
  for j in 0 ..< min(cols[0].idxTerms.len, retIdx.len):
    let nc = noConfusionConflictPre(retIdx[j], cols[0].idxTerms[j],
                                    ctx.ctorToData, bound80)
    if nc.bad:
      raise elabErr(sub0[0].cloc, "impossible clause for constructor '" &
        ctor.name & "': " & nc.reason & ctxMsg)
  # Constructor argument types with params/names substituted.
  var argTys: seq[PreTerm] = @[]
  for te in ctor.tele:
    argTys.add(substPreN(substPreN(te.ty, paramSubstI, ctx.fresh),
                         nameSubst, ctx.fresh))
  # The tail: computed here for the top split, inherited for nested ones.
  # The rest binders are bound at the method level (see below): nested
  # splits scrutinize the rest binders, so they must be in scope at the
  # split site rather than bound at the leaves.
  var tailOut = tail
  var matchCols: seq[MatrixCol] = @[]
  var idxSubst: seq[(string, PreTerm)] = @[]
  if not hasTail:
    for j, v in ctx.scrIdxVars: idxSubst.add((v, retIdx[j]))
    # Issue #44: method-level rest arguments: every non-scrutinee argument
    # the methods take explicitly — all post-scrutinee args (implicits made
    # explicit, as before) plus explicit pre-scrutinee args (the view
    # desugar's original scrutinee) — in telescope order. For the default
    # scrutinee position this is exactly sPos+1..tele.high.
    var restTis: seq[int] = @[]
    for ti in 0 .. ctx.tele.high:
      if ti == ctx.sPos: continue
      if ti < ctx.sPos and ctx.tele[ti].impl: continue
      restTis.add(ti)
    # Explicit rest positions: the match columns.
    var expTis: seq[int] = @[]
    for ti in restTis:
      if not ctx.tele[ti].impl: expTis.add(ti)
    # Canonical rest binders, freshened against every name in sight. Base
    # name: this constructor's first row's variable pattern for the column
    # when it has one, else the telescope binder name. (Pattern variables
    # are substituted by these binders per row at the leaves, so no eager
    # per-row substitution is needed here.)
    var canonNames: seq[string] = @[]
    for ep_i, ti in expTis:
      let p0 = sub0[0].pats[ctor.tele.len + ep_i]
      var base = if p0.kind == pkVar and p0.name.len > 0: p0.name
                 elif ctx.tele[ti].name.len > 0: ctx.tele[ti].name
                 else: "marg" & $ep_i
      var nm = base
      var k = 0
      while nm in ctx.usedNames or isIhName(nm):
        nm = base & "'" & $k
        inc k
      ctx.usedNames.incl(nm)
      canonNames.add(nm)
    # Rest binders in telescope order (implicits keep their tele names).
    # Telescope names are rewritten to the canonical ones so dependent
    # rest types stay well-scoped.
    var restNames: seq[string] = @[]
    var restTys: seq[PreTerm] = @[]
    var teleToCanon: seq[(string, PreTerm)] = @[]
    var ep_i = 0
    for ti in restTis:
      var bn: string
      if ctx.tele[ti].impl:
        bn = if ctx.tele[ti].name.len > 0: ctx.tele[ti].name else: "x" & $ti
      else:
        bn = canonNames[ep_i]
        inc ep_i
      restNames.add(bn)
      restTys.add(substPreN(substPreN(substPreN(ctx.tele[ti].ty,
                                                ctx.paramSubst, ctx.fresh),
                                     idxSubst, ctx.fresh),
                            teleToCanon, ctx.fresh))
      if ctx.tele[ti].name.len > 0 and ctx.tele[ti].name != bn:
        teleToCanon.add((ctx.tele[ti].name, mkVar(bn, ctx.loc)))
    # Build the match columns (one per explicit rest argument):
    # their terms are the canonical rest binders, bound by this method's
    # lambda nest below, so nested splits on them are well-scoped. The
    # rows' pattern vectors already carry the rest patterns (merged at
    # the top level), aligned with `newCols & matchCols`.
    ep_i = 0
    var ri = 0
    for ti in restTis:
      if not ctx.tele[ti].impl:
        var h = restTys[ri]
        while h.kind == pkApp: h = h.c1
        let isD = h.kind == pkVar and ctx.dataInfos.hasKey(h.name)
        matchCols.add(MatrixCol(term: mkVar(restNames[ri], ctx.loc),
                                dataName: (if isD: h.name else: ""),
                                isData: isD, matchCol: true,
                                argTy: restTys[ri]))
        inc ep_i
      inc ri
    var midxToRet: seq[(string, PreTerm)] = @[]
    for j, mn in ctx.motiveIdxNames: midxToRet.add((mn, retIdx[j]))
    # The tail's Pi binders use canonical rest names, so the motive body
    # gets the tele->canonical rewrite as well.
    tailOut = TailCtx(restNames: restNames, restTys: restTys,
                      tailTy: substPreN(substPreN(ctx.cBody, teleToCanon,
                                                 ctx.fresh),
                                        midxToRet, ctx.fresh),
                      retTy: substPreN(substPreN(ctx.cBodyRet, teleToCanon,
                                                ctx.fresh),
                                       midxToRet, ctx.fresh),
                      restBound: false)
  else:
    # Nested split: the rest binders are bound by the enclosing method's
    # lambda nest, so this method must not re-bind them.
    tailOut.restBound = true
  # Catch-all and pattern-variable substitutions per row.
  var ctorApp = mkVar(ctor.name, ctx.loc)
  for an in argNames: ctorApp = mkApp(ctorApp, mkVar(an, ctx.loc), ctx.loc)
  for r in sub0.mitems:
    if r.catchVar != "":
      r.rhs = substPre(r.rhs, r.catchVar, ctorApp, ctx.fresh)
    for i in 0 ..< ctor.tele.len:
      let p = r.pats[i]
      if p.kind == pkVar and p.name != argNames[i]:
        r.rhs = substPre(r.rhs, p.name, mkVar(argNames[i], ctx.loc),
                         ctx.fresh)
  # Induction hypotheses for recursive arguments (Issue #113: reject
  # higher-order recursive arguments here as before).
  var ihTys = newSeq[PreTerm](ctor.tele.len)
  var ihNames = newSeq[string](ctor.tele.len)
  for ti, te in ctor.tele:
    if mentionsFam(te.ty, dd.dname):
      let (hoTele, _) = splitCtorArg(te.ty, dd.dname, ctor.name, te.name,
                                     dd.params.len, ctor.cloc)
      if hoTele.len > 0:
        raise elabErr(sub0[0].cloc, "constructor '" & ctor.name &
          "' has a higher-order recursive argument '" & te.name &
          "'; clause-style definitions over such datatypes are not yet " &
          "supported (use the '" & elimNameFor(dd.dname) &
          "' eliminator directly)" & ctxMsg)
      let ihN = freshIhName(ctx, sub0[0].cloc)
      var ihTy: PreTerm
      if hasTail:
        # The nested motive is constant in its indices and the rest
        # binders are bound by the enclosing method: the IH type is the
        # stripped inherited tail `Ret` (the nested eliminator applied to
        # this argument computes exactly it).
        ihTy = tailOut.retTy
      else:
        var argIdx = substPreSeq(extractIndices(te.ty, dd.dname,
                                                dd.params.len, ctor.cloc),
                                 paramSubstI, ctx.fresh)
        argIdx = substPreSeq(argIdx, nameSubst, ctx.fresh)
        ihTy = ctx.cBody
        for j, mn in ctx.motiveIdxNames:
          ihTy = substPre(ihTy, mn, argIdx[j], ctx.fresh)
      ihTys[ti] = ihTy
      ihNames[ti] = ihN
      ctx.recPairs.add((rv: argNames[ti], ihn: ihN, nested: hasTail))
  # Columns for the constructor arguments; recurse into nested patterns.
  var newCols: seq[MatrixCol] = @[]
  for i, te in ctor.tele:
    let aty = argTys[i]
    var h = aty
    while h.kind == pkApp: h = h.c1
    var isD = false
    var dn = ""
    if h.kind == pkVar and ctx.dataInfos.hasKey(h.name):
      isD = true
      dn = h.name
    newCols.add(MatrixCol(term: mkVar(argNames[i], ctx.loc), dataName: dn,
                          isData: isD, argTy: aty))
  let restCols = if hasTail: cols[1 .. ^1] else: matchCols
  let inner = compileMatrixNode(ctx, newCols & restCols, sub0, tailOut,
                                ctxMsg & " (under '" & ctor.name & "')")
  # Lambda nest: args, then IHs (in tele order, IH after its var), then
  # the rest binders — unless the rest is already bound by an enclosing
  # split node (`tailOut.restBound`), in which case nested splits see the
  # enclosing binders and use the stripped tail `retTy`. Each mkLam wraps
  # outside the previous, so the rest binders are wrapped first.
  result = inner
  if not tailOut.restBound:
    for ri in countdown(tailOut.restNames.high, 0):
      result = mkLam(tailOut.restNames[ri], tailOut.restTys[ri], result,
                     ctx.loc)
  for ti in countdown(ctor.tele.high, 0):
    if not ihTys[ti].isNil:
      result = mkLam(ihNames[ti], ihTys[ti], result, ctx.loc)
    result = mkLam(argNames[ti], argTys[ti], result, ctx.loc)

proc compileMatrixNode(ctx: ClauseCtx, cols: seq[MatrixCol],
                       rows: seq[MatrixRow], tail: TailCtx,
                       ctxMsg: string): PreTerm =
  ## Compile one split node: the first column with a constructor pattern
  ## becomes one eliminator application; otherwise assemble the leaf.
  var j = -1
  for cji in 0 ..< cols.len:
    for row in rows:
      let (isCtor, headName, _) = patKindOf(row.pats[cji], ctx.ctorToData)
      if isCtor:
        if not cols[cji].isData:
          raise elabErr(row.cloc,
            "'def' clauses: cannot pattern-match on '" & headName &
            "': the argument type is not a data type" & ctxMsg)
        j = cji
        break
    if j >= 0: break
  if j < 0:
    return assembleLeaf(ctx, cols, rows, tail)
  # Swap the split column to the front (patterns move with it).
  var cols2 = cols
  cols2[0] = cols[j]
  cols2[j] = cols[0]
  var rows2 = rows
  if j != 0:
    for r in rows2.mitems:
      let t = r.pats[0]
      r.pats[0] = r.pats[j]
      r.pats[j] = t
  let dd = ctx.dataInfos[cols2[0].dataName]
  # Analyze the column type once for this split.
  let (paramsI, idxTermsI) = analyzeColType(ctx, cols2[0])
  cols2[0].params = paramsI
  cols2[0].idxTerms = idxTermsI
  let perCtor = checkMatrixCoverage(rows2, dd, ctx.dataInfos, ctx.ctorToData,
                                ctxMsg, ctx.loc)
  # The motive: constant in the indices, body is the inherited tail.
  var paramSubstI: seq[(string, PreTerm)] = @[]
  for i, p in dd.params: paramSubstI.add((p.name, paramsI[i]))
  let motive = buildNestedMotive(ctx, dd, paramSubstI, paramsI, tail)
  var methods: seq[PreTerm] = @[]
  for ci, ctor in dd.ctors:
    methods.add(compileBranch(ctx, dd, ci, cols2, perCtor[ci], tail, true,
                              ctxMsg))
  result = mkVar(elimNameFor(dd.dname), ctx.loc)
  for i, p in dd.params:
    if not p.impl:
      result = mkApp(result, paramsI[i], ctx.loc)
  result = mkApp(result, motive, ctx.loc)
  for m in methods: result = mkApp(result, m, ctx.loc)
  for it in idxTermsI: result = mkApp(result, it, ctx.loc)
  result = mkApp(result, cols2[0].term, ctx.loc)



proc compileClausesToSurfDef(cd: ClausesDef, globals: var Globals,
                             supply: var Supply, ms: var MetaStore,
                             dataInfos: var Table[string, SurfDecl],
                             scrutPos: int = -1): SurfDef =
  ## Issue #42: the clause-matrix compilation half of elabClausesDecl:
  ## compile `def name : Ty` + `|` clauses to the eliminator-application
  ## SurfDef, without elaborating or registering it. The caller elaborates
  ## the SurfDef (single: elabDefDecl; mutual: elabMutualDecl's knot-tying
  ## finalization).
  ## Issue #44: `scrutPos` overrides the scrutinee position (a telescope
  ## index; -1 = the first explicit argument, the #32 default). The view
  ## desugar uses it: the covered value sits after the original scrutinee.
  ## Everything is stated in terms of "the scrutinee column vs the rest
  ## columns", so scrutPos = -1 behaves exactly as before.
  profilePhase(epClause):
      let loc = cd.loc
      resetQVars(ms)  # Issue #66: fresh quantity-variable scope per declaration
      # Issue #44: view clauses must go through the view desugar
      # (elabViewClausesDecl), which strips the annotations before calling
      # back here with scrutPos >= 0. A view clause reaching this proc
      # directly (e.g. inside a `mutual` block) is rejected, never silently
      # miscompiled.
      if scrutPos < 0:
        for cl in cd.clauses:
          if cl.viewName != "":
            raise elabErr(cl.cloc, "view clauses ('[" & cl.viewName &
              "]') are not supported in 'mutual' blocks yet (issue #44)")
      # 1. Find the scrutinee's data type from the type signature.
      # (Computed from the telescope below, once sPos is known.)
      # Issue #80: constructor -> datatype map for the impossible-clause check.
      var ctorToData = initTable[string, string]()
      for dn, dd in dataInfos:
        for ctor in dd.ctors: ctorToData[ctor.name] = dn
      # 2. Count explicit Pis in the type to validate clause arity.
      var nExplicit = 0
      var cur = cd.ty
      while cur.kind == pkPi:
        if not cur.impl: inc nExplicit
        cur = cur.c2
      # 3. Build the top-level clause matrix: coverage + overlap over the
      #    scrutinee-pattern column. Issue #78: the scrutinee pattern may be
      #    a constructor pattern (possibly nested), a variable, or a
      #    wildcard `_`. A variable/wildcard covers every constructor not
      #    already covered; a clause covering nothing new is redundant.
      #    Issue #44: the scrutinee column is pats[sExp] (sExp = the
      #    scrutinee's index among explicit patterns); the matrix rows put
      #    it first so the downstream splitting code is unchanged.
      for cl in cd.clauses:
        if cl.pats.len != nExplicit:
          raise elabErr(cl.cloc, "clause has " & $cl.pats.len & " patterns but " &
            "the type has " & $nExplicit & " explicit arguments")
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
      # Find scrutinee position: issue #44's override, else the first
      # explicit argument.
      var sPos = -1
      if scrutPos >= 0:
        if scrutPos >= tele.len:
          raise elabErr(loc, "'def' clauses: scrutinee position " & $scrutPos &
            " out of range")
        if tele[scrutPos].impl:
          raise elabErr(loc, "'def' clauses: the scrutinee cannot be an " &
            "implicit argument")
        sPos = scrutPos
      else:
        for i, b in tele:
          if not b.impl:
            sPos = i
            break
      if sPos < 0:
        raise elabErr(loc, "'def' clauses need at least one explicit argument " &
          "(the scrutinee)")
      # Explicit-argument telescope indices in order; pats[j] is the pattern
      # for expTis[j]. sExp = the scrutinee's index among explicit patterns.
      var expTis: seq[int] = @[]
      for ti in 0 .. tele.high:
        if not tele[ti].impl: expTis.add(ti)
      var sExp = -1
      for j, ti in expTis:
        if ti == sPos: sExp = j
      # 1 (continued). The scrutinee's data type: head of tele[sPos].ty.
      var dnHead = tele[sPos].ty
      while dnHead.kind == pkApp: dnHead = dnHead.c1
      let dataName =
        if dnHead.kind == pkVar and dataInfos.hasKey(dnHead.name): dnHead.name
        else: ""
      if dataName == "":
        raise elabErr(loc, "'def' clauses require the scrutinee argument " &
          "to have a data type; none found in the type signature")
      let dataDecl = dataInfos[dataName]
      let elimName = elimNameFor(dataName)
      if not globals.hasKey(elimName):
        raise elabErr(loc, "eliminator '" & elimName & "' not found for data '" &
          dataName & "'")
      # 3 (continued). Build the top-level clause matrix with the scrutinee
      # column first.
      var topRows: seq[MatrixRow] = @[]
      for si, cl in cd.clauses:
        var rpats: seq[PreTerm] = @[copyPre(cl.pats[sExp])]
        for j, p in cl.pats:
          if j != sExp: rpats.add(copyPre(p))
        topRows.add(MatrixRow(pats: rpats,
                              rhs: copyPre(cl.rhs), cloc: cl.cloc, src: si,
                              catchVar: ""))
      let perCtorTop = checkMatrixCoverage(topRows, dataDecl, dataInfos, ctorToData,
                                      "", loc)
      # Issue #78: per-clause pattern validation. Patterns (scrutinee and
      # rest columns, at any nesting depth) must be constructor patterns,
      # variables, or wildcards; pattern variables must be unique per clause
      # and must not shadow telescope binders (the method body rebinds rest
      # implicits by their tele names, so a colliding pattern variable would
      # be misread).
      var allPatVars = initHashSet[string]()
      for cl in cd.clauses:
        var pvars: seq[string] = @[]
        collectPatVarSeq(cl.pats[sExp], ctorToData, pvars)
        # Issue #32 (kept through the #165 rewrite): a non-scrutinee-column
        # variable pattern may reuse the name of the telescope binder it
        # binds (an identity pattern, e.g. what the LSP case-split
        # generates); it must not shadow any *other* telescope binder.
        # Issue #44: this covers pre-scrutinee columns too (the view
        # desugar's original-scrutinee pattern).
        var identRest = initHashSet[string]()
        for j, ti in expTis:
          if j == sExp: continue
          let rp = cl.pats[j]
          let (rpIsCtor, _, _) = patKindOf(rp, ctorToData)
          if not rpIsCtor and rp.kind != pkVar and rp.kind != pkHole:
            raise elabErr(cl.cloc, "'def' clauses: pattern must be a " &
              "constructor pattern, a variable, or a wildcard `_`")
          collectPatVarSeq(rp, ctorToData, pvars)
          if rp.kind == pkVar and rp.name == tele[ti].name:
            identRest.incl(rp.name)
        var seen = initHashSet[string]()
        for v in pvars:
          if v in seen:
            raise elabErr(cl.cloc, "duplicate pattern variable '" & v & "'")
          seen.incl(v)
          allPatVars.incl(v)
        for v in pvars:
          if v in teleNames and v != tele[sPos].name and v notin identRest:
            raise elabErr(cl.cloc, "pattern variable '" & v &
              "' shadows argument '" & v & "'; rename the pattern variable")
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
      let cBodyRet = copyPre(cBody)  # cBody with the `Pi rest` prefix stripped
      # Issue #44: the motive's trailing Pi abstracts every non-scrutinee
      # argument that the methods take explicitly: all post-scrutinee args
      # (implicits made explicit, as before) plus explicit pre-scrutinee
      # args (the view desugar's original scrutinee). Implicit pre-scrutinee
      # args stay outer binders, as before. Reverse telescope order.
      for ti in countdown(tele.high, 0):
        if ti == sPos: continue
        if ti < sPos and tele[ti].impl: continue
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
      # Build methods, one per constructor (in dataDecl order), via the
      # recursive clause-matrix compiler (issue #78). Nested constructor
      # patterns become nested eliminator applications inside method bodies.
      let ctx = ClauseCtx(
        cdName: cd.name, loc: loc, dataInfos: dataInfos, ctorToData: ctorToData,
        tele: tele, teleNames: teleNames, sPos: sPos, paramSubst: paramSubst,
        motiveIdxNames: motiveIdxNames, cBody: cBody, cBodyRet: cBodyRet,
        scrIdxVars: scrIdxVars,
        usedNames: usedNames, allPatVars: allPatVars, fresh: fresh, ihFresh: 0,
        recPairs: @[])
      let scrutBinder = if tele[sPos].name.len > 0: tele[sPos].name
                        else: "x" & $sPos
      let topCol = MatrixCol(term: mkVar(scrutBinder, loc), dataName: dataName,
                             isData: true, params: paramTerms,
                             idxTerms: scrIdxTerms, argTy: domS)
      var methods: seq[PreTerm] = @[]
      for ci, ctor in dataDecl.ctors:
        ctx.recPairs = @[]
        var body = compileBranch(ctx, dataDecl, ci, @[topCol], perCtorTop[ci],
                                 TailCtx(), false, "")
        # Rewrite structural recursive calls on pattern binders (at any
        # nesting depth) to IH applications.
        for rp in ctx.recPairs:
          body = replaceRecCalls(body, cd.name, rp.rv, rp.ihn, rp.nested)
        # Issue #36: any self-reference surviving IH-rewriting is a
        # non-structural recursive call — reject with a termination error.
        let fc = if perCtorTop[ci].len > 0: perCtorTop[ci][0].cloc else: loc
        checkClauseTermination(body, cd.name, fc)
        methods.add(body)
      # Write back the consumed fresh-name state.
      fresh = ctx.fresh
      usedNames = ctx.usedNames

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
        # Issue #44: every non-scrutinee argument the methods take
        # explicitly (all post-scrutinee args + explicit pre-scrutinee
        # args), in telescope order.
        if i != sPos and (i > sPos or not tele[i].impl):
          restVars.add(bn)
      # scrutinee applied right after the indices, then the rest arguments
      # in telescope order
      # (implicit rest args applied explicitly: the motive tail is all-explicit)
      app = mkApp(app, mkVar(procTele[sPos].name, loc), loc)
      for rv in restVars:
        app = mkApp(app, mkVar(rv, loc), loc)
      # Build the SurfDef and elaborate
      result = SurfDef(name: cd.name, tele: procTele, retTy: retTy, body: app,
                       loc: loc)

proc elabViewClausesDecl(cd: ClausesDef, vi: ViewInfo, globals: var Globals,
                         supply: var Supply, ms: var MetaStore,
                         dataInfos: var Table[string, SurfDecl]): seq[ElabDef] =
  ## Issue #44: elaborate `def f : Ty` whose clauses carry `| x [Fam] pat`
  ## view annotations. The scrutinee is the explicit argument carrying the
  ## `[Fam]` annotation (parameters, if any, precede it). Desugar into two
  ## declarations:
  ##   def f_viewInner : (p1 : P1) -> (x : T) -> (v : Fam x p1..pn) -> R
  ##     (clauses on the covered value v, compiled by #32's machinery with
  ##     the scrutinee at telescope position sPos+1)
  ##     | p1.. x pat = rhs ...
  ##   proc f (p1 : P1) (x : T) : R = f_viewInner p1.. x (cover p1..pn x) rest...
  ## Constructor clauses are the identity-covering special case of this
  ## scheme. Note: recursive calls in rhs go through the wrapper, so #32's
  ## structural termination checking does not transfer through views —
  ## view recursion is currently unchecked (documented limitation).
  let loc = cd.loc
  var piList: seq[tuple[name: string, ty: PreTerm, impl: bool,
                        erased: bool, qty: Qty]] = @[]
  var tcur = cd.ty
  while tcur.kind == pkPi:
    piList.add((tcur.name, tcur.c1, tcur.impl, tcur.erased, tcur.qty))
    tcur = tcur.c2
  let retTy = tcur
  # The scrutinee is the explicit argument carrying the `[Fam]` annotation:
  # its explicit position is the first clause's viewPos (the annotation
  # follows the scrutinee pattern, so viewPos counts only explicit patterns
  # before it). All clauses must annotate the same argument. Parameterized
  # views (#44) put their parameters before the scrutinee.
  var nExplicit = 0
  var explicitIdx: seq[int] = @[]
  for i, b in piList:
    if b.impl: continue
    explicitIdx.add(i)
    inc nExplicit
  if nExplicit == 0:
    raise elabErr(loc, "'def' with view clauses needs an explicit argument")
  let sExp = cd.clauses[0].viewPos
  if sExp < 0 or sExp >= nExplicit:
    raise elabErr(cd.clauses[0].cloc, "the view annotation '[" & vi.vname &
      "]' must follow an explicit argument pattern")
  let sPos = explicitIdx[sExp]
  # Issue #44 (parameterized views): the view's nParams explicit arguments
  # immediately preceding the scrutinee are the view parameters.
  if sExp < vi.nParams:
    raise elabErr(loc, "view '" & vi.vname & "' takes " & $vi.nParams &
      " parameter(s) before the scrutinee, but '" & cd.name &
      "' has only " & $sExp & " explicit argument(s) before it")
  var paramPi: seq[int] = @[]
  for j in 0 ..< vi.nParams:
    paramPi.add(explicitIdx[sExp - vi.nParams + j])
  # Every clause agrees on the view and the annotated position; the
  # annotation sits on the scrutinee.
  for cl in cd.clauses:
    if cl.viewName == "":
      raise elabErr(cl.cloc, "view clauses ('[" & vi.vname &
        "]') cannot be mixed with plain clauses in one 'def'")
    if cl.viewName != vi.vname:
      raise elabErr(cl.cloc, "unknown view '" & cl.viewName &
        "' (expected '[" & vi.vname & "]')")
    if cl.viewPos != sExp:
      raise elabErr(cl.cloc, "the view annotation '[" & cl.viewName &
        "]' must follow the same argument in every clause")
    if cl.pats.len != nExplicit + 1:
      raise elabErr(cl.cloc, "view clause has " & $cl.pats.len &
        " patterns but the type has " & $nExplicit &
        " explicit arguments (plus one view pattern)")
    let xp = cl.pats[cl.viewPos]
    if xp.kind != pkVar and xp.kind != pkHole:
      raise elabErr(cl.cloc, "the pattern before '[" & cl.viewName &
        "]' must be a variable binding the scrutinee")
  # The scrutinee's type must be the view's `over` type (head check).
  var sh = piList[sPos].ty
  while sh.kind == pkApp: sh = sh.c1
  if sh.kind != pkVar or sh.name != vi.scrutHead:
    raise elabErr(loc, "view '" & vi.vname & "' is over '" & vi.scrutHead &
      "' but the scrutinee has a different type head")
  # Freshen unreferenceable binder names ("_" / "") — semantics-preserving,
  # mirroring the clause compiler's own hygiene.
  var used = allNamesPre(cd.ty)
  for cl in cd.clauses:
    for p in cl.pats: used = used + allNamesPre(p)
    used = used + allNamesPre(cl.rhs)
  var scrutName = piList[sPos].name
  if scrutName.len == 0 or scrutName == "_":
    scrutName = "x'view"
    var k = 0
    while scrutName in used:
      scrutName = "x'view" & $k; inc k
  used.incl(scrutName)
  var vName = "v'view"
  var k2 = 0
  while vName in used:
    vName = "v'view" & $k2; inc k2
  used.incl(vName)
  let innerName = cd.name & "_viewInner"
  if globals.hasKey(innerName):
    raise elabErr(loc, "generated name '" & innerName &
      "' clashes with an existing definition")
  # Freshened telescope, shared by the inner def and the wrapper so the
  # wrapper's applications line up with the inner binders.
  var wrapTele: seq[tuple[name: string, ty: PreTerm, impl: bool,
                          erased: bool, qty: Qty]] = @[]
  var seenW = initHashSet[string]()
  var freshW = 0
  for i, e in piList:
    var bn = if i == sPos: scrutName else: e.name
    if bn.len == 0 or bn == "_":
      bn = "_'c" & $freshW
      inc freshW
      while bn in seenW:
        bn = "_'c" & $freshW
        inc freshW
    elif bn in seenW:
      raise elabErr(loc, "'def' with view clauses: duplicate binder name '" &
        bn & "' in the type; rename one of them")
    seenW.incl(bn)
    wrapTele.add((bn, e.ty, e.impl, e.erased, e.qty))
  # Inner type: (tele...) with (v : Fam s p1..pn) inserted after the
  # scrutinee Pi, preserving impl/erased/qty flags. The parameters are
  # already in scope before the scrutinee.
  var famApp: PreTerm = mkVar(vi.vname, loc)
  famApp = mkApp(famApp, mkVar(wrapTele[sPos].name, loc), loc)
  for pj in paramPi:
    famApp = mkApp(famApp, mkVar(wrapTele[pj].name, loc), loc)
  var innerTy = retTy
  for i in countdown(piList.high, 0):
    let e = piList[i]
    if i == sPos:
      # The covered-value binder goes *inside* the scrutinee Pi:
      # (n : Nat) -> (v : Parity n) -> ...
      innerTy = mkPi(vName, famApp, innerTy, loc)
    innerTy = mkPi(wrapTele[i].name, e.ty, innerTy, loc, e.impl, e.erased,
                   e.qty)
  var innerClauses: seq[Clause] = @[]
  for cl in cd.clauses:
    innerClauses.add(Clause(pats: cl.pats, rhs: cl.rhs, cloc: cl.cloc))
  let innerCd = ClausesDef(name: innerName, ty: innerTy,
                           clauses: innerClauses, loc: loc)
  let innerSdef = compileClausesToSurfDef(innerCd, globals, supply, ms,
                                         dataInfos, scrutPos = sPos + 1)
  result.add(elabDefDecl(innerSdef, globals, supply, ms))
  # Wrapper: proc f tele : Ret = f_viewInner x.. (cover p1..pn x_s) rest...
  # (explicit args only; the elaborator inserts metas for implicits).
  var app: PreTerm = mkVar(innerName, loc)
  for i, e in piList:
    if e.impl: continue
    let an = wrapTele[i].name
    app = mkApp(app, mkVar(an, loc), loc)
    if i == sPos:
      var coverApp: PreTerm = mkVar(vi.coverName, loc)
      for pj in paramPi:
        coverApp = mkApp(coverApp, mkVar(wrapTele[pj].name, loc), loc)
      coverApp = mkApp(coverApp, mkVar(an, loc), loc)
      app = mkApp(app, coverApp, loc)
  let wrapSdef = SurfDef(name: cd.name, tele: wrapTele, retTy: retTy,
                         body: app, loc: loc)
  result.add(elabDefDecl(wrapSdef, globals, supply, ms))

proc elabClausesDecl(cd: ClausesDef, globals: var Globals, supply: var Supply,
                     ms: var MetaStore,
                     dataInfos: var Table[string, SurfDecl]): ElabDef =
  ## Single (non-mutual) clause def: compile then elaborate as a plain def.
  let sdef = compileClausesToSurfDef(cd, globals, supply, ms, dataInfos)
  elabDefDecl(sdef, globals, supply, ms)

# --- Issue #42: mutual blocks -------------------------------------------

proc explicitFormalNames(ty: PreTerm): seq[string] =
  ## Explicit formal names of a clause-def type (index 0 = scrutinee).
  var cur = ty
  while cur.kind == pkPi:
    if not cur.impl:
      result.add(cur.name)
    cur = cur.c2

proc strictSubtermVars(pat: PreTerm,
                       ctorToData: Table[string, string]): seq[string] =
  ## Variables bound *strictly inside* a constructor pattern (not the head,
  ## not a bare-variable pattern itself).
  let (isCtor, _, args) = patKindOf(pat, ctorToData)
  if isCtor:
    for a in args:
      var vs: seq[string] = @[]
      collectPatVarSeq(a, ctorToData, vs)
      result.add(vs)

proc sctArcsForCall(args: seq[PreTerm], nTgt: int,
                    ltVars, leVars: seq[seq[string]]): seq[SctArc] =
  ## Size-change arcs for one call: arg i against the caller's formals.
  ## Strict when the argument is a strict subterm of the formal's pattern;
  ## non-strict when it is the formal itself (or a bare-variable alias).
  for i, a in args:
    if i >= nTgt: break  # over-applied: extra args are not formals
    if a.kind != pkVar: continue
    for j in 0 ..< ltVars.len:
      if a.name in ltVars[j]:
        result.add((src: j, strict: true, tgt: i))
      elif a.name in leVars[j]:
        result.add((src: j, strict: false, tgt: i))

proc collectSctCalls(rhs: PreTerm, caller: string, group: HashSet[string],
                     ltVars, leVars: seq[seq[string]],
                     nTgtOf: Table[string, int],
                     bound: seq[string],
                     calls: var seq[SctCall]) =
  ## Walk a clause RHS, recording one SctCall per application headed by a
  ## group member. `bound` tracks shadowing binders (a shadowed head is not
  ## a global call — recording it would add spurious arcs).
  case rhs.kind
  of pkApp:
    var spine: seq[PreTerm] = @[]
    var h = rhs
    while h.kind == pkApp:
      spine.add(h.c2)
      h = h.c1
    if h.kind == pkVar and h.name in group and h.name notin bound:
      var args: seq[PreTerm] = @[]
      for i in countdown(spine.high, 0): args.add(spine[i])
      calls.add(SctCall(caller: caller, callee: h.name,
                      nSrc: ltVars.len, nTgt: nTgtOf[h.name],
                      arcs: sctArcsForCall(args, nTgtOf[h.name], ltVars, leVars),
                      loc: rhs.loc))
    collectSctCalls(h, caller, group, ltVars, leVars, nTgtOf, bound, calls)
    for s in spine:
      collectSctCalls(s, caller, group, ltVars, leVars, nTgtOf, bound, calls)
  of pkLam, pkPi:
    if rhs.c1 != nil:
      collectSctCalls(rhs.c1, caller, group, ltVars, leVars, nTgtOf, bound, calls)
    collectSctCalls(rhs.c2, caller, group, ltVars, leVars, nTgtOf,
                    bound & @[rhs.name], calls)
  of pkSigma, pkPair, pkLet, pkAnn:
    if rhs.c1 != nil:
      collectSctCalls(rhs.c1, caller, group, ltVars, leVars, nTgtOf, bound, calls)
    if rhs.c2 != nil:
      let bound2 = if rhs.kind == pkLet: bound & @[rhs.name] else: bound
      collectSctCalls(rhs.c2, caller, group, ltVars, leVars, nTgtOf, bound2, calls)
    if rhs.c3 != nil:
      collectSctCalls(rhs.c3, caller, group, ltVars, leVars, nTgtOf, bound, calls)
  of pkFst, pkSnd, pkProj:
    collectSctCalls(rhs.c1, caller, group, ltVars, leVars, nTgtOf, bound, calls)
  else:
    discard

proc elabMutualDecl(cds: seq[ClausesDef], blocLoc: Loc, globals: var Globals,
                    supply: var Supply, ms: var MetaStore,
                    dataInfos: var Table[string, SurfDecl]): seq[ElabDef] =
  ## Issue #42: elaborate a `mutual` block of clause-style defs.
  ##
  ## 1. Compile each def's clauses to a SurfDef (pure PreTerm work; also
  ##    validates arity/coverage per def).
  ## 2. Size-change termination check over the group's call sites (fail
  ##    fast: no elaboration is wasted on a non-terminating group).
  ## 3. Forward-declare every name as an opaque R node (postulate-like).
  ## 4. Elaborate each body with all siblings in scope, kernel-check it,
  ##    then *tie the knot*: flip the forward R node into a real definition
  ##    (refIsDefn=true, refVal filled). Sound: bodies were checked with
  ##    siblings opaque (conservative — opacity only removes reductions),
  ##    and clause-def bodies are lambda nests, so filling needs no
  ##    unfolding of siblings.
  ##
  ## Limitation (MVP): a def's *type* may only reference earlier siblings
  ## or globals (forward declarations are sequential); bodies may reference
  ## any sibling.
  for cd in cds:
    if cd.name in globals:
      raise elabErr(cd.loc, "duplicate definition '" & cd.name & "'")
  # 1. compile clauses
  var sdefs: seq[SurfDef] = @[]
  for cd in cds:
    sdefs.add(compileClausesToSurfDef(cd, globals, supply, ms, dataInfos))
  # 2. size-change termination check
  var ctorToData = initTable[string, string]()
  for dn, dd in dataInfos:
    for ctor in dd.ctors: ctorToData[ctor.name] = dn
  var group = initHashSet[string]()
  var nTgtOf = initTable[string, int]()
  var formalNamesOf = initTable[string, seq[string]]()
  for cd in cds:
    group.incl(cd.name)
    let fnames = explicitFormalNames(cd.ty)
    formalNamesOf[cd.name] = fnames
    nTgtOf[cd.name] = fnames.len
  var sctCalls: seq[SctCall] = @[]
  for cd in cds:
    let fnames = formalNamesOf[cd.name]
    for cl in cd.clauses:
      var ltVars, leVars: seq[seq[string]] = @[]
      for j in 0 ..< fnames.len:
        ltVars.add(strictSubtermVars(cl.pats[j], ctorToData))
        var le: seq[string] = @[]
        if fnames[j].len > 0: le.add(fnames[j])
        if cl.pats[j].kind == pkVar and cl.pats[j].name notin le:
          # bare-variable pattern aliases the formal
          le.add(cl.pats[j].name)
        leVars.add(le)
      collectSctCalls(cl.rhs, cd.name, group, ltVars, leVars, nTgtOf, @[],
                      sctCalls)
  try:
    checkSct(sctCalls)
  except SctError as e:
    raise elabErr(e.loc, e.msg)
  # 3. forward declarations (opaque R nodes)
  for sdef in sdefs:
    elabPostulateDecl(sdef.name, sdef.desugarTy(), sdef.loc,
                      globals, supply, ms, false)
  # 4. elaborate bodies; tie the knot
  for sdef in sdefs:
    let extBefore = ms.extDischarges  # Experiment 41: see elabDefDecl
    resetQVars(ms)  # Issue #66: fresh quantity-variable scope per declaration
    let g = globals[sdef.name]
    let tyT = g.ty
    let tyV = g.tm.refTyp
    let ab = g.peg
    let tyPre = sdef.desugarTy()
    let tmPre = sdef.desugarTm()
    # Issue #66: quantity-first order when the type mentions qty vars.
    # The forward type was elaborated type-first; here we mirror
    # elabDefDecl exactly (infer body, re-elaborate type, convert) and
    # update the forward entry — inference quality for qty-var types in
    # mutual blocks is best-effort (documented limitation).
    let qtyFirst = pretermHasQtyVar(tyPre)
    var tmT0: Term
    var tmTy0: Term
    var tyT2 = tyT
    var tyV2 = tyV
    if qtyFirst:
      let inferred = inferTm(tmPre, @[], globals, ms, supply, ab)
      tmT0 = inferred.tm
      tmTy0 = zonk(ms, inferred.ty)
      let (tyTm0, tyTy) = inferTm(tyPre, @[], globals, ms, supply, ab)
      unifyElab(ms, tyTy, tmC(cStar), sdef.loc)
      tyT2 = zonk(ms, tyTm0)
      let ru = findUnsolved(ms, tyT2)
      if ru.found and not ms.allowHoles:
        raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
          " in the type of '" & sdef.name & "'" & unsolvedMetaHint())
      tyV2 =
        if ru.found: vStar()
        else:
          try: check(supply, vStar(), tyT2)
          except ValueError as e:
            raise elabErr(sdef.loc, "ill-formed type of '" & sdef.name &
              "': " & sanitizeKernelMsg(e.msg))
      discard convElab(ms, supply, tmTy0, tyT2, sdef.loc, @[], globals,
                       tmC(cStar), tyPre.loc)
    else:
      tmT0 = checkTm(tmPre, @[], globals, ms, supply, tyT, ab, tyPre.loc)
    let tmT = zonk(ms, tmT0)
    let ru2 = findUnsolved(ms, tmT)
    if ru2.found and not ms.allowHoles:
      raise elabErr(ru2.loc, "unsolved metavariable ?m" & $ru2.id &
        " in the definition of '" & sdef.name & "'" & unsolvedMetaHint())
    if ms.allowHoles and ru2.found:
      # Issue #58: keep the opaque forward declaration; skip the fill.
      result.add(ElabDef(name: sdef.name, tyTm: tyT2, tmTm: tmT, loc: sdef.loc))
      continue
    let tmV =
      if ms.extDischarges != extBefore:
        eval(tmT, @[])
      else:
        try: check(supply, tyV2, tmT)
        except ValueError as e:
          raise elabErr(sdef.loc, "definition '" & sdef.name &
            "' does not check against its declared type: " &
            sanitizeKernelMsg(e.msg))
    # Tie the knot: the forward R node becomes a real definition. All
    # previously elaborated references (same refId) see the filled value.
    let rNode = globals[sdef.name].tm
    rNode.refTyp = tyV2
    rNode.refIsDefn = true
    rNode.refVal = tmV
    globals[sdef.name] = GEntry(tm: rNode, ty: tyT2, peg: ab)
    result.add(ElabDef(name: sdef.name, tyTm: tyT2, tmTm: tmT, loc: sdef.loc))

proc elabInterfaceDecl(name: string, loc: Loc,
                       globals: var Globals, supply: var Supply,
                       ms: var MetaStore) =
  ## Issue #177: `interface Name` — registers an ability interface marker.
  ## Interfaces are not terms; resolveVar rejects them as such.
  if name in globals:
    raise elabErr(loc, "duplicate declaration '" & name & "'")
  globals[name] = GEntry(isIface: true)
  # No refId: interfaces never appear in terms, so refNames skips them.

proc elabCommandDecl(name: string, ty: PreTerm, iface: string, loc: Loc,
                     globals: var Globals, supply: var Supply,
                     ms: var MetaStore) =
  ## Issue #177: `command c : A -> B in I` — declares a command of
  ## interface I. The command is a global operator; the Command rule
  ## (in resolveVar) checks `I` against the ambient at each use and pegs
  ## the operator type at the ambient.
  resetQVars(ms)
  if name in globals:
    raise elabErr(loc, "duplicate declaration '" & name & "'")
  if iface notin globals or not globals[iface].isIface:
    raise elabErr(loc, "unknown interface '" & iface & "'")
  let ab: Ability = nil  # the command's *type* elaborates purely
  let (tyTm0, tyTy) = inferTm(ty, @[], globals, ms, supply, ab)
  ensureIsUniverse(ms, supply, tyTy, loc, "the type of command '" & name & "'")
  let tyT = zonk(ms, tyTm0)
  flushDeferredElab(ms, loc)  # Issue #56: report stuck pre-unification goals
  let ru = findUnsolved(ms, tyT)
  if ru.found and not ms.allowHoles:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the type of command '" & name & "'" & unsolvedMetaHint())
  if headTy(ms, tyT).kind != tPi:
    raise elabErr(loc, "command '" & name & "' must have a function type")
  let tyV =
    # Issue #84: the command's type is elaborator output, so the
    # well-formedness audit uses the subsumption relation.
    try: check(supply, vStar(), tyT, qtySubsumption = true)
    except ValueError as e:
      raise elabErr(loc, "ill-formed type of command '" & name & "': " & sanitizeKernelMsg(e.msg))
  let tm = newPostulateRef(supply, tyV)
  globals[name] = GEntry(tm: tm, ty: tyT, cmdIface: iface)
  ms.refNames[tm.refId] = name

proc elabViewDecl(vd: ViewDecl, globals: var Globals, supply: var Supply,
                  ms: var MetaStore,
                  dataInfos: var Table[string, SurfDecl],
                  viewInfos: var Table[string, ViewInfo]) =
  ## Issue #44 (step 2 of 3): validate and register a `view` declaration.
  ## The covering obligation is checked here, so an ill-typed covering
  ## function is rejected with a located error at the `view` declaration.
  ## The cover type must be
  ##   (p1 : P1) -> ... -> (pn : Pn) -> (s : S) -> Fam s p1..pn
  ## i.e. a Pi prefix of explicit binders whose last binder is the
  ## scrutinee, and whose codomain applies the view family to the scrutinee
  ## first and then the parameter binders in order. (Deeper mismatches,
  ## e.g. the index not mentioning the scrutinee, surface when the
  ## generated wrapper `f x = f_inner x (cover params.. x)` is elaborated.)
  ## Parameterized covers (McBride's BoundCheck) are the nParams > 0 case;
  ## plain covers are nParams = 0.
  if not dataInfos.hasKey(vd.vname):
    raise elabErr(vd.vloc, "'view': '" & vd.vname &
      "' is not a data declaration (the view family must be a `data` type)")
  if not globals.hasKey(vd.coverName):
    raise elabErr(vd.vloc, "'view': covering function '" & vd.coverName &
      "' not found")
  var oh = vd.scrutTy
  while oh.kind == pkApp: oh = oh.c1
  let scrutHead = if oh.kind == pkVar: oh.name else: ""
  if scrutHead == "":
    raise elabErr(vd.vloc, "'view': the 'over' type must have a rigid head " &
      "(e.g. `Nat`, not a computed type)")
  let coverTy = globals[vd.coverName].ty
  var binderAdvs: seq[string] = @[]
  var binderDoms: seq[Term] = @[]
  var ccur = coverTy
  while ccur.kind == tPi:
    if ccur.impl:
      raise elabErr(vd.vloc, "'view': covering function '" & vd.coverName &
        "' must take all its arguments explicitly (parameter '" &
        ccur.scope.adv & "' is implicit)")
    binderAdvs.add(ccur.scope.adv)
    binderDoms.add(ccur.dom)
    ccur = ccur.scope.bdy
  if binderAdvs.len == 0:
    raise elabErr(vd.vloc, "'view': covering function '" & vd.coverName &
      "' must have type (x : T) -> " & vd.vname & " x")
  # The scrutinee binder's domain must have the `over` type's head.
  var dh = binderDoms[^1]
  while dh.kind == tApp: dh = dh.fn
  let dhn = if dh.kind == tR: ms.refNames.getOrDefault(dh.refId, "") else: ""
  if dhn != scrutHead:
    raise elabErr(vd.vloc, "'view': the covering function's scrutinee " &
      "argument does not have the 'over' type '" & scrutHead & "'")
  # The codomain must be `Fam s p1..pn`: head is the view family and the
  # arguments are exactly the binders — the scrutinee (innermost binder,
  # de Bruijn index 0) first, then the parameter binders outermost-first.
  var cargs: seq[Term] = @[]
  var ch = ccur
  while ch.kind == tApp:
    cargs.add(ch.arg)
    ch = ch.fn
  let k = binderAdvs.len
  let hn = if ch.kind == tR: ms.refNames.getOrDefault(ch.refId, "") else: ""
  # cargs collects innermost-first, so the i-th applied argument is
  # cargs[k-1-i]; it must be the binder of de Bruijn index
  # (0 for i = 0, else k-i).
  var shapeOk = hn == vd.vname and cargs.len == k
  if shapeOk:
    for i in 0 ..< k:
      let a = cargs[k - 1 - i]
      let wantIdx = if i == 0: 0 else: k - i
      if a.kind != tV or a.idx != wantIdx:
        shapeOk = false
        break
  if not shapeOk:
    raise elabErr(vd.vloc, "'view': covering function '" & vd.coverName &
      "' must have type (p1 : P1) -> ... -> (s : S) -> " & vd.vname &
      " s p1 ... pn — the view family applied to the scrutinee, then the " &
      "parameters in order (the covering obligation: cover maps each " &
      "scrutinee to its view)")
  viewInfos[vd.vname] = ViewInfo(vname: vd.vname, scrutHead: scrutHead,
                                 coverName: vd.coverName, nParams: k - 1)

proc elabDecl(d: SurfDecl, globals: var Globals, supply: var Supply,
              ms: var MetaStore,
              dataInfos: var Table[string, SurfDecl],
              viewInfos: var Table[string, ViewInfo]): seq[ElabDef] =
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
  of dkRecord:
    elabRecordDecl(d, globals, supply, ms)
  of dkClauses:
    # Issue #44: view-annotated clauses go through the view desugar.
    var vws = initHashSet[string]()
    for cl in d.clausesDef.clauses:
      if cl.viewName != "": vws.incl(cl.viewName)
    if vws.len > 1:
      raise elabErr(d.clausesDef.loc,
        "clauses of one 'def' must use the same view")
    if vws.len == 1:
      let vw = toSeq(vws)[0]
      if not viewInfos.hasKey(vw):
        raise elabErr(d.clausesDef.loc, "unknown view '" & vw &
          "' (no `view " & vw & " over ... with ...` declaration)")
      for ed in elabViewClausesDecl(d.clausesDef, viewInfos[vw], globals,
                                   supply, ms, dataInfos):
        result.add(ed)
    else:
      result.add(elabClausesDecl(d.clausesDef, globals, supply, ms, dataInfos))
  of dkMutual:
    for ed in elabMutualDecl(d.mutualDefs, d.mutualLoc, globals, supply, ms,
                             dataInfos):
      result.add(ed)
  of dkView:
    elabViewDecl(d.viewDecl, globals, supply, ms, dataInfos, viewInfos)
  of dkInterface:
    elabInterfaceDecl(d.ifname, d.ifloc, globals, supply, ms)
  of dkCommand:
    elabCommandDecl(d.cname, d.cty, d.ciface, d.cloc, globals, supply, ms)
  of dkImport:
    # Issue #49: `import` needs a file context (base directory for path
    # resolution); the ModuleDriver below handles it. A bare elabCheck
    # over a source string has no directory to resolve against.
    raise elabErr(d.iloc, "import \"" & d.ipath &
      "\" requires a file context; use elabCheckFile")

proc elabCheckStateG*(src: string, handlers: seq[ConvHandler] = @[]):
    tuple[defs: seq[ElabDef], globals: Globals, ms: MetaStore] =
  profilePhase(epOther):
      ## Issue #62: like elabCheckState, but also returns the elaborator's
      ## global table (name -> GEntry with the tR node and zonked type) so the
      ## independent audit kernel can build its own KernelGlobals over the
      ## same refIds. Raises ParseError (carries loc) or ElabError (carries loc).
      maybeEnableTraceFromEnv()  # Issue #83: EPON_TRACE env var
      let decls = parseProgram(src)
      var globals: Globals = initTable[string, GEntry]()
      var supply = Supply()
      var ms = initMetaStore()  # includes fresh convCache (Experiment 10)
      for h in handlers: ms.convHandlers.add(h)
      var dataInfos: Table[string, SurfDecl] = initTable[string, SurfDecl]()
      var viewInfos: Table[string, ViewInfo] = initTable[string, ViewInfo]()
      var defs: seq[ElabDef] = @[]
      for d in decls:
        let eds = elabDecl(d, globals, supply, ms, dataInfos, viewInfos)
        for ed in eds:
          # Issue #64: verify linear/erased usage in the elaborated term
          try:
            checkUsage(ed.tmTm)
          except UsageError as e:
            raise elabErr(ed.loc, "usage error in '" & ed.name & "': " & e.msg)
          defs.add(ed)
      (defs, globals, ms)

proc elabCheckState*(src: string, handlers: seq[ConvHandler] = @[]):
    tuple[defs: seq[ElabDef], ms: MetaStore] =
  ## Parse, elaborate, and typecheck a surface program, decl by decl,
  ## returning the MetaStore too (for tooling: hole info, issue #58).
  ## Raises ParseError (carries loc) or ElabError (carries loc).
  let st = elabCheckStateG(src, handlers)
  (st.defs, st.ms)

proc elabCheck*(src: string, handlers: seq[ConvHandler] = @[]): seq[ElabDef] =
  ## Parse, elaborate, and typecheck a surface program, decl by decl.
  ## Later decls may mention earlier ones (via closed R nodes).
  ## Raises ParseError (carries loc) or ElabError (carries loc).
  ## Experiment 41: `handlers` installs conversion decision procedures
  ## for the dynamic extent of the whole program (e.g. @[cacheConvHandler]).
  elabCheckState(src, handlers).defs

proc elabCheckHoles*(src: string): tuple[defs: seq[ElabDef], ms: MetaStore,
    errLoc: Loc, errMsg: string] =
  profilePhase(epOther):
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
      var viewInfos: Table[string, ViewInfo] = initTable[string, ViewInfo]()
      var defs: seq[ElabDef] = @[]
      var errLoc = noLoc
      var errMsg = ""
      for d in decls:
        try:
          let eds = elabDecl(d, globals, supply, ms, dataInfos, viewInfos)
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
    viewInfos*: Table[string, ViewInfo]  # Issue #44: registered views
    loading*: seq[string]        # canonical paths on the import stack
    modHash*: Table[string, Hash] # canonical path -> content hash (skip unchanged)
    elabCount*: Table[string, int] # canonical path -> times elaborated
    allDefs*: Table[string, ElabDef]
      ## Issue #62: every definition elaborated through this driver
      ## (including via `import`), by name. Lets consumers (e.g. the
      ## independent audit kernel) recover definition bodies for globals
      ## that `elabFile`'s return value omits as "imported".

proc initModuleDriver*(handlers: seq[ConvHandler] = @[]): ModuleDriver =
  result.ms = initMetaStore()  # includes fresh convCache (Experiment 10)
  for h in handlers: result.ms.convHandlers.add(h)
  result.globals = initTable[string, GEntry]()
  result.dataInfos = initTable[string, SurfDecl]()
  result.allDefs = initTable[string, ElabDef]()

proc elabFile*(drv: var ModuleDriver, path: string,
               importLoc: Loc = noLoc): seq[ElabDef]
  ## Forward: elaborates one file (defined below); elabDeclsDir recurses
  ## through it for nested imports.

proc elabDeclsDirInner(drv: var ModuleDriver, decls: seq[SurfDecl],
                       baseDir: string, srcLabel: string,
                       holeTolerant: bool):
    tuple[defs: seq[ElabDef], errLoc: Loc, errMsg: string] =
  ## Inner driver loop (issues #49/#131/#133). With `holeTolerant=false`
  ## the first ElabError propagates to the caller. With `holeTolerant=true`
  ## (issue #133) decls elaborate one at a time and the loop stops at the
  ## first *non-hole* failure, reporting it via errLoc/errMsg (both empty =
  ## full success) while holes from the successful prefix stay queryable.
  var defs: seq[ElabDef] = @[]
  var errLoc = noLoc
  var errMsg = ""
  for d in decls:
    try:
      if d.kind == dkImport:
        let target = if isAbsolute(d.ipath): d.ipath
                     else: baseDir / d.ipath
        if not fileExists(target):
          raise elabErr(d.iloc, "import \"" & d.ipath & "\": file not found " &
            "(resolved to '" & target & "', imported from '" & srcLabel & "')")
        discard drv.elabFile(target, d.iloc)
      else:
        let eds = elabDecl(d, drv.globals, drv.supply, drv.ms, drv.dataInfos, drv.viewInfos)
        for ed in eds:
          # Issue #64: verify linear/erased usage in the elaborated term
          try:
            checkUsage(ed.tmTm)
          except UsageError as e:
            raise elabErr(ed.loc, "usage error in '" & ed.name & "': " & e.msg)
          defs.add(ed)
          drv.allDefs[ed.name] = ed  # issue #62: log imported defs too
    except ElabError as e:
      if not holeTolerant:
        # Issue #199: explicit `raise e`, NOT bare `raise`. A bare re-raise
        # here segfaults the Nim VM at compile time (exit 139) instead of
        # propagating the exception, turning every user type error inside
        # eponymBlock into a compiler crash.
        raise e
      errLoc = e.loc
      errMsg = e.msg
      break
  (defs, errLoc, errMsg)

proc elabDeclsDir*(drv: var ModuleDriver, decls: seq[SurfDecl],
                   baseDir: string, srcLabel: string): seq[ElabDef] =
  profilePhase(epOther):
    ## Elaborate `decls` into the driver's environment, recursively
    ## elaborating `import` declarations first. Import paths resolve relative
    ## to `baseDir` (the importing source's directory); `srcLabel` names the
    ## importing source in error messages (a file path, or "<eponymBlock>").
    ## Returns the defs declared by `decls` themselves; imported definitions
    ## live in `drv.globals`. Raises ElabError on cycles, missing files, or
    ## elaboration failures.
    maybeEnableTraceFromEnv()  # Issue #83: EPON_TRACE env var
    let (defs, _, errMsg) = drv.elabDeclsDirInner(decls, baseDir, srcLabel, false)
    assert errMsg == "",
      "elabDeclsDirInner(holeTolerant=false) raises instead of reporting"
    defs

proc elabCheckHolesDir*(src: string, baseDir: string,
                        handlers: seq[ConvHandler] = @[]):
    tuple[defs: seq[ElabDef], ms: MetaStore, errLoc: Loc, errMsg: string] =
  ## Issue #133: hole-tolerant elaboration (issue #58 semantics) with
  ## `import` support (issue #131 semantics): `import "path.ep"` resolves
  ## relative to `baseDir`. Used by the shedsBlock macro: each shed becomes
  ## a hole, so the surrounding program must elaborate hole-tolerantly
  ## while still resolving prelude imports. Raises ParseError as usual.
  profilePhase(epOther):
    let decls = parseProgram(src)  # ParseError propagates
    var drv = initModuleDriver(handlers)
    drv.ms.allowHoles = true
    let (defs, errLoc, errMsg) =
      drv.elabDeclsDirInner(decls, baseDir, "<shedsBlock>", true)
    (defs, drv.ms, errLoc, errMsg)

proc elabFile*(drv: var ModuleDriver, path: string,
               importLoc: Loc = noLoc): seq[ElabDef] =
  ## Elaborate the file at `path`, recursively elaborating its `import`
  ## declarations first. Returns the defs declared by this file itself;
  ## imported definitions live in `drv.globals`.
  ## Raises ElabError (located) on import cycles, missing files, parse
  ## errors, or elaboration failures. Files already elaborated with
  ## identical content are skipped via the content-hash cache.
  maybeEnableTraceFromEnv()  # Issue #83: EPON_TRACE env var
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
  var viewInfos: Table[string, ViewInfo] = initTable[string, ViewInfo]()
  for d in decls:
    discard elabDecl(d, globals, supply, ms, dataInfos, viewInfos)
  (globals, ms, supply)

proc checkTermElab*(pre: PreTerm, ctx: Ctx, globals: Globals,
                    ms: var MetaStore, supply: var Supply,
                    expTy: Term, ab: Ability = nil): Term =
  ## Check a single pre-term against an expected type (benchmark hook for
  ## issue #19). Returns the elaborated term; raises ElabError if ill-typed.
  ## Issue #177: ambient ability (default [] = pure).
  checkTm(pre, ctx, globals, ms, supply, expTy, ab)

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

  # --- Issue #33: family occurrences in index positions ---------------------
  # Return-type index mentioning the family (otherwise well-formed).
  expectElabErr("""
proc idPoly33 (A : ?) (x : A) : A = x
data U33 : ? -> ? where
| umk33 (A : ?) (x : U33 A) : U33 (idPoly33 ? (U33 A))
""", "an index of the return type")
  # Family-headed argument type with the family inside an index.
  expectElabErr("""
proc idPoly33b (A : ?) (x : A) : A = x
data T33 : ? -> ? where
| tmk33 (A : ?) (x : T33 (idPoly33b ? (T33 A))) : T33 A
""", "an index of argument 'x'")
  # The acceptance example shape: negative occurrence, located, naming the
  # constructor and the offending argument.
  expectElabErr("""
data Bad33 : ? where
| bad33 (k : (Bad33 -> O) -> Bad33) : Bad33
""", "constructor 'bad33' argument 'k'")
  echo "ok: family occurrences in index positions rejected (#33)"

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
  # Issue #84 refines the rule above: the directional q0 ≤ ω subsumption
  # holds in the inferred-vs-expected check, so an erasing function is
  # usable where an unrestricted one is expected (this is what lets
  # inferred-precise types interoperate with ω-annotated code).
  let qttSubOk = elabCheck("""
postulate N : ?
postulate idN0 : Pi (0 x : N). N
proc subOk : Pi (x : N). N = idN0
""")
  assert qttSubOk.len == 1
  echo "ok: q0 ≤ ω subsumption in conversion (#84)"
  # The reverse direction stays rejected: an unrestricted function is not
  # usable where an erasing one is expected.
  expectElabErr("""
postulate N : ?
postulate idNW : Pi (x : N). N
proc revMismatch : Pi (0 x : N). N = idNW
""", "quantity mismatch")
  echo "ok: Pi conversion rejects mismatched quantities (#66); q0 ≤ ω subsumed (#84)"

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

  # --- Issue #84: quantity-first reconciliation ------------------------
  # Unannotated binders parse to fresh quantity variables; in the
  # quantity-first order the body's inference solves them (0 uses -> q0,
  # otherwise -> qOmega, never q1) and the ascribed type is reconciled
  # against the inference before the generic conversion check.
  # An unshared ascribed quantity variable (unannotated binder written only
  # in the ascribed type) is solved positionally from the inference.
  let q84Pos = elabCheck("""
postulate N : ?
postulate n0 : N
proc p (A : ?) : Pi (x : A). N = lam (x : A). n0
""")
  let pTy = q84Pos[^1].tyTm
  assert pTy.kind == tPi and pTy.scope.bdy.kind == tPi
  assert pTy.scope.bdy.qty == q0
  echo "ok: unshared ascribed quantity variable solved positionally (#84)"
  # Ascribed qOmega never conflicts: `A -> B` desugars to an omega Pi, and
  # an inferred q0 widens to it (no regression vs main, where the body
  # inherited omega in checking mode).
  discard elabCheck("""
postulate N : ?
postulate n0 : N
proc w (A : ?) : N -> N = lam (x : N). n0
""")
  echo "ok: inferred q0 widens to ascribed qOmega (#84)"
  # Plain inference: unused binders infer q0, used binders qOmega.
  let q84Inf = elabCheck("""
postulate N : ?
postulate n0 : N
proc k (A : ?) (x : A) : N = n0
proc u (A : ?) (x : A) : A = x
""")
  let kTy = q84Inf[^2].tyTm
  assert kTy.kind == tPi and kTy.qty == q0
  assert kTy.scope.bdy.kind == tPi and kTy.scope.bdy.qty == q0
  let uTy = q84Inf[^1].tyTm
  assert uTy.kind == tPi and uTy.qty == q0
  assert uTy.scope.bdy.kind == tPi and uTy.scope.bdy.qty == qOmega
  echo "ok: unannotated binders infer 0 when unused, omega otherwise (#84)"
  # An explicit ascribed 0/1 disagreeing with the inference is an error
  # naming the binder and the usage sites that forced the inference.
  expectElabErr("""
postulate N : ?
proc h2 (A : ?) : Pi (0 x : A). A = lam (x : A). x
""", "quantity mismatch for binder 'x'")
  expectElabErr("""
postulate N : ?
proc h2 (A : ?) : Pi (0 x : A). A = lam (x : A). x
""", "the body uses 'x' 1 time(s) at line 2")
  expectElabErr("""
postulate N : ?
postulate n0 : N
proc g2 (A : ?) : Pi (1 x : A). N = lam (x : A). n0
""", "the body never uses 'x', inferring quantity q0")
  expectElabErr("""
postulate N : ?
proc g (A : ?) : Pi (1 x : A). A = lam (x : A). x
""", "quantity 1 is never inferred")
  echo "ok: inferred/ascribed quantity conflicts name binder and use sites (#84)"

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
  # Issue #4: honest cache measurement — report probes/hits/hit-rate so
  # the wall-clock numbers above can be interpreted (a 1.0x with 0 hits
  # and a 1.0x with 90% hits are very different findings).
  let (cachedDefs2, cachedMs) = elabCheckState(vecCorpus, @[cacheConvHandler()])
  assert cachedDefs2.len == cacheDefs.len
  let probes = cachedMs.convCacheProbes
  let hits = cachedMs.convCacheHits
  let hitRate = if probes > 0: 100.0 * hits.float / probes.float else: 0.0
  echo "cache stats: probes=" & $probes & " hits=" & $hits &
    " hit-rate=" & formatFloat(hitRate, ffDecimal, 1) & "%"

  # --- Experiment 41: Nat arithmetic as a scoped decision procedure --
  # `by arith` installs natArithHandler for the dynamic extent of the
  # tactic and the inferred-vs-expected check. It discharges open goals
  # the default conversion cannot: the eliminator is stuck on the
  # neutral first argument, while the handler normalizes linear
  # polynomials.
  # --- Issue #45: natArithHandler returns evidence, extends no trust ----
  # The four synthesized lemmas verify with the bare core at handler
  # construction (no handlers installed — no circularity with `by arith`).
  block:
    var drv = initModuleDriver()
    discard drv.elabDeclsDir(parseProgram("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
"""), ".", "<lemma-test>")
    # NB: use drv.supply, not a fresh Supply(): the core allocates
    # freshPara ids from the supply counter, and a fresh counter restarts
    # at 0, colliding with the global refIds this driver allocated.
    let lem = buildArithLemmas(drv.globals, drv.supply)
    assert lem.ok, "lemma synthesis failed: " & lem.failReason
    echo "ok: arith lemmas synthesize and check with the bare core"
  let (arithDefs, arithMs) = elabCheckState("""
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
  assert arithMs.extDischarges == 0,
    "by arith must not extend trust: evidence discharge leaves extDischarges at 0"
  echo "ok: arith handler discharges open Nat goals with validated evidence"
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

  # --- Issue #45: evidence-returning handlers ---------------------------
  # A mock handler returning `refl`-evidence for one closed goal, built
  # against a ModuleDriver's globals so refIds line up with the elaborated
  # goal. Positive: the evidence validates with the bare core, the
  # definition elaborates, and extDischarges stays 0 (trust not extended —
  # the bare-core re-check in elabDefDecl stays in force). Negative:
  # bogus evidence for a false goal is rejected with a located error.
  let evPrelude = """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
"""
  proc mockEvHandler(g: Globals, bogus: bool, fired: ref bool): ConvHandler =
    ## Fires on one closed goal only (shape-matched by refId):
    ## good mode: `add zero zero === zero` with `refl Nat zero` evidence
    ## (valid: `add zero zero` unfolds definitionally to `zero`);
    ## bogus mode: `zero === suc zero` with `refl Nat zero` evidence
    ## (invalid: the core must reject it).
    let zeroId = g["zero"].tm.refId
    let sucId = g["suc"].tm.refId
    let addId = g["add"].tm.refId
    let natT = g["Nat"].tm
    let reflT = g["refl"].tm
    let zeroT = g["zero"].tm
    let decide: ConvDecide =
      proc(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
           ctxLen: int, goalTy: Term): ConvResult {.closure.} =
        let (ha, aa) = spineOf(a)
        let isAddZeroZero =
          ha.kind == tR and ha.refId == addId and aa.len == 2 and
          aa[0].kind == tR and aa[0].refId == zeroId and
          aa[1].kind == tR and aa[1].refId == zeroId and
          b.kind == tR and b.refId == zeroId
        let isZeroSucZero =
          a.kind == tR and a.refId == zeroId and
          b.kind == tApp and b.fn.kind == tR and b.fn.refId == sucId and
          b.arg.kind == tR and b.arg.refId == zeroId
        if not bogus and isAddZeroZero:
          fired[] = true
          ConvResult(verdict: cvDischargedEv,
                     evidence: tmApp(tmApp(reflT, natT), zeroT))
        elif bogus and isZeroSucZero:
          fired[] = true
          ConvResult(verdict: cvDischargedEv,
                     evidence: tmApp(tmApp(reflT, natT), zeroT))
        else:
          ConvResult(verdict: cvDeclined)
    ConvHandler(decide: decide, coreValid: false)
  var evDrv = initModuleDriver()
  discard evDrv.elabDeclsDir(parseProgram(evPrelude), ".", "<ev-test>")
  var evFired = new(bool)
  evDrv.ms.convHandlers.add(mockEvHandler(evDrv.globals, false, evFired))
  let evDefs = evDrv.elabDeclsDir(parseProgram(
    "proc evOk : Eq Nat (add zero zero) zero =\n  by refl\n"), ".", "<ev-test>")
  assert evDefs.len == 1
  assert evFired[], "mock evidence handler never fired on the positive goal"
  assert evDrv.ms.extDischarges == 0,
    "evidence discharge must not extend trust"
  echo "ok: evidence-returning discharge validated by the bare core"
  var badDrv = initModuleDriver()
  discard badDrv.elabDeclsDir(parseProgram(evPrelude), ".", "<ev-test>")
  var badFired = new(bool)
  badDrv.ms.convHandlers.add(mockEvHandler(badDrv.globals, true, badFired))
  try:
    discard badDrv.elabDeclsDir(parseProgram(
      "proc evBad : Eq Nat zero (suc zero) =\n  by refl\n"), ".", "<ev-test>")
    assert false, "expected ElabError for bogus evidence"
  except ElabError as e:
    assert "evidence rejected" in e.msg, "missing 'evidence rejected' in: " & e.msg
  echo "ok: bogus handler evidence rejected by the core"

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

  # --- Issue #78: catch-all (variable/wildcard) first patterns --------
  # A variable/wildcard first pattern covers every constructor not matched
  # by an earlier clause; a variable pattern stands for the scrutinee.
  let catchAllDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Bool : ? where
| true : Bool
| false : Bool
def isZeroV : Nat -> Bool
| zero = true
| m = false
def constT : Nat -> Bool
| _ = true
def idNat : Nat -> Nat
| x = x
proc t1 : Bool = isZeroV zero
proc t2 : Bool = isZeroV (suc zero)
proc t3 : Nat = idNat (suc zero)
proc t4 : Bool = constT (suc (suc zero))
proc tru : Bool = true
proc fls : Bool = false
proc one : Nat = suc zero
""")
  proc findDef(nm: string): ElabDef =
    for d in catchAllDefs:
      if d.name == nm: return d
    assert false, "missing def " & nm
  let truId = eval(findDef("tru").tmTm, @[]).whnfRefId
  let flsId = eval(findDef("fls").tmTm, @[]).whnfRefId
  assert eval(findDef("t1").tmTm, @[]).whnfRefId == truId,
    "isZeroV zero should reduce to true"
  assert eval(findDef("t2").tmTm, @[]).whnfRefId == flsId,
    "isZeroV (suc zero) should reduce to false"
  assert eval(findDef("t4").tmTm, @[]).whnfRefId == truId,
    "constT (suc (suc zero)) should reduce to true"
  let t3v = eval(findDef("t3").tmTm, @[])
  let onev = eval(findDef("one").tmTm, @[])
  assert t3v.whnfKind == wRef and onev.whnfKind == wRef and
    t3v.whnfRefId == onev.whnfRefId and
    t3v.whnfSpineLen == onev.whnfSpineLen,
    "idNat (suc zero) should reduce to suc zero"
  echo "ok: catch-all first patterns elaborate and compute (issue #78)"
  # A clause after a catch-all covers nothing new
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Bool : ? where
| true : Bool
| false : Bool
def bad : Nat -> Bool
| _ = true
| zero = false
""", "already covered")
  # A catch-all after full coverage is redundant
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Bool : ? where
| true : Bool
| false : Bool
def bad : Nat -> Bool
| zero = true
| (suc n) = false
| _ = true
""", "redundant clause")

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

  # --- Issue #42: mutual termination (size-change) ----------------------
  # Corpus: terminating mutual blocks accepted (and compute), looping ones
  # rejected with a named cycle. Uses the same acc/rej template style.
  let mutStart = cpuTime()
  var mutAccepted = 0
  var mutRejected = 0
  template acc42(name, src: string) =
    try:
      discard elabCheck(src)
      inc mutAccepted
    except ElabError as e:
      assert false, "mutual corpus: " & name & " should be accepted: " & e.msg
  template rej42(name, src: string, frag: string) =
    try:
      discard elabCheck(src)
      assert false, "mutual corpus: " & name & " should be rejected"
    except ElabError as e:
      if frag.len > 0:
        assert frag in e.msg, "mutual corpus: " & name &
          " rejected without naming the cycle: " & e.msg
      inc mutRejected
  let natBoolPre = """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Bool : ? where
| true : Bool
| false : Bool
"""
  acc42("mutual even/odd", natBoolPre & """
mutual
def even : Nat -> Bool
| zero = true
| (suc n) = odd n
def odd : Nat -> Bool
| zero = false
| (suc n) = even n
""")
  acc42("mutual even/odd computes", natBoolPre & """
mutual
def even : Nat -> Bool
| zero = true
| (suc n) = odd n
def odd : Nat -> Bool
| zero = false
| (suc n) = even n
proc four : Nat = suc (suc (suc (suc zero)))
proc testEven : Bool = even four
proc testOdd : Bool = odd four
""")
  # even 4 / odd 4 must evaluate (knot-tying is sound)
  block:
    let st42 = elabCheckState(natBoolPre & """
mutual
def even : Nat -> Bool
| zero = true
| (suc n) = odd n
def odd : Nat -> Bool
| zero = false
| (suc n) = even n
proc testEven : Bool = even (suc (suc (suc (suc zero))))
proc testOdd : Bool = odd (suc (suc (suc (suc zero))))
""")
    var gotEven, gotOdd = ""
    for d in st42.defs:
      if d.name == "testEven" or d.name == "testOdd":
        let v = eval(d.tmTm, @[])
        let nm = if v.whnf.kind == wRef: st42.ms.refNames.getOrDefault(whnfRefId(v), "?")
                 else: $v.whnf.kind
        if d.name == "testEven": gotEven = nm else: gotOdd = nm
    assert gotEven == "true", "even 4 should be true, got " & gotEven
    assert gotOdd == "false", "odd 4 should be false, got " & gotOdd
    inc mutAccepted
  acc42("one direction decreases, other passes through", natBoolPre & """
mutual
def a : Nat -> Bool
| zero = true
| (suc m) = b m
def b : Nat -> Bool
| n = a n
""")
  rej42("non-decreasing ping-pong", natBoolPre & """
mutual
def ping : Nat -> Bool
| zero = true
| (suc n) = pong (suc (suc n))
def pong : Nat -> Bool
| zero = false
| (suc m) = ping (suc (suc m))
""", "ping -> pong -> ping")
  rej42("decrease-then-constant loop (SCT soundness)", natBoolPre & """
mutual
def f : Nat -> Bool
| zero = true
| (suc n) = g n
def g : Nat -> Bool
| zero = false
| (suc m) = f (suc (suc zero))
""", "f -> g -> f")
  rej42("self-loop in mutual block (caught by #36 check)", natBoolPre & """
mutual
def loop : Nat -> Bool
| zero = true
| (suc n) = loop (suc (suc n))
def ok : Nat -> Bool
| zero = true
| (suc k) = ok k
""", "")
  assert mutAccepted >= 4, "need >= 4 accepted, got " & $mutAccepted
  assert mutRejected >= 3, "need >= 3 rejected, got " & $mutRejected
  echo "ok: mutual termination corpus (", mutAccepted, " accepted, ",
    mutRejected, " rejected) in ", formatFloat(cpuTime() - mutStart, ffDecimal, 3), "s"

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

  # --- Issue #37, step 4: record-aware pretty-printing -----------------------
  # An iterated Sigma whose binder names and unit tail match a registered
  # record prints as `R{f: T, ...}`, never as raw `Si` nesting.
  let rstate = elabCheckState("""
postulate Nat : ?
postulate zero : Nat
postulate Vec : Nat -> ? -> ?
record Point:
| x : Nat
| y : Nat
record DepR:
| n : Nat
| v : Vec n Nat
proc asSig : ? =
  Sig (x : Nat). Sig (y : Nat). 1
proc asSigDep : ? =
  Sig (n : Nat). Sig (v : Vec n Nat). 1
proc asSigOther : ? =
  Sig (u : Nat). Sig (v : Nat). 1
""")
  proc findDef(ds: seq[ElabDef], name: string): ElabDef =
    for d in ds:
      if d.name == name: return d
    assert false, "def not found: " & name
  proc prettyRec(t: Term): string =
    prettyTerm(zonk(rstate.ms, t), @[], rstate.ms.refNames,
               rstate.ms.recordFields)
  let pPoint = prettyRec(findDef(rstate.defs, "asSig").tmTm)
  assert pPoint == "Point{x: Nat, y: Nat}", "got: " & pPoint
  echo "ok: record skeleton prints with field names: ", pPoint
  let pDep = prettyRec(findDef(rstate.defs, "asSigDep").tmTm)
  assert pDep == "DepR{n: Nat, v: (Vec n Nat)}", "got: " & pDep
  echo "ok: dependent record fields print with names: ", pDep
  let pOther = prettyRec(findDef(rstate.defs, "asSigOther").tmTm)
  assert pOther.startsWith("Si("), "got: " & pOther
  assert "Point" notin pOther, "got: " & pOther
  echo "ok: non-matching Sigma still prints raw: ", pOther

  # --- Issue #52: level-annotated universes ---------------------------------
  # Surface syntax `Type l`, Pi/Sigma formation levels, and cumulativity.
  # Positive: three level-annotated programs check (a datatype at Type 0,
  # polymorphic identity over Type 0, a Pi whose formation level is
  # computed as the max of the domain/codomain levels). Cumulativity: a
  # `Type 0` is accepted where `Type 1` is expected. Negative: `Type 0`
  # is rejected where `Type 0` is expected (its type is `Type 1`), and a
  # Pi at formation level 1 is rejected against `Type 0`.
  let udefs = elabCheck("""
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
proc polyId (A : Type 0) (x : A) : A =
  x
proc natArr : Type 0 =
  Nat -> Nat
proc typeZero : Type 1 =
  Type 0
proc polyTy : Type 1 =
  Pi (A : Type 0). A -> A
""")
  assert udefs.len == 4  # data desugars to postulates; 4 procs
  echo "ok: #52 level-annotated corpus elaborates (Nat : Type 0, polyId, Pi levels, cumulativity)"
  # The Pi `Pi (A : Type 0). A -> A` really lives at Type 1, not Type 0:
  # its formation level is max(classifier(Type 0) = 1, classifier(A -> A) = 0).
  expectElabErr("proc badPiTy : Type 0 =\n  Pi (A : Type 0). A -> A\n",
    "not convertible")
  echo "ok: #52 Pi formation level enforced (level-1 Pi rejected at Type 0)"
  # `Type 0 : Type 1`, so it is rejected where `Type 0` is expected.
  expectElabErr("proc badSelf : Type 0 =\n  Type 0\n", "not convertible")
  echo "ok: #52 level violation rejected (Type 0 does not check against Type 0)"
  # Anti-cumulativity direction: `Type 1` is not accepted where `Type 0`
  # is expected.
  expectElabErr("proc badDown : Type 0 =\n  Type 1\n", "not convertible")
  echo "ok: #52 cumulativity is directional (Type 1 rejected at Type 0)"
  # `Type` without a level is still an ordinary identifier.
  let uidef = elabCheck("""
postulate Nat : Type 0
postulate zero : Nat
proc Type : Nat =
  zero
""")
  assert uidef.len == 1  # postulates yield no ElabDef; one proc
  echo "ok: #52 `Type` alone remains a plain identifier (contextual keyword)"
  # Legacy `?` programs are unaffected: `?`-classified Pis stay level-0
  # definitionally (the `?`/Type-0 bridge) and keep elaborating.
  let ulegacy = elabCheck("""
proc legacyId (A : ?) (x : A) : A =
  x
""")
  assert ulegacy.len == 1
  echo "ok: #52 legacy `?` programs unaffected"

  echo "--- all elaborator tests passed ---"
