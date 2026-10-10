# unify.nim -- Experiment 3: metavariables + Miller pattern unification.
#
# Metavariables live in the core Term as tMeta(id, spine) (see ett_init.nim):
# every occurrence carries a spine with one entry per creation-context
# variable (innermost-first). The elaborator maintains the invariant that an
# occurrence's context has the same length as the creation context; the
# spine is usually the (possibly shifted) identity.
#
# unify implements the pattern fragment (Miller, McBride/Norell style):
#   ?m[sp] =?= t   -- sp must be distinct bound vars; occurs check; solve by
#                     inverting the spine (a permutation) and renaming t back
#                     into the creation context.
# Rigid-rigid cases recurse structurally (de Bruijn: V0 = V0 under binders
# needs no freshening); lambda vs neutral uses eta-expansion. Solved metas
# are followed by zonkHead; zonk substitutes all solutions at the end of
# elaboration, before the core's check/infer ever sees the term.
#
# Precondition (upheld by the elaborator): unified terms have the same type
# up to metas. UnifyError carries a source location for ElabError.

import tables
import sets
import sequtils
import preterm   # Loc
import ett_init
import egraph

type
  UnifyError* = object of CatchableError

  # Experiment 41: equality-as-effect handler interface.
  #
  # A conversion handler discharges one conversion goal `a === b` (both
  # already zonked by convElab). It returns cvDischarged if it proves the
  # goal, or cvDeclined if it cannot decide it — the driver then tries the
  # next handler down the stack; the bottom of the stack is the default
  # handler (full conversion via the core evaluator + areEqual), which
  # raises ElabError on failure exactly as before. Handlers never raise
  # for goals they merely cannot decide; they decline.
  #
  # Handlers are dynamically scoped: they apply only within the dynamic
  # extent of their installation (see withConvHandler in elab.nim).
  # Because Nim closures cannot capture `var` parameters, ms/s travel as
  # explicit arguments rather than through a `next` closure.
  # `coreValid`: true when the handler's discharges are always validated
  # by the core's own conversion (e.g. the cache, which only replays
  # goals the default handler already proved). A handler with
  # coreValid=false (e.g. a domain decision procedure) extends what
  # counts as convertible for its dynamic extent — installing it is an
  # explicit, scoped trust extension, à la Andromeda.
  ConvVerdict* = enum
    cvDischarged
    cvDeclined
  ConvDecide* = proc(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
                     ctxLen: int): ConvVerdict {.closure.}
  ConvHandler* = object
    decide*: ConvDecide
    coreValid*: bool

  MetaEntry* = object
    metaTy*: Term     # type of the meta, in creation context
    metaCtxLen*: int  # length of the creation context
    metaLoc*: Loc     # where the meta was created (for error messages)
    solution*: Term   # nil = unsolved; lives in the creation context

  MetaStore* = object
    nextId*: int
    entries*: Table[int, MetaEntry]
    convCache*: EGraph  # Experiment 10: conversion cache (per elabCheck)
    convHandlers*: seq[ConvHandler]  # Experiment 41: handler stack (top = last)
    extDischarges*: int  # Experiment 41: discharges by coreValid=false handlers
    # Issue #66: quantity variables. Declaration-scoped: the elaborator
    # resets all three at the start of each top-level declaration.
    qvarNames*: Table[string, int]  # variable name -> solution index
    qvarSols*: seq[QtySol]          # per-variable solution
    # Issue #66: pending erased-arg obligations. checkErasedArg records
    # (qty-var name -> app sites) when the argument mentions a variable
    # whose quantity variable is still unsolved; enforceBinderQty flushes
    # the entry when the variable is solved (a q1 solution rejects).
    qvarPending*: Table[string, seq[tuple[varName: string, loc: Loc]]]
    ctorTable*: CtorTable  # Issue #80: constructor disjointness facts

  QtySolKind* = enum qsUnknown, qsSolved
  QtySol* = object
    ## Solution state of one quantity variable.
    case kind*: QtySolKind
    of qsUnknown: discard
    of qsSolved: q*: Quantity

  # Issue #80: constructor disjointness facts (noConfusion/noCycle).
  #
  # For every `data` declaration, elabDataDecl registers the datatype's
  # constructors here: constructor refId -> datatype refId, datatype
  # refId -> constructor refIds (declaration order), plus surface names
  # for error messages. Unification consults the table in its
  # rigid-rigid cases: distinct constructors of the same datatype fail
  # fast with a *named* noConfusion reason instead of a generic
  # "neutral mismatch" / "cannot unify tR with tApp"; the occurs check
  # names noCycle when the offending term is constructor-headed.
  # `constructorForbidEdges` exposes the same facts as forbid-edges for
  # disequality-graph consumers (issue #68, Experiment 10 die-graph).
  CtorTable* = object
    ctorData*: Table[int, int]       # constructor refId -> datatype refId
    dataCtors*: Table[int, seq[int]] # datatype refId -> constructor refIds
    ctorNames*: Table[int, string]   # constructor refId -> surface name
    dataNames*: Table[int, string]   # datatype refId -> surface name

proc initCtorTable*(): CtorTable =
  CtorTable(ctorData: initTable[int, int](),
            dataCtors: initTable[int, seq[int]](),
            ctorNames: initTable[int, string](),
            dataNames: initTable[int, string]())

proc registerDataCtors*(ms: var MetaStore, dataRefId: int, dataName: string,
                        ctors: seq[(int, string)]) =
  ## Issue #80: record one `data` declaration's constructor set.
  ms.ctorTable.dataNames[dataRefId] = dataName
  var ids: seq[int] = @[]
  for (cid, cname) in ctors:
    ms.ctorTable.ctorData[cid] = dataRefId
    ms.ctorTable.ctorNames[cid] = cname
    ids.add(cid)
  ms.ctorTable.dataCtors[dataRefId] = ids

proc ctorHeadOf*(ms: MetaStore, t: Term): int =
  ## The constructor refId at the head of t's application spine, or -1
  ## when the head is not a registered data constructor.
  var cur = t
  while cur.kind == tApp: cur = cur.fn
  if cur.kind == tR and cur.refId in ms.ctorTable.ctorData: cur.refId
  else: -1

proc isConstructor*(ms: MetaStore, refId: int): bool =
  refId in ms.ctorTable.ctorData

proc sameDatatypeCtors*(ms: MetaStore, c1, c2: int): bool =
  ## Both are registered constructors of one datatype.
  c1 in ms.ctorTable.ctorData and c2 in ms.ctorTable.ctorData and
    ms.ctorTable.ctorData[c1] == ms.ctorTable.ctorData[c2]

proc noConfusionMsg*(ms: MetaStore, c1, c2: int): string =
  let n1 = ms.ctorTable.ctorNames[c1]
  let n2 = ms.ctorTable.ctorNames[c2]
  let dn = ms.ctorTable.dataNames[ms.ctorTable.ctorData[c1]]
  "noConfusion: distinct constructors '" & n1 & "' and '" & n2 &
    "' of datatype '" & dn & "' cannot be equal"

proc constructorForbidEdges*(ms: MetaStore): seq[(int, int)] =
  ## Issue #80: the disjointness facts as forbid-edges between
  ## constructor refIds — one unordered pair per two distinct
  ## constructors of the same datatype. For disequality-graph
  ## consumers (issue #68): these pairs can never become equal, so a
  ## conversion cache / e-graph can treat an attempt to equate them as
  ## an immediate contradiction (the `conflict` transition), without
  ## unfolding.
  for dataId, cids in ms.ctorTable.dataCtors:
    for i in 0 ..< cids.len:
      for j in i+1 ..< cids.len:
        result.add((cids[i], cids[j]))

proc initMetaStore*(): MetaStore =
  MetaStore(nextId: 0, entries: initTable[int, MetaEntry](),
            convCache: initEGraph(), convHandlers: @[], extDischarges: 0,
            qvarNames: initTable[string, int](), qvarSols: @[],
            qvarPending: initTable[string, seq[tuple[varName: string, loc: Loc]]](),
            ctorTable: initCtorTable())

proc uerr(loc: Loc, msg: string): ref UnifyError =
  # No location prefix here: the elaborator catches UnifyError and re-raises
  # as ElabError, which adds the source location exactly once.
  newException(UnifyError, msg)

proc freshMeta*(ms: var MetaStore, ty: Term, ctxLen, extra: int,
                loc: Loc): Term =
  ## Create ?m : ty (ty in a context of length ctxLen). The occurrence is
  ## under `extra` additional binders, so the spine is the shifted identity.
  inc ms.nextId
  let id = ms.nextId
  var spine = newSeq[Term](ctxLen)
  for i in 0 ..< ctxLen: spine[i] = vv(i + extra)
  ms.entries[id] = MetaEntry(metaTy: ty, metaCtxLen: ctxLen, metaLoc: loc,
                             solution: nil)
  tmMeta(id, spine)

proc isSolved*(ms: MetaStore, id: int): bool =
  id in ms.entries and not ms.entries[id].solution.isNil

proc zonkHead*(ms: MetaStore, t: Term): Term =
  ## Follow solved metas at the head only.
  var cur = t
  while cur.kind == tMeta:
    if cur.metaId notin ms.entries: break
    let e = ms.entries[cur.metaId]
    if e.solution.isNil: break
    cur = substSpine(e.solution, cur.metaSpine)
  cur

proc unifyHead*(ms: MetaStore, t: Term): Term =
  ## Head-normalize for unification: unfold solved metas (at the head
  ## and in function position) and beta-reduce. No delta-unfolding of
  ## definitions — rigid heads stay rigid. (Experiment 4: eliminator
  ## motives are lambdas, so `C true` with `C = lam u. Bool` must
  ## head-reduce before the rigid-rigid comparison.)
  var cur = zonkHead(ms, t)
  while true:
    if cur.kind != tApp: return cur
    let f = unifyHead(ms, cur.fn)
    if f.kind == tLam:
      cur = zonkHead(ms, subst(f.scope.bdy, 0, cur.arg))
    else:
      return tmApp(f, cur.arg)

# --- Issue #80: rigid noConfusion conflict ------------------------------------
# Placed after unifyHead (used for head-normalization below).

proc noConfusionConflict*(ms: MetaStore, a, b: Term): tuple[bad: bool,
    c1, c2: int]

proc rigidHead(t: Term): bool =
  ## A head that never unfolds under the core evaluator (ett_init.nim:
  ## only tR with refIsDefn unfolds): constructor / type-former / axiom
  ## postulates, bound variables, and core constants. Descent through
  ## such heads is sound; descent through definitions is not (e.g. a
  ## defined `f` could map distinct arguments to equal values).
  case t.kind
  of tR: not t.refIsDefn
  of tV, tC, tInt, tNatLit: true
  else: false

proc sameRigidHead(a, b: Term): bool =
  ## Same head after spine-stripping, where both heads are rigid.
  var fa = a
  while fa.kind == tApp: fa = fa.fn
  var fb = b
  while fb.kind == tApp: fb = fb.fn
  if not rigidHead(fa) or not rigidHead(fb): return false
  if fa.kind != fb.kind: return false
  case fa.kind
  of tR: fa.refId == fb.refId
  of tV: fa.idx == fb.idx
  of tC: fa.c == fb.c
  of tInt: fa.intVal == fb.intVal
  of tNatLit: fa.natLitVal == fb.natLitVal
  else: false

proc argsConflict(ms: MetaStore, a, b: Term): tuple[bad: bool, c1, c2: int] =
  var aa: seq[Term] = @[]
  var ca = a
  while ca.kind == tApp: aa.add(ca.arg); ca = ca.fn
  var bb: seq[Term] = @[]
  var cb = b
  while cb.kind == tApp: bb.add(cb.arg); cb = cb.fn
  if aa.len != bb.len: return (false, -1, -1)
  for i in 0 ..< aa.len:
    let r = noConfusionConflict(ms, aa[i], bb[i])
    if r.bad: return r
  (false, -1, -1)

proc noConfusionConflict*(ms: MetaStore, a, b: Term): tuple[bad: bool,
    c1, c2: int] =
  ## Issue #80: rigid noConfusion conflict between two terms. Both sides
  ## are head-normalized here (beta + zonk; no delta-unfolding). Returns
  ## the offending constructor pair when rigid-rigid comparison forces
  ## distinct constructors of one datatype at some position, descending
  ## through matching rigid heads (injectivity). Conservative: any
  ## flexible, reducible, or mismatched position counts as compatible —
  ## a `bad` result is positive evidence of inequality.
  let a1 = unifyHead(ms, a)
  let b1 = unifyHead(ms, b)
  let ha = ctorHeadOf(ms, a1)
  let hb = ctorHeadOf(ms, b1)
  if ha >= 0 and hb >= 0:
    if ha == hb: return argsConflict(ms, a1, b1)
    if sameDatatypeCtors(ms, ha, hb): return (true, ha, hb)
    return (false, -1, -1)
  if sameRigidHead(a1, b1): return argsConflict(ms, a1, b1)
  (false, -1, -1)

proc zonk*(ms: MetaStore, t: Term): Term =
  ## Substitute every solved metavariable, recursively.
  if t.isNil: return nil
  case t.kind
  of tMeta:
    if t.metaId notin ms.entries: return t
    let e = ms.entries[t.metaId]
    let sp = t.metaSpine.mapIt(zonk(ms, it))
    if e.solution.isNil: tmMeta(t.metaId, sp)
    else: zonk(ms, substSpine(e.solution, sp))
  of tV, tR, tC, tInt, tPrim, tNatLit: t
  of tPi, tSi, tLam:
    mkBinder(t.kind, zonk(ms, t.dom),
              Scope(adv: t.scope.adv, bdy: zonk(ms, t.scope.bdy)), t.impl, t.qty)
  of tPair:
    tmPair(zonk(ms, t.pFst), zonk(ms, t.pSnd),
           t.pScope.adv, zonk(ms, t.pScope.bdy))
  of tApp: tmApp(zonk(ms, t.fn), zonk(ms, t.arg))
  of tFst: tmFst(zonk(ms, t.sub))
  of tSnd: tmSnd(zonk(ms, t.sub))
  of tAbsurd: tmAbsurd(zonk(ms, t.sub))
  of tLet:
    tmLet(zonk(ms, t.letVal), zonk(ms, t.letTy),
          t.letScope.adv, zonk(ms, t.letScope.bdy))

proc findUnsolved*(ms: MetaStore, t: Term): tuple[found: bool, id: int, loc: Loc] =
  ## First unsolved metavariable in t (after zonking), if any.
  case t.kind
  of tMeta:
    if t.metaId in ms.entries:
      let e = ms.entries[t.metaId]
      if e.solution.isNil: return (true, t.metaId, e.metaLoc)
      return findUnsolved(ms, substSpine(e.solution, t.metaSpine))
    for s in t.metaSpine:
      let r = findUnsolved(ms, s)
      if r.found: return r
    (false, 0, noLoc)
  of tV, tR, tC, tInt, tPrim, tNatLit: (false, 0, noLoc)
  of tPi, tSi, tLam:
    let r = findUnsolved(ms, t.dom)
    if r.found: r else: findUnsolved(ms, t.scope.bdy)
  of tPair:
    let r = findUnsolved(ms, t.pFst)
    if r.found: r
    else:
      let r2 = findUnsolved(ms, t.pSnd)
      if r2.found: r2 else: findUnsolved(ms, t.pScope.bdy)
  of tApp:
    let r = findUnsolved(ms, t.fn)
    if r.found: r else: findUnsolved(ms, t.arg)
  of tFst, tSnd, tAbsurd:
    findUnsolved(ms, t.sub)
  of tLet:
    let r = findUnsolved(ms, t.letVal)
    if r.found: r
    else:
      let r2 = findUnsolved(ms, t.letTy)
      if r2.found: r2 else: findUnsolved(ms, t.letScope.bdy)

# --- pattern fragment ---------------------------------------------------------

proc occursSyn(id: int, t: Term): bool =
  case t.kind
  of tMeta:
    if t.metaId == id: return true
    t.metaSpine.anyIt(occursSyn(id, it))
  of tV, tR, tC, tInt, tPrim, tNatLit: false
  of tPi, tSi, tLam:
    occursSyn(id, t.dom) or occursSyn(id, t.scope.bdy)
  of tPair:
    occursSyn(id, t.pFst) or occursSyn(id, t.pSnd) or
      occursSyn(id, t.pScope.bdy)
  of tApp: occursSyn(id, t.fn) or occursSyn(id, t.arg)
  of tFst, tSnd, tAbsurd: occursSyn(id, t.sub)
  of tLet:
    occursSyn(id, t.letVal) or occursSyn(id, t.letTy) or
      occursSyn(id, t.letScope.bdy)

proc invertSpine(spine: seq[Term], loc: Loc): seq[int] =
  ## spine (innermost-first) must be distinct bound variables.
  ## Returns perm with perm[i] = the current-context var for creation var i.
  result = newSeq[int](spine.len)
  var seen = initHashSet[int]()
  for i, s in spine:
    if s.kind != tV or s.idx in seen:
      raise uerr(loc, "cannot solve metavariable: not a pattern spine")
    seen.incl(s.idx)
    result[i] = s.idx

proc renameAt(t: Term, inv: seq[int], depth, n: int, loc: Loc): Term =
  ## Rename current-context vars back to creation-context vars.
  ## inv[j] = creation var for current var j (at depth 0); -1 = unmapped.
  case t.kind
  of tV:
    if t.idx < depth: t
    else:
      let j = t.idx - depth
      if j < inv.len and inv[j] >= 0: vv(inv[j] + depth)
      else: raise uerr(loc,
        "cannot solve metavariable: variable V" & $t.idx & " escapes the spine")
  of tR, tC, tInt, tPrim, tNatLit: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(renameAt(it, inv, depth, n, loc)))
  of tPi, tSi, tLam:
    mkBinder(t.kind, renameAt(t.dom, inv, depth, n, loc),
              Scope(adv: t.scope.adv,
                    bdy: renameAt(t.scope.bdy, inv, depth + 1, n, loc)),
              t.impl, t.qty)
  of tPair:
    tmPair(renameAt(t.pFst, inv, depth, n, loc),
           renameAt(t.pSnd, inv, depth, n, loc), t.pScope.adv,
           renameAt(t.pScope.bdy, inv, depth + 1, n, loc))
  of tApp:
    tmApp(renameAt(t.fn, inv, depth, n, loc), renameAt(t.arg, inv, depth, n, loc))
  of tFst: tmFst(renameAt(t.sub, inv, depth, n, loc))
  of tSnd: tmSnd(renameAt(t.sub, inv, depth, n, loc))
  of tAbsurd: tmAbsurd(renameAt(t.sub, inv, depth, n, loc))
  of tLet:
    tmLet(renameAt(t.letVal, inv, depth, n, loc),
          renameAt(t.letTy, inv, depth, n, loc), t.letScope.adv,
          renameAt(t.letScope.bdy, inv, depth + 1, n, loc))

proc unify*(ms: var MetaStore, a, b: Term, loc: Loc)  # forward (mutual with solveMeta)

proc solveMeta(ms: var MetaStore, id: int, spine: seq[Term], t: Term, loc: Loc) =
  ## Solve ?m[spine] = t (Miller pattern fragment).
  if id notin ms.entries:
    raise uerr(loc, "unknown metavariable ?m" & $id)
  let e = ms.entries[id]
  if not e.solution.isNil:
    unify(ms, substSpine(e.solution, spine.mapIt(zonk(ms, it))), t, loc)
    return
  let zsp = spine.mapIt(zonk(ms, it))
  let zt = zonk(ms, t)
  if occursSyn(id, zt):
    # Issue #80: name the noCycle case — a constructor applied to a term
    # containing the meta can never equal the meta itself.
    let hid = ctorHeadOf(ms, zt)
    if hid >= 0:
      raise uerr(loc, "occurs check failed for ?m" & $id & " (noCycle): " &
        "constructor '" & ms.ctorTable.ctorNames[hid] &
        "' is applied to a term containing ?m" & $id)
    raise uerr(loc, "occurs check failed for ?m" & $id)
  let perm = invertSpine(zsp, loc)
  var maxV = -1
  for p in perm: maxV = max(maxV, p)
  var inv = newSeq[int](maxV + 1)
  for i in 0 .. maxV: inv[i] = -1
  for i, p in perm: inv[p] = i
  let sol = renameAt(zt, inv, 0, e.metaCtxLen, loc)
  ms.entries[id] = MetaEntry(metaTy: e.metaTy, metaCtxLen: e.metaCtxLen,
                             metaLoc: e.metaLoc, solution: sol)

# --- unification ---------------------------------------------------------------

proc unify*(ms: var MetaStore, a, b: Term, loc: Loc) =
  let a1 = unifyHead(ms, a)
  let b1 = unifyHead(ms, b)
  if a1.kind == tMeta and b1.kind == tMeta and a1.metaId == b1.metaId:
    # flex-flex, same meta: unify the spines
    if a1.metaSpine.len != b1.metaSpine.len:
      raise uerr(loc, "metavariable spine length mismatch")
    for i in 0 ..< a1.metaSpine.len:
      unify(ms, a1.metaSpine[i], b1.metaSpine[i], loc)
    return
  if a1.kind == tMeta:
    solveMeta(ms, a1.metaId, a1.metaSpine, b1, loc)
    return
  if b1.kind == tMeta:
    solveMeta(ms, b1.metaId, b1.metaSpine, a1, loc)
    return
  if a1.kind != b1.kind:
    # eta: lambda against a neutral
    if a1.kind == tLam and b1.kind in {tR, tV, tApp, tFst, tSnd}:
      unify(ms, a1.scope.bdy, tmApp(weaken(b1), vv(0)), loc)
      return
    if b1.kind == tLam and a1.kind in {tR, tV, tApp, tFst, tSnd}:
      unify(ms, tmApp(weaken(a1), vv(0)), b1.scope.bdy, loc)
      return
    # Issue #80: named noConfusion — distinct constructors of one datatype
    # (e.g. `zero =?= suc n`, which used to report "cannot unify tR with
    # tApp") fail fast with the constructors named.
    let ha = ctorHeadOf(ms, a1)
    let hb = ctorHeadOf(ms, b1)
    if ha >= 0 and hb >= 0 and ha != hb and sameDatatypeCtors(ms, ha, hb):
      raise uerr(loc, noConfusionMsg(ms, ha, hb))
    raise uerr(loc, "cannot unify " & $a1.kind & " with " & $b1.kind)
  case a1.kind
  of tC:
    if a1.c != b1.c: raise uerr(loc, "constant mismatch")
  of tInt:
    if a1.intVal != b1.intVal: raise uerr(loc, "integer mismatch")
  of tNatLit:
    if a1.natLitVal != b1.natLitVal: raise uerr(loc, "nat literal mismatch")
  of tPrim:
    if a1.primOp != b1.primOp: raise uerr(loc, "primitive op mismatch")
  of tR:
    if a1.refId != b1.refId:
      # Issue #80: name the noConfusion case for bare constructors
      # (used to report the generic "neutral mismatch").
      if sameDatatypeCtors(ms, a1.refId, b1.refId):
        raise uerr(loc, noConfusionMsg(ms, a1.refId, b1.refId))
      raise uerr(loc, "neutral mismatch")
  of tV:
    if a1.idx != b1.idx: raise uerr(loc, "variable mismatch")
  of tPi, tSi, tLam:
    if a1.impl != b1.impl:
      raise uerr(loc, "implicit/explicit binder mismatch")
    unify(ms, a1.dom, b1.dom, loc)
    unify(ms, a1.scope.bdy, b1.scope.bdy, loc)
  of tPair:
    unify(ms, a1.pFst, b1.pFst, loc)
    unify(ms, a1.pSnd, b1.pSnd, loc)
    unify(ms, a1.pScope.bdy, b1.pScope.bdy, loc)
  of tApp:
    unify(ms, a1.fn, b1.fn, loc)
    unify(ms, a1.arg, b1.arg, loc)
  of tFst, tSnd, tAbsurd:
    unify(ms, a1.sub, b1.sub, loc)
  of tLet:
    unify(ms, a1.letVal, b1.letVal, loc)
    unify(ms, a1.letTy, b1.letTy, loc)
    unify(ms, a1.letScope.bdy, b1.letScope.bdy, loc)
  of tMeta:
    discard  # handled above

when isMainModule:
  import strutils
  var ms = initMetaStore()
  let loc = noLoc

  # ?m0[V0] = 1, then zonk
  let m0 = freshMeta(ms, tmC(cStar), 1, 0, loc)
  unify(ms, m0, tmC(cOne), loc)
  assert $zonk(ms, m0) == "1"
  echo "ok: solve ?m[V0] = 1"

  # occurs check
  let m1 = freshMeta(ms, tmC(cStar), 0, 0, loc)
  try:
    unify(ms, m1, tmApp(m1, tmC(cOne)), loc)
    assert false, "occurs check should fail"
  except UnifyError as e:
    assert "occurs check" in e.msg
    echo "ok: occurs check fires"

  # pattern spine violation: ?m[V0, V0] = 1
  let m2 = freshMeta(ms, tmC(cStar), 1, 0, loc)
  let badSpine = tmMeta(m2.metaId, @[vv(0), vv(0)])
  try:
    unify(ms, badSpine, tmC(cOne), loc)
    assert false, "non-pattern spine should fail"
  except UnifyError as e:
    assert "pattern spine" in e.msg
    echo "ok: non-pattern spine rejected"

  # spine inversion: ?m[V1] = V1  ==>  stored solution V0 (creation ctx),
  # while the value at the occurrence (spine [V1]) is V1
  var ms2 = initMetaStore()
  let m3 = freshMeta(ms2, tmC(cStar), 1, 1, loc)  # occurrence under 1 binder
  assert $m3.metaSpine[0] == "V1", $m3.metaSpine[0]
  unify(ms2, m3, vv(1), loc)
  assert $ms2.entries[m3.metaId].solution == "V0",
    $ms2.entries[m3.metaId].solution
  assert $zonk(ms2, m3) == "V1", $zonk(ms2, m3)
  echo "ok: spine inversion"

  # rigid-rigid success and failure
  var ms3 = initMetaStore()
  unify(ms3, tmPi(tmC(cStar), "A", vv(0)), tmPi(tmC(cStar), "B", vv(0)), loc)
  echo "ok: rigid-rigid Pi"
  try:
    unify(ms3, tmC(cOne), tmC(cZero), loc)
    assert false
  except UnifyError:
    echo "ok: constant mismatch rejected"

  # eta: lam (x:? ). r x  =?=  r  (r neutral) -- expands r, bodies match
  var ms4 = initMetaStore()
  let r = Term(kind: tR, refId: 99, refTyp: nil, refIsDefn: false, refVal: nil)
  unify(ms4, tmLam(tmC(cStar), "x", tmApp(r, vv(0))), r, loc)
  echo "ok: eta expansion"
  # and the negative: lam (x:? ). x  =/=  r
  try:
    unify(ms4, tmLam(tmC(cStar), "x", vv(0)), r, loc)
    assert false, "identity vs neutral should not unify"
  except UnifyError:
    echo "ok: eta does not equate identity with a neutral"

  # flex-flex same meta: unifies the spines; solving one occurrence
  # is visible at the other
  var ms5 = initMetaStore()
  let m4 = freshMeta(ms5, tmC(cStar), 1, 0, loc)
  let m4alias = tmMeta(m4.metaId, @[vv(0)])
  unify(ms5, m4, m4alias, loc)  # same meta, same spine: fine
  unify(ms5, m4, tmC(cOne), loc)
  assert $zonk(ms5, m4alias) == "1"
  echo "ok: flex-flex same meta"

  # Issue #80: constructor disjointness (noConfusion / noCycle).
  # Fake a Nat datatype: datatype refId 100, ctors zero=101, suc=102.
  var ms6 = initMetaStore()
  ms6.registerDataCtors(100, "Nat", @[(101, "zero"), (102, "suc")])
  let zero6 = Term(kind: tR, refId: 101, refTyp: nil, refIsDefn: false, refVal: nil)
  let suc6 = Term(kind: tR, refId: 102, refTyp: nil, refIsDefn: false, refVal: nil)
  # zero =?= suc n: named noConfusion (was "cannot unify tR with tApp")
  try:
    unify(ms6, zero6, tmApp(suc6, vv(0)), loc)
    assert false, "zero =?= suc n should fail"
  except UnifyError as e:
    assert "noConfusion" in e.msg and "zero" in e.msg and "suc" in e.msg,
      e.msg
    echo "ok: noConfusion named conflict (zero vs suc n)"
  # bare constructors: named instead of "neutral mismatch"
  try:
    unify(ms6, zero6, suc6, loc)
    assert false, "zero =?= suc should fail"
  except UnifyError as e:
    assert "noConfusion" in e.msg and "Nat" in e.msg, e.msg
    echo "ok: noConfusion named conflict (bare constructors)"
  # injectivity still decomposes: suc ?m =?= suc V0 solves ?m := V0
  var ms7 = initMetaStore()
  ms7.registerDataCtors(100, "Nat", @[(101, "zero"), (102, "suc")])
  let mA = freshMeta(ms7, tmC(cStar), 1, 0, loc)
  unify(ms7, tmApp(suc6, mA), tmApp(suc6, vv(0)), loc)
  assert $zonk(ms7, mA) == "V0", $zonk(ms7, mA)
  echo "ok: injectivity decomposes (suc ?m =?= suc V0)"
  # noCycle: ?m =?= suc ?m names the constructor
  var ms8 = initMetaStore()
  ms8.registerDataCtors(100, "Nat", @[(101, "zero"), (102, "suc")])
  let mB = freshMeta(ms8, tmC(cStar), 0, 0, loc)
  try:
    unify(ms8, mB, tmApp(suc6, mB), loc)
    assert false, "occurs check should fire"
  except UnifyError as e:
    assert "noCycle" in e.msg and "suc" in e.msg and "occurs check" in e.msg,
      e.msg
    echo "ok: noCycle named cycle error"
  # unregistered refIds keep the old generic errors
  var ms9 = initMetaStore()
  let r1 = Term(kind: tR, refId: 201, refTyp: nil, refIsDefn: false, refVal: nil)
  let r2 = Term(kind: tR, refId: 202, refTyp: nil, refIsDefn: false, refVal: nil)
  try:
    unify(ms9, r1, r2, loc)
    assert false
  except UnifyError as e:
    assert e.msg == "neutral mismatch", e.msg
    echo "ok: unregistered refs keep generic errors"
  # forbid-edges: one unordered pair for Nat's two constructors
  let edges = ms8.constructorForbidEdges()
  assert edges.len == 1 and edges[0] == (101, 102), $edges
  echo "ok: constructor forbid-edges"

  # noConfusionConflict: recursive rigid check used by conversion.
  var ms10 = initMetaStore()
  ms10.registerDataCtors(100, "Nat", @[(101, "zero"), (102, "suc")])
  let z10 = Term(kind: tR, refId: 101, refTyp: nil, refIsDefn: false, refVal: nil)
  let s10 = Term(kind: tR, refId: 102, refTyp: nil, refIsDefn: false, refVal: nil)
  # Vec Nat zero vs Vec Nat (suc zero): Vec is a rigid postulate head,
  # so injectivity descent finds zero vs suc.
  let vec10 = Term(kind: tR, refId: 103, refTyp: nil, refIsDefn: false, refVal: nil)
  let v1 = tmApp(tmApp(vec10, tmC(cStar)), z10)
  let v2 = tmApp(tmApp(vec10, tmC(cStar)), tmApp(s10, z10))
  let nc10 = noConfusionConflict(ms10, v1, v2)
  assert nc10.bad and nc10.c1 == 101 and nc10.c2 == 102, $nc10
  echo "ok: noConfusionConflict descends through rigid heads"
  # defined head: no descent (would be unsound — a definition could map
  # distinct arguments to equal values)
  let add10 = Term(kind: tR, refId: 104, refTyp: nil, refIsDefn: true, refVal: nil)
  let d1 = tmApp(tmApp(add10, z10), vv(0))
  let d2 = tmApp(tmApp(add10, tmApp(s10, z10)), z10)
  assert not noConfusionConflict(ms10, d1, d2).bad
  echo "ok: noConfusionConflict does not descend through definitions"
  # flexible positions are compatible
  var ms11 = initMetaStore()
  ms11.registerDataCtors(100, "Nat", @[(101, "zero"), (102, "suc")])
  let mC = freshMeta(ms11, tmC(cStar), 1, 0, loc)
  assert not noConfusionConflict(ms11, tmApp(s10, mC), tmApp(s10, z10)).bad
  assert not noConfusionConflict(ms11, tmApp(s10, z10), tmApp(s10, mC)).bad
  echo "ok: noConfusionConflict treats metas as compatible"

  echo "--- unify tests done ---"
