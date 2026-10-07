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
import strutils
import preterm   # Loc
import ett_init

type
  UnifyError* = object of CatchableError

  MetaEntry* = object
    metaTy*: Term     # type of the meta, in creation context
    metaCtxLen*: int  # length of the creation context
    metaLoc*: Loc     # where the meta was created (for error messages)
    solution*: Term   # nil = unsolved; lives in the creation context

  MetaStore* = object
    nextId*: int
    entries*: Table[int, MetaEntry]

proc initMetaStore*(): MetaStore =
  MetaStore(nextId: 0, entries: initTable[int, MetaEntry]())

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

proc unifyHead(ms: MetaStore, t: Term): Term =
  ## Head-normalize for unification: unfold solved metas (at the head
  ## and in function position) and beta-reduce. No delta-unfolding of
  ## definitions — rigid heads stay rigid. (Experiment 4: eliminator
  ## motives are lambdas, so `C true` with `C := lam u. Bool` must
  ## head-reduce before the rigid-rigid comparison.)
  var cur = zonkHead(ms, t)
  while true:
    if cur.kind != tApp: return cur
    let f = unifyHead(ms, cur.fn)
    if f.kind == tLam:
      cur = zonkHead(ms, subst(f.scope.bdy, 0, cur.arg))
    else:
      return tmApp(f, cur.arg)

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
  of tV, tR, tC: t
  of tPi, tSi, tLam:
    mkBinder(t.kind, zonk(ms, t.dom),
              Scope(adv: t.scope.adv, bdy: zonk(ms, t.scope.bdy)), t.impl)
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
  of tV, tR, tC: (false, 0, noLoc)
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
  of tV, tR, tC: false
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
  of tR, tC: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(renameAt(it, inv, depth, n, loc)))
  of tPi, tSi, tLam:
    mkBinder(t.kind, renameAt(t.dom, inv, depth, n, loc),
              Scope(adv: t.scope.adv,
                    bdy: renameAt(t.scope.bdy, inv, depth + 1, n, loc)),
              t.impl)
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
  ## Solve ?m[spine] := t (Miller pattern fragment).
  if id notin ms.entries:
    raise uerr(loc, "unknown metavariable ?m" & $id)
  let e = ms.entries[id]
  if not e.solution.isNil:
    unify(ms, substSpine(e.solution, spine.mapIt(zonk(ms, it))), t, loc)
    return
  let zsp = spine.mapIt(zonk(ms, it))
  let zt = zonk(ms, t)
  if occursSyn(id, zt):
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
    raise uerr(loc, "cannot unify " & $a1.kind & " with " & $b1.kind)
  case a1.kind
  of tC:
    if a1.c != b1.c: raise uerr(loc, "constant mismatch")
  of tR:
    if a1.refId != b1.refId: raise uerr(loc, "neutral mismatch")
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
  var ms = initMetaStore()
  let loc = noLoc

  # ?m0[V0] := 1, then zonk
  let m0 = freshMeta(ms, tmC(cStar), 1, 0, loc)
  unify(ms, m0, tmC(cOne), loc)
  assert $zonk(ms, m0) == "1"
  echo "ok: solve ?m[V0] := 1"

  # occurs check
  let m1 = freshMeta(ms, tmC(cStar), 0, 0, loc)
  try:
    unify(ms, m1, tmApp(m1, tmC(cOne)), loc)
    assert false, "occurs check should fail"
  except UnifyError as e:
    assert "occurs check" in e.msg
    echo "ok: occurs check fires"

  # pattern spine violation: ?m[V0, V0] := 1
  let m2 = freshMeta(ms, tmC(cStar), 1, 0, loc)
  let badSpine = tmMeta(m2.metaId, @[vv(0), vv(0)])
  try:
    unify(ms, badSpine, tmC(cOne), loc)
    assert false, "non-pattern spine should fail"
  except UnifyError as e:
    assert "pattern spine" in e.msg
    echo "ok: non-pattern spine rejected"

  # spine inversion: ?m[V1] := V1  ==>  stored solution V0 (creation ctx),
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

  echo "--- unify tests done ---"
