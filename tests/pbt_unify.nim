## tests/pbt_unify.nim — Issue #163: property tests for the Miller
## pattern-fragment unifier (src/eponym/unify.nim).
##
## The unifier is the elaborator's workhorse for implicit arguments,
## and its spine-inversion machinery (invertSpine/renameAt/solveMeta) is
## subtle enough to deserve extensional checks. Properties pin:
##   P1 solve-then-zonk agreement (soundness roundtrip): when unify(a, b)
##      succeeds, zonk(a) and zonk(b) are structurally equal.
##   P2 spine-inversion roundtrip: solving ?m[sp] = t stores a solution
##      with zonk(substSpine(solution, zonkedSpine)) == zonk(t) — the
##      stored solution really does reconstruct the unified term.
##   P3 symmetry: unify(a, b) and unify(b, a) agree on success when at
##      most one side is flexible; rigid-rigid comparison is symmetric.
##      (Flex-flex with distinct metas is order-sensitive by design — the
##      unifier commits to solving the head's meta — pinned by a targeted
##      characterization case, not a universal property.)
##   P4 occurs check: ?m = t[?m] raises UnifyError; a constructor-headed
##      t names noCycle (issue #80).
##   P5 non-pattern spines rejected: duplicate-var spines, non-var spines,
##      and escaping variables all raise.
##   P6 zonk idempotence: zonk(zonk(t)) == zonk(t), even mid-elaboration.
##   P7 eta: lam(x). r x =?= r succeeds for neutral r; lam(x). x =/= r fails.
##   P8 noConfusion differential: on ground constructor terms, unify
##      succeeds iff the terms are structurally equal; distinct
##      constructors of one datatype fail with the named noConfusion error.
##   P9 reflexivity: unify(t, t) succeeds on random ground terms (with
##      binders) and on bare unsolved metas.
##
## Run: nim c -r --hints:off --path:src --path:src/eponym \
##        --path:src/experimental --path:src/experimental/relational --path:src/experimental/staging tests/pbt_unify.nim
## Fixed seed 424242 in CI (change Seed locally for fresh fuzzing).

import pbt
import eponym_init  # Term, vv, tmLam/tmPi/tmApp/..., tmMeta, weaken, substSpine
import preterm       # Loc, noLoc, Quantity (q0/q1/qOmega)
import unify         # MetaStore, initMetaStore, freshMeta, unify, zonk,
                     # UnifyError, registerDataCtors
import sequtils
import tables
import strutils

const Seed = 424242'u64
const Cases = 200

# --- structural equality ----------------------------------------------------
# Term has hash but no ==; compare every semantically relevant field
# (display hints `adv` excluded).

proc structEq*(a, b: Term): bool =
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of tV: a.idx == b.idx
  of tR: a.refId == b.refId
  of tC: a.c == b.c
  of tInt: a.intVal == b.intVal
  of tNatLit: a.natLitVal == b.natLitVal
  of tNatSing: a.natSingVal == b.natSingVal
  of tPrim: a.primOp == b.primOp and structEq(a.primTy, b.primTy)
  of tMeta:
    if a.metaId != b.metaId or a.metaSpine.len != b.metaSpine.len:
      return false
    for i in 0 ..< a.metaSpine.len:
      if not structEq(a.metaSpine[i], b.metaSpine[i]): return false
    true
  of tPi, tSi, tLam:
    a.impl == b.impl and structEq(a.dom, b.dom) and
      structEq(a.scope.bdy, b.scope.bdy)
  of tPair:
    structEq(a.pFst, b.pFst) and structEq(a.pSnd, b.pSnd) and
      structEq(a.pScope.bdy, b.pScope.bdy)
  of tApp: structEq(a.fn, b.fn) and structEq(a.arg, b.arg)
  of tFst, tSnd, tAbsurd: structEq(a.sub, b.sub)
  of tLet:
    structEq(a.letVal, b.letVal) and structEq(a.letTy, b.letTy) and
      structEq(a.letScope.bdy, b.letScope.bdy)

# --- generators --------------------------------------------------------------

type
  MetaOcc* = tuple[id: int, spine: seq[Term]]  # one generated occurrence

proc permSpine*(r: var Rng, id, k, e: int): seq[Term] =
  ## A random permutation of the k creation-context vars, shifted by e
  ## (a pattern spine by construction).
  var p = toSeq(0 ..< k)
  for i in countdown(p.high, 1):
    let j = r.below(i + 1)
    swap(p[i], p[j])
  p.mapIt(vv(e + it))

proc genMetaOcc*(r: var Rng, metas: seq[int], k, e: int): Term =
  ## One occurrence of a random known meta: identity or permuted spine.
  let id = metas[r.below(metas.len)]
  if r.genBool: tmMeta(id, toSeq(0 ..< k).mapIt(vv(e + it)))
  else: tmMeta(id, permSpine(r, id, k, e))

proc genFlex*(r: var Rng, depth, maxVar: int, metas: seq[int],
             k, e: int): Term =
  ## Terms possibly mentioning metas (no binders: every meta occurrence
  ## stays in the creation context + e extra binders).
  if depth <= 0:
    case r.below(6)
    of 0: vv(r.below(maxVar + 1))
    of 1: tmC(cStar)
    of 2: tmC(cOne)
    of 3: tmInt(r.genInt(-2, 2))
    of 4: tmNatLit(r.below(3))
    else:
      if metas.len > 0: genMetaOcc(r, metas, k, e)
      else: vv(r.below(maxVar + 1))
  else:
    case r.below(6)
    of 0: tmApp(genFlex(r, depth-1, maxVar, metas, k, e),
                genFlex(r, depth-1, maxVar, metas, k, e))
    of 1: tmPair(genFlex(r, depth-1, maxVar, metas, k, e),
                 genFlex(r, depth-1, maxVar, metas, k, e),
                 "p", genFlex(r, depth-1, maxVar, metas, k, e))
    of 2: tmFst(genFlex(r, depth-1, maxVar, metas, k, e))
    of 3: tmSnd(genFlex(r, depth-1, maxVar, metas, k, e))
    of 4:
      if metas.len > 0: genMetaOcc(r, metas, k, e)
      else: genFlex(r, 0, maxVar, metas, k, e)
    else: genFlex(r, depth-1, maxVar, metas, k, e)

proc genGround*(r: var Rng, depth, maxVar: int): Term =
  ## Meta-free terms, binders allowed (used for P8/P9).
  if depth <= 0:
    case r.below(5)
    of 0: vv(r.below(maxVar + 1))
    of 1: tmC(cStar)
    of 2: tmInt(r.genInt(-2, 2))
    of 3: tmNatLit(r.below(3))
    else: tmC(cOne)
  else:
    case r.below(8)
    of 0: tmApp(genGround(r, depth-1, maxVar), genGround(r, depth-1, maxVar))
    of 1: tmLam(tmC(cStar), "x", genGround(r, depth-1, maxVar + 1))
    of 2: tmPi(tmC(cStar), "x", genGround(r, depth-1, maxVar + 1))
    of 3: tmPair(genGround(r, depth-1, maxVar), genGround(r, depth-1, maxVar),
                 "p", genGround(r, depth-1, maxVar + 1))
    of 4: tmFst(genGround(r, depth-1, maxVar))
    of 5: tmSnd(genGround(r, depth-1, maxVar))
    of 6: tmLet(genGround(r, depth-1, maxVar), tmC(cStar), "y",
                genGround(r, depth-1, maxVar + 1))
    else: genGround(r, depth-1, maxVar)

type
  PairCase* = tuple[ms: MetaStore, a, b: Term]

proc genPair*(r: var Rng): PairCase =
  ## Two terms sharing a fresh MetaStore with 1..3 metas (creation
  ## context length 0..2, occurrence under 0..1 extra binders). Half the
  ## cases pair a term with itself (must succeed); half pair two
  ## independent terms (mixed outcomes).
  let k = r.genInt(0, 2)
  let e = r.below(2)
  var ms = initMetaStore()
  var metas: seq[int] = @[]
  for _ in 0 ..< 1 + r.below(3):
    let occ = freshMeta(ms, tmC(cStar), k, e, noLoc)
    metas.add(occ.metaId)
  let maxVar = e + k - 1
  let a = genFlex(r, 3, max(maxVar, 0), metas, k, e)
  let b = if r.genBool: a else: genFlex(r, 3, max(maxVar, 0), metas, k, e)
  (ms, a, b)

proc tryUnify(ms: var MetaStore, a, b: Term): bool =
  try:
    unify(ms, a, b, noLoc)
    true
  except UnifyError:
    false

# --- P1: solve-then-zonk agreement --------------------------------------------

var p1ok = 0
var p1fail = 0
var p1solved = 0

proc propP1(c: PairCase): bool =
  var (ms, a, b) = c
  if not tryUnify(ms, a, b):
    inc p1fail
    return true
  inc p1ok
  for id, e in ms.entries:
    if not e.solution.isNil: inc p1solved
  # P6 (zonk idempotence) rides along on the same cases.
  if not structEq(zonk(ms, zonk(ms, a)), zonk(ms, a)): return false
  if not structEq(zonk(ms, zonk(ms, b)), zonk(ms, b)): return false
  structEq(zonk(ms, a), zonk(ms, b))

# --- P2: spine-inversion roundtrip ---------------------------------------------

type
  SpineCase* = tuple[ms: MetaStore, id: int, spine: seq[Term], t: Term]

proc genSpineCase*(r: var Rng): SpineCase =
  ## One meta solved against a random term through a permuted spine.
  ## The term may mention *other* metas (aliasing), but not this one.
  let k = r.genInt(1, 3)
  let e = r.below(2)
  var ms = initMetaStore()
  var other: seq[int] = @[]
  for _ in 0 ..< r.below(3):
    other.add(freshMeta(ms, tmC(cStar), k, e, noLoc).metaId)
  let id = freshMeta(ms, tmC(cStar), k, e, noLoc).metaId
  let spine = permSpine(r, id, k, e)
  let t = genFlex(r, 3, e + k - 1, other, k, e)
  (ms, id, spine, t)

var p2ok = 0

proc propP2(c: SpineCase): bool =
  var (ms, id, spine, t) = c
  let occ = tmMeta(id, spine)
  if not tryUnify(ms, occ, t):
    return true  # e.g. t mentions id indirectly — failure is fine
  inc p2ok
  let sol = ms.entries[id].solution
  if sol.isNil: return false  # success must record a solution
  let zsp = spine.mapIt(zonk(ms, it))
  # The stored solution, applied to the (zonked) spine and fully zonked,
  # reconstructs the unified term.
  structEq(zonk(ms, substSpine(sol, zsp)), zonk(ms, t))

# --- P3: symmetry ---------------------------------------------------------------

var p3ok = 0
var p3fail = 0

proc propP3(c: PairCase): bool =
  ## Success must agree in both directions. With pattern spines this
  ## holds across the generator's cases: one-flex-side pairs dispatch to
  ## the same solveMeta call either way; distinct-meta flex-flex succeeds
  ## in both directions (solving opposite sides); rigid-rigid and the eta
  ## cases are symmetric by construction.
  var (ms, a, b) = c
  var ms2 = ms  # value copy: same meta ids, independent solutions
  let ok1 = tryUnify(ms, a, b)
  let ok2 = tryUnify(ms2, b, a)
  if ok1: inc p3ok else: inc p3fail
  ok1 == ok2

proc propP3ground(r: var Rng): bool =
  let a = genGround(r, 3, 2)
  let b = genGround(r, 3, 2)
  var ms1 = initMetaStore()
  var ms2 = initMetaStore()
  tryUnify(ms1, a, b) == tryUnify(ms2, b, a)

# --- P4: occurs check ------------------------------------------------------------

proc propP4(r: var Rng): bool =
  var ms = initMetaStore()
  let m = freshMeta(ms, tmC(cStar), 0, 0, noLoc)
  # t properly contains m (never bare m: that takes the flex-flex path).
  let t =
    if r.genBool: tmApp(m, tmC(cOne))
    else: tmLam(tmC(cStar), "x", tmApp(m, vv(0)))
  try:
    unify(ms, m, t, noLoc)
    return false
  except UnifyError as e:
    return "occurs check" in e.msg

proc propP4noCycle(): bool =
  ## Constructor-headed occurs failure names noCycle (issue #80).
  var ms = initMetaStore()
  ms.registerDataCtors(100, "Nat", @[(101, "zero"), (102, "suc")])
  let suc = Term(kind: tR, refId: 102, refTyp: nil, refIsDefn: false,
                 refVal: nil)
  let m = freshMeta(ms, tmC(cStar), 0, 0, noLoc)
  try:
    unify(ms, m, tmApp(suc, m), noLoc)
    return false
  except UnifyError as e:
    return "occurs check" in e.msg and "noCycle" in e.msg

# --- P5: non-pattern spines -------------------------------------------------------

proc propP5dup(): bool =
  var ms = initMetaStore()
  let m = freshMeta(ms, tmC(cStar), 1, 0, noLoc)
  let bad = tmMeta(m.metaId, @[vv(0), vv(0)])
  try:
    unify(ms, bad, tmC(cOne), noLoc)
    return false
  except UnifyError as e:
    return "pattern spine" in e.msg

proc propP5nonVar(): bool =
  var ms = initMetaStore()
  let m = freshMeta(ms, tmC(cStar), 1, 0, noLoc)
  let bad = tmMeta(m.metaId, @[tmC(cOne)])
  try:
    unify(ms, bad, tmC(cOne), noLoc)
    return false
  except UnifyError as e:
    return "pattern spine" in e.msg

proc propP5escape(): bool =
  var ms = initMetaStore()
  let m = freshMeta(ms, tmC(cStar), 1, 0, noLoc)  # spine [V0]
  try:
    unify(ms, m, vv(5), noLoc)  # V5 not in the spine
    return false
  except UnifyError as e:
    return "escapes the spine" in e.msg

# --- P7: eta -----------------------------------------------------------------------

proc neutralR(id: int): Term =
  Term(kind: tR, refId: id, refTyp: nil, refIsDefn: false, refVal: nil)

proc propP7pos(r: var Rng): bool =
  ## lam(x). r x =?= r for neutral r: the eta rule fires.
  ## (No zonk-equality: the sides are convertible, not structurally equal.)
  let r =
    if r.genBool: neutralR(99)
    else: tmApp(vv(0), tmC(cOne))
  var ms = initMetaStore()
  let lam = tmLam(tmC(cStar), "x", tmApp(weaken(r), vv(0)))
  tryUnify(ms, lam, r)

proc propP7constNeg(r: var Rng): bool =
  ## lam(x). r =/= r when x is unused: eta does not fire spuriously.
  let r =
    if r.genBool: neutralR(99)
    else: tmApp(vv(0), tmC(cOne))
  var ms = initMetaStore()
  not tryUnify(ms, tmLam(tmC(cStar), "x", weaken(r)), r)

proc propP7neg(r: var Rng): bool =
  ## lam(x). x =/= r: the identity is not eta-equal to a neutral.
  let r =
    if r.genBool: neutralR(99)
    else: tmApp(vv(0), tmC(cOne))
  var ms = initMetaStore()
  not tryUnify(ms, tmLam(tmC(cStar), "x", vv(0)), r)

# --- P8: noConfusion differential ---------------------------------------------------

proc fakeNatCtors(ms: var MetaStore) =
  ms.registerDataCtors(100, "Nat", @[(101, "zero"), (102, "suc")])
  ms.registerDataCtors(200, "Bool", @[(201, "true"), (202, "false")])

proc genCtorTerm(r: var Rng, depth: int): Term =
  ## Ground terms over two fake datatypes.
  if depth <= 0:
    case r.below(4)
    of 0: Term(kind: tR, refId: 101, refTyp: nil, refIsDefn: false, refVal: nil)
    of 1: Term(kind: tR, refId: 201, refTyp: nil, refIsDefn: false, refVal: nil)
    of 2: tmInt(r.genInt(0, 2))
    else: tmC(cOne)
  else:
    case r.below(4)
    of 0: tmApp(Term(kind: tR, refId: 102, refTyp: nil, refIsDefn: false,
                     refVal: nil),
                genCtorTerm(r, depth - 1))
    of 1: tmApp(Term(kind: tR, refId: 202, refTyp: nil, refIsDefn: false,
                     refVal: nil),
                genCtorTerm(r, depth - 1))
    of 2: tmApp(genCtorTerm(r, depth - 1), genCtorTerm(r, depth - 1))
    else: genCtorTerm(r, depth - 1)

var p8named = 0

proc propP8(r: var Rng): bool =
  ## On ground constructor terms, unify succeeds iff structurally equal.
  let a = genCtorTerm(r, 3)
  let b = genCtorTerm(r, 3)
  var ms = initMetaStore()
  fakeNatCtors(ms)
  var ok = false
  var msg = ""
  try:
    unify(ms, a, b, noLoc)
    ok = true
  except UnifyError as e:
    msg = e.msg
  if ok != structEq(a, b): return false
  if not ok and not structEq(a, b):
    # Distinct constructors of one datatype must fail *by name*.
    let ha = ms.ctorHeadOf(a)
    let hb = ms.ctorHeadOf(b)
    if ha >= 0 and hb >= 0 and ha != hb and
        ms.sameDatatypeCtors(ha, hb):
      if "noConfusion" notin msg: return false
      inc p8named
  true

# --- P9: reflexivity ------------------------------------------------------------------

proc propP9(r: var Rng): bool =
  let t = genGround(r, 3, 2)
  var ms = initMetaStore()
  tryUnify(ms, t, t)

proc propP9meta(): bool =
  var ms = initMetaStore()
  let m = freshMeta(ms, tmC(cStar), 2, 0, noLoc)
  tryUnify(ms, m, m)

# --- flex-flex order characterization --------------------------------------------
# Documents the head-commitment: unify(?m1[dup-spine], ?m2[pat]) fails
# (non-pattern spine), while the reverse order succeeds by solving ?m2.
# The unifier does not backtrack to the other side — incomplete, but sound.

proc propFlexOrder(): bool =
  var ms1 = initMetaStore()
  let m1 = freshMeta(ms1, tmC(cStar), 1, 0, noLoc)
  let m2 = freshMeta(ms1, tmC(cStar), 1, 0, noLoc)
  let dup = tmMeta(m1.metaId, @[vv(0), vv(0)])
  let fwdFails =
    try:
      unify(ms1, dup, m2, noLoc)
      false
    except UnifyError as e:
      "pattern spine" in e.msg
  var ms2 = initMetaStore()
  let n1 = freshMeta(ms2, tmC(cStar), 1, 0, noLoc)
  let n2 = freshMeta(ms2, tmC(cStar), 1, 0, noLoc)
  let revOk =
    try:
      unify(ms2, n2, tmMeta(n1.metaId, @[vv(0), vv(0)]), noLoc)
      structEq(zonk(ms2, n2), tmMeta(n1.metaId, @[vv(0), vv(0)]))
    except UnifyError:
      false
  fwdFails and revOk

# --- main --------------------------------------------------------------------------

when isMainModule:
  var r = initRng(Seed)
  var allOk = true
  template check(name: string, body: bool) =
    let b: bool = body
    echo (if b: "ok: " else: "FAIL: ") & name
    allOk = allOk and b

  check("P1 solve-then-zonk agreement (+P6 zonk idempotence)",
        forAll("p1", r, Cases, genPair, propP1))
  check("P1 non-vacuous: successes, failures, and solutions all occur",
        p1ok > 0 and p1fail > 0 and p1solved > 0)
  if not (p1ok > 0 and p1fail > 0 and p1solved > 0):
    echo "  p1ok=", p1ok, " p1fail=", p1fail, " p1solved=", p1solved
  check("P2 spine-inversion roundtrip",
        forAll("p2", r, Cases, genSpineCase, propP2))
  check("P2 non-vacuous: some spines solved", p2ok > 0)
  check("P3 symmetry (<=1 flexible side)",
        forAll("p3", r, Cases, genPair, propP3))
  check("P3 non-vacuous", p3ok > 0 and p3fail > 0)
  check("P3 ground rigid-rigid symmetry",
        forAll("p3g", r, Cases,
               proc(r: var Rng): int = 0,
               proc(x: int): bool = propP3ground(r)))
  check("P4 occurs check",
        forAll("p4", r, Cases,
               proc(r: var Rng): int = 0,
               proc(x: int): bool = propP4(r)))
  check("P4 occurs check names noCycle under constructors", propP4noCycle())
  check("P5 duplicate-var spine rejected", propP5dup())
  check("P5 non-var spine rejected", propP5nonVar())
  check("P5 escaping variable rejected", propP5escape())
  check("P7 eta-positive: lam(x). r x =?= r",
        forAll("p7p", r, Cases,
               proc(r: var Rng): int = 0,
               proc(x: int): bool = propP7pos(r)))
  check("P7 eta-negative: lam(x). x =/= r",
        forAll("p7n", r, Cases,
               proc(r: var Rng): int = 0,
               proc(x: int): bool = propP7neg(r)))
  check("P7 eta-boundary: lam(x). r =/= r (x unused)",
        forAll("p7c", r, Cases,
               proc(r: var Rng): int = 0,
               proc(x: int): bool = propP7constNeg(r)))
  check("P8 noConfusion differential on ground ctor terms",
        forAll("p8", r, Cases,
               proc(r: var Rng): int = 0,
               proc(x: int): bool = propP8(r)))
  check("P8 non-vacuous: named noConfusion failures occur", p8named > 0)
  check("P9 reflexivity on ground terms",
        forAll("p9", r, Cases,
               proc(r: var Rng): int = 0,
               proc(x: int): bool = propP9(r)))
  check("P9 reflexivity on bare metas", propP9meta())
  check("flex-flex head-commitment characterization", propFlexOrder())

  if not allOk: quit(1)
  echo "all unifier properties pass at seed ", Seed
