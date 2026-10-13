## tests/pbt_usage.nim — Issue #163: property tests for the QTT usage-
## checking paths (src/eponym/usage_check.nim and the quantity algebra in
## src/eponym/preterm.nim).
##
## The quantity paths guard Eponym's linear/erased discipline: in-judgment
## enforcement (elab.enforceBinderQty, #66) and the post-elaboration backstop
## (checkUsage, #64) both count a binder's uses in *term* positions via
## countVarUses (binder domains and other type annotations are not uses —
## QTT types are checked in the all-0 context). qadd/qmul implement the
## quantity semiring on Quantity. Properties pin their extensional behavior:
##   P1 countVarUses-differential: countVarUses agrees with an independent
##      reference counter that materializes (idx, depth) occurrence pairs
##      for variables in term positions, then counts pairs with idx == depth.
##   P2 weaken-kills-uses (metamorphic): weakening shifts every free index
##      up by one, so countVarUses(weaken(t)) == 0 for any generated t.
##   P3 checkUsage-agreement: on lambdas whose bodies are built with exactly
##      n uses of the bound variable (flat and nested-binder variants),
##      checkUsage raises UsageError iff the quantity rule is violated
##      (q1: n != 1; q0: n > 0; qOmega: never).
##   P4 quantity-semiring: qadd is associative/commutative, qmul is
##      associative, q0 annihilates, q1 is the unit, and qmul distributes
##      over qadd — checked exhaustively (3 quantities, 27 combos).
##
## Run: nim c -r --hints:off --path:src --path:src/eponym tests/pbt_usage.nim
## Fixed seed 424242 in CI (change Seed locally for fresh fuzzing).

import pbt
import eponym_init  # Term, vv, tmLam/tmPi/tmApp/..., weaken, Const
import preterm       # Quantity, qadd, qmul
import usage_check   # countVarUses, checkUsage, UsageError
import sequtils

const Seed = 424242'u64
const Cases = 200

# --- generators -------------------------------------------------------------

proc pickQty(r: var Rng): Quantity =
  case r.below(3)
  of 0: q0
  of 1: q1
  else: qOmega

proc genTerm(r: var Rng, depth: int, maxVar: int): Term =
  ## Small core terms: variables (idx <= maxVar), binders with generated
  ## quantities, apps, pairs, projections, lets, absurd, literals.
  if depth <= 0:
    case r.below(5)
    of 0: tmInt(r.genInt(-2, 2))
    of 1: vv(r.below(maxVar + 1))
    of 2: tmNatLit(r.below(3))
    of 3: tmC(cStar)
    else: tmC(cOne)
  else:
    case r.below(9)
    of 0: tmApp(genTerm(r, depth - 1, maxVar), genTerm(r, depth - 1, maxVar))
    of 1: tmLam(tmC(cStar), "x", genTerm(r, depth - 1, maxVar + 1),
                qty = pickQty(r))
    of 2: tmPi(tmC(cStar), "x", genTerm(r, depth - 1, maxVar + 1),
               qty = pickQty(r))
    of 3: tmPair(genTerm(r, depth - 1, maxVar), genTerm(r, depth - 1, maxVar),
                 "p", genTerm(r, depth - 1, maxVar + 1))
    of 4: tmFst(genTerm(r, depth - 1, maxVar))
    of 5: tmSnd(genTerm(r, depth - 1, maxVar))
    of 6: tmLet(genTerm(r, depth - 1, maxVar), tmC(cStar), "y",
                genTerm(r, depth - 1, maxVar + 1))
    of 7: tmAbsurd(genTerm(r, depth - 1, maxVar))
    else: tmSi(tmC(cStar), "x", genTerm(r, depth - 1, maxVar + 1))

proc genJunk(r: var Rng, depth: int, minVar: int, maxVar: int): Term =
  ## Binder-free junk whose variables stay within [minVar, maxVar].
  ## With minVar = 1 the result mentions no vv(0); with minVar = 2 it
  ## mentions neither vv(0) nor vv(1).
  doAssert minVar >= 1 and maxVar >= minVar
  if depth <= 0:
    case r.below(3)
    of 0: tmInt(r.genInt(0, 5))
    of 1: vv(minVar + r.below(maxVar - minVar + 1))
    else: tmNatLit(r.below(4))
  else:
    if r.below(2) == 0:
      tmApp(genJunk(r, depth - 1, minVar, maxVar),
            genJunk(r, depth - 1, minVar, maxVar))
    else:
      genJunk(r, depth - 1, minVar, maxVar)

proc genKnownUseBody(r: var Rng, n: int, nested: bool): Term =
  ## A body whose countVarUses is *exactly* n, by construction:
  ## a left-nested app spine mixing n copies of the use-marker with
  ## junk that provably contains no marker. Flat variant: the marker is
  ## vv(0). Nested variant: the spine sits under one qOmega binder and
  ## the marker is vv(1) (the outer variable), so the count exercises
  ## the depth tracking — the inner vv(0) uses of the nested binder must
  ## not leak into the outer count.
  let (marker, lo, hi) =
    if nested: (vv(1), 2, 4) else: (vv(0), 1, 3)
  var leaves: seq[Term] = @[]
  for _ in 0 ..< n: leaves.add(marker)
  # One vv(0) under the nested binder: refers to the *inner* binder, not
  # the outer one; must not change the outer count.
  if nested: leaves.add(vv(0))
  let m = 1 + r.below(3)  # at least one junk leaf: leaves never empty
  for _ in 0 ..< m: leaves.add(genJunk(r, 2, lo, hi))
  for i in countdown(leaves.high, 1):
    let j = r.below(i + 1)
    swap(leaves[i], leaves[j])
  result = leaves[0]
  for i in 1 ..< leaves.len:
    result = tmApp(result, leaves[i])
  if nested:
    result = tmLam(tmC(cStar), "y", result, qty = qOmega)

# --- reference implementation (P1) ------------------------------------------

proc refOccurrences(t: Term, depth: int, acc: var seq[(int, int)]) =
  ## Collect (idx, depth) for every variable in term positions.
  ## Written as a materializing traversal, independent of countVarUses's
  ## direct recursive counter; the position rules (skip dom/letTy/primTy)
  ## are the same by design — the property pins that both implementations
  ## agree on them.
  case t.kind
  of tV: acc.add((t.idx, depth))
  of tLam, tPi, tSi:
    refOccurrences(t.scope.bdy, depth + 1, acc)  # dom is a type position
  of tApp:
    refOccurrences(t.fn, depth, acc)
    refOccurrences(t.arg, depth, acc)
  of tPair:
    refOccurrences(t.pFst, depth, acc)
    refOccurrences(t.pSnd, depth, acc)
    refOccurrences(t.pScope.bdy, depth + 1, acc)
  of tFst, tSnd, tAbsurd:
    refOccurrences(t.sub, depth, acc)
  of tLet:
    refOccurrences(t.letVal, depth, acc)
    refOccurrences(t.letScope.bdy, depth + 1, acc)  # letTy is a type position
  of tPrim, tR, tC, tMeta, tInt, tNatLit:
    discard

proc refCountVarUses(t: Term): int =
  var occs: seq[(int, int)] = @[]
  refOccurrences(t, 0, occs)
  occs.countIt(it[0] == it[1])

# --- shrinking --------------------------------------------------------------

proc shrinkTerm(t: Term): seq[Term] =
  ## Shrink toward smaller terms: subterms first, then tmInt(0).
  result = @[tmInt(0)]
  case t.kind
  of tV, tR, tC, tInt, tNatLit: discard
  of tMeta: result.add(t.metaSpine)
  of tLam, tPi, tSi:
    result.add(t.dom)
    result.add(t.scope.bdy)
  of tApp:
    result.add(t.fn)
    result.add(t.arg)
  of tPair:
    result.add(t.pFst)
    result.add(t.pSnd)
    result.add(t.pScope.bdy)
  of tFst, tSnd, tAbsurd:
    result.add(t.sub)
  of tLet:
    result.add(t.letVal)
    result.add(t.letTy)
    result.add(t.letScope.bdy)
  of tPrim:
    result.add(t.primTy)

# --- P3: known-count lambda cases -------------------------------------------

type QtyCase = object
  qty: Quantity
  n: int
  term: Term

proc genQtyCase(r: var Rng, nested: bool): QtyCase =
  let q = pickQty(r)
  let n = r.below(4)  # 0..3 uses
  let body = genKnownUseBody(r, n, nested)
  QtyCase(qty: q, n: n, term: tmLam(tmC(cStar), "x", body, qty = q))

proc expectedRaises(q: Quantity, n: int): bool =
  ## The quantity rule checkUsage enforces.
  case q
  of q1: n != 1
  of q0: n > 0
  of qOmega: false

proc checkUsageRaises(t: Term): bool =
  try:
    checkUsage(t)
    false
  except UsageError:
    true

proc shrinkQtyCase(c: QtyCase): seq[QtyCase] =
  result = @[]
  for t in shrinkTerm(c.term):
    result.add(QtyCase(qty: c.qty, n: c.n, term: t))

# --- P4: quantity semiring, exhaustive ---------------------------------------

const AllQty = [q0, q1, qOmega]

proc checkSemiring(): bool =
  for a in AllQty:
    for b in AllQty:
      for c in AllQty:
        if qadd(a, b) != qadd(b, a):  # commutative
          echo "qadd not commutative: ", a, " ", b; return false
        if qadd(qadd(a, b), c) != qadd(a, qadd(b, c)):  # associative
          echo "qadd not associative: ", a, " ", b, " ", c; return false
        if qmul(qmul(a, b), c) != qmul(a, qmul(b, c)):  # associative
          echo "qmul not associative: ", a, " ", b, " ", c; return false
        if qmul(a, qadd(b, c)) != qadd(qmul(a, b), qmul(a, c)):  # distributes
          echo "qmul does not distribute: ", a, " ", b, " ", c; return false
      if qadd(q0, a) != a or qadd(a, q0) != a:  # q0 is the additive unit
        echo "q0 not additive unit: ", a; return false
      if qmul(q0, a) != q0 or qmul(a, q0) != q0:  # q0 annihilates
        echo "q0 does not annihilate: ", a; return false
      if qmul(q1, a) != a or qmul(a, q1) != a:  # q1 is the multiplicative unit
        echo "q1 not multiplicative unit: ", a; return false
  true

# --- main --------------------------------------------------------------------

when isMainModule:
  var r = initRng(Seed)
  var allOk = true

  allOk = forAll("countVarUses-differential", r, Cases,
    proc(r: var Rng): Term = genTerm(r, 4, 2),
    proc(t: Term): bool = countVarUses(t) == refCountVarUses(t),
    shrinkTerm) and allOk

  allOk = forAll("weaken-kills-uses", r, Cases,
    proc(r: var Rng): Term = genTerm(r, 4, 2),
    proc(t: Term): bool = countVarUses(weaken(t)) == 0,
    shrinkTerm) and allOk

  allOk = forAll("checkUsage-agreement-flat", r, Cases,
    proc(r: var Rng): QtyCase = genQtyCase(r, nested = false),
    proc(c: QtyCase): bool =
      checkUsageRaises(c.term) == expectedRaises(c.qty, c.n),
    shrinkQtyCase) and allOk

  allOk = forAll("checkUsage-agreement-nested", r, Cases,
    proc(r: var Rng): QtyCase = genQtyCase(r, nested = true),
    proc(c: QtyCase): bool =
      checkUsageRaises(c.term) == expectedRaises(c.qty, c.n),
    shrinkQtyCase) and allOk

  echo "quantity semiring laws (exhaustive, 3^3 combos):"
  if checkSemiring():
    echo "ok [quantity-semiring]: 27 combos"
  else:
    allOk = false

  if not allOk: quit(1)
  echo "pbt_usage: all properties passed"
