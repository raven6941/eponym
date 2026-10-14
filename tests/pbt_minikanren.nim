## tests/pbt_minikanren.nim — Issue #163: property tests for the Track C
## relational engine (src/experimental/relational/minikanren.nim).
##
## The engine is an explicit-stream miniKanren: goals are State -> Stream
## procs, `take` processes the stream tree with an explicit worklist, and
## `run` reifies the query variable. Properties pin the answer-set contract:
##   P1 answer-soundness:  every answer state of a generated goal satisfies
##                         that goal (re-running it on the state succeeds).
##   P2 eq-identity:       run(q, q==t) reifies to exactly @[t] for ground t.
##   P3 diseq-semantics:   run(q, (q==t1) & (q=/=t2)) is nonempty iff t1 != t2.
##   P4 disj-soundness:    each answer of disj(g1,g2) satisfies g1 or g2.
##   P5 disj-commutes:     answers of disj(g1,g2) and disj(g2,g1) agree as
##                         multisets (interleaving changes order, not content).
##   P6 setEqo-soundness:  setEqo + branchMostConstrained reifies the cells
##                         to a permutation of the given values in every answer.
##   P7 setEqo-completeness: with k distinct values (k<=3 in the suite) there
##                         are exactly k! answers. This pins the enumerator's
##                         completeness deliberately: a pruning optimization
##                         that drops assignments must update this property.
##
## Run: nim c -r --hints:off --path:src --path:src/eponym \
##        --path:src/experimental --path:src/experimental/relational --path:src/experimental/staging tests/pbt_minikanren.nim
## Fixed seed 424242 in CI (change Seed locally for fresh fuzzing).

import pbt
import minikanren
import sequtils
import strutils
import algorithm

const Seed = 424242'u64
const Cases = 200

# --- generators -------------------------------------------------------------

proc genGround(r: var Rng, depth: int): RTerm =
  ## Small ground terms: atoms a/b/c, ints 0..2, nil, pairs (depth-bounded).
  if depth <= 0 or r.below(3) == 0:
    case r.below(5)
    of 0: ratom("a")
    of 1: ratom("b")
    of 2: ratom("c")
    of 3: rint(r.below(3))
    else: rnil()
  else:
    rpair(genGround(r, depth - 1), genGround(r, depth - 1))

proc shrinkRTerm(t: RTerm): seq[RTerm] =
  ## Shrink toward smaller ground terms: pairs drop a side, int atoms
  ## shrink the int.
  result = @[]
  case t.kind
  of rkPair:
    result.add(t.head)
    result.add(t.tail)
  of rkAtom:
    try:
      let n = parseInt(t.name)
      for c in shrinkInt(n): result.add(ratom($c))
    except ValueError:
      discard
  of rkVar:
    discard

proc genAtomicGoal(r: var Rng, q: RTerm): Goal =
  ## An atomic goal over q: unification with, or disequality from, a
  ## generated ground term.
  let t = genGround(r, 2)
  if r.genBool(): `==`(q, t) else: `=/=`(q, t)

proc genGoal(r: var Rng, q: RTerm): Goal =
  ## Small generated goals: atomic, conjunction, or disjunction of two.
  let g1 = genAtomicGoal(r, q)
  if r.below(3) == 0: return g1
  let g2 = genAtomicGoal(r, q)
  if r.genBool(): conj(g1, g2) else: disj(g1, g2)

proc genGroundBinding(r: var Rng, q: RTerm): Goal =
  ## A disjunct that always binds q to a ground term (so answers reify
  ## ground and P5's multiset comparison is meaningful).
  `==`(q, genGround(r, 2))

proc listElems(t: RTerm): seq[RTerm] =
  ## Flatten an rlist-style (a b ... . nil) term into its elements.
  var cur = t
  while cur.kind == rkPair:
    result.add(cur.head)
    cur = cur.tail

proc isPermutation(elems, vals: seq[RTerm]): bool =
  if elems.len != vals.len: return false
  var rem = vals.mapIt($it)
  for e in elems:
    let i = rem.find($e)
    if i < 0: return false
    rem.del(i)
  rem.len == 0

proc fact(n: int): int =
  result = 1
  for i in 2 .. n: result *= i

# --- the suite --------------------------------------------------------------

proc `$`(g: Goal): string = "<goal>"  # closures can't be printed; the case
                                      # index in the FAIL line locates the input

let q = rvar(0)
var r = initRng(Seed)
var allOk = true

# P1: answer-soundness — every answer state satisfies the goal that produced it.
allOk = forAll("P1 answer-soundness", r, Cases,
  proc(r: var Rng): Goal = genGoal(r, q),
  proc(g: Goal): bool =
    for s in take(30, g(emptyState())):
      if take(1, g(s)).len != 1: return false
    true) and allOk

# P2: eq-identity — run(q, q==t) reifies to exactly @[t].
allOk = forAll("P2 eq-identity", r, Cases,
  proc(r: var Rng): RTerm = genGround(r, 2),
  proc(t: RTerm): bool = run(q, `==`(q, t), 10).mapIt($it) == @[$t],
  shrinkRTerm) and allOk

# P3: diseq-semantics — (q==t1) & (q=/=t2) succeeds iff t1 != t2.
allOk = forAll("P3 diseq-semantics", r, Cases,
  proc(r: var Rng): (RTerm, RTerm) = (genGround(r, 2), genGround(r, 2)),
  proc(ts: (RTerm, RTerm)): bool =
    let ans = run(q, conj(`==`(q, ts[0]), `=/=`(q, ts[1])), 10)
    ans.len == (if $ts[0] != $ts[1]: 1 else: 0)) and allOk

# P4: disj-soundness — each answer of disj(g1,g2) satisfies g1 or g2.
allOk = forAll("P4 disj-soundness", r, Cases,
  proc(r: var Rng): (Goal, Goal) =
    (genGroundBinding(r, q), genGroundBinding(r, q)),
  proc(gs: (Goal, Goal)): bool =
    let g = disj(gs[0], gs[1])
    for s in take(30, g(emptyState())):
      if take(1, gs[0](s)).len == 0 and take(1, gs[1](s)).len == 0:
        return false
    true) and allOk

# P5: disj-commutes — interleaving order changes, answer multiset does not.
allOk = forAll("P5 disj-commutes", r, Cases,
  proc(r: var Rng): (Goal, Goal) =
    (genGroundBinding(r, q), genGroundBinding(r, q)),
  proc(gs: (Goal, Goal)): bool =
    let fwd = run(q, disj(gs[0], gs[1]), 100).mapIt($it).sorted()
    let rev = run(q, disj(gs[1], gs[0]), 100).mapIt($it).sorted()
    fwd == rev) and allOk

# P6/P7: setEqo — soundness (cells reify to a permutation of the values)
# and completeness (exactly k! answers for k distinct values).
allOk = forAll("P6/P7 setEqo soundness+completeness", r, 100,
  proc(r: var Rng): seq[RTerm] =
    var vals: seq[RTerm] = @[]
    for _ in 0 ..< r.genInt(1, 3):
      let v = rint(r.below(3))
      if vals.allIt($it != $v): vals.add(v)
    if vals.len == 0: vals.add(rint(0))
    vals,
  proc(vals: seq[RTerm]): bool =
    let cells = @[rvar(1), rvar(2), rvar(3)][0 ..< vals.len]
    let g = conj(setEqo(cells, vals), branchMostConstrained(cells))
    let ans = run(rlist(cells), g, 100)
    if ans.len != fact(vals.len): return false
    for a in ans:
      if not isPermutation(listElems(a), vals): return false
    true) and allOk

if not allOk:
  echo "--- property failures (seed ", Seed, ") ---"
  quit(1)
echo "--- all minikanren properties hold ---"
