## tests/pbt_egraph.nim — Issue #163: property tests for the e-graph
## conversion cache (Experiment 10, src/eponym/egraph.nim).
##
## The cache is a memo table over conversion goals: `merge` records a
## goal NbE proved; `areEqualCached` probes. Properties pin the public
## contract:
##   P1 merge-then-hit:    a merged key always probes (true, true).
##   P2 fresh-miss:        an unmerged key probes (false, false).
##   P3 merge-idempotent:  merging twice is a no-op (merges counts once).
##   P4 stats-accounting:  hits + misses == number of probes.
##   P5 key-order-pinning: the memo key is order-sensitive —
##                         convKey(l, a, b) != convKey(l, b, a) for
##                         distinct-hash terms, so a swapped probe misses.
##                         This pins the current construction deliberately:
##                         canonicalizing the key (a real hit-rate
##                         improvement) must update this property.
##
## Run: nim c -r --hints:off --path:src --path:src/eponym \
##        --path:src/relational --path:src/staging tests/pbt_egraph.nim
## Fixed seed 424242 in CI (change Seed locally for fresh fuzzing).

import pbt
import egraph
import eponym_init
import hashes

const Seed = 424242'u64
const Cases = 300

proc genKey(r: var Rng): ConvKey =
  ## Hash is a distinct int: mask the generator output into int64 range.
  (r.below(4), Hash(cast[int64](r.next() shr 1)),
   Hash(cast[int64](r.next() shr 1)))

let star = Term(kind: tC, c: cStar)
let one = Term(kind: tC, c: cOne)
doAssert hashTerm(star) != hashTerm(one),
  "test premise: distinct terms must have distinct hashes"

var r = initRng(Seed)
var allOk = true

allOk = forAll("P1 merge-then-hit", r, Cases, genKey,
  proc(k: ConvKey): bool =
    var g = initEGraph()
    merge(g, k)
    areEqualCached(g, k) == (true, true),
  shrinkConvKey) and allOk

allOk = forAll("P2 fresh-miss", r, Cases, genKey,
  proc(k: ConvKey): bool =
    var g = initEGraph()
    areEqualCached(g, k) == (false, false),
  shrinkConvKey) and allOk

allOk = forAll("P3 merge-idempotent", r, Cases, genKey,
  proc(k: ConvKey): bool =
    var g = initEGraph()
    merge(g, k)
    merge(g, k)
    merge(g, k)
    g.merges == 1 and areEqualCached(g, k) == (true, true),
  shrinkConvKey) and allOk

allOk = forAll("P4 stats-accounting", r, Cases,
  proc(r: var Rng): seq[ConvKey] = genSeq(r, 8, genKey),
  proc(ks: seq[ConvKey]): bool =
    var g = initEGraph()
    for k in ks: merge(g, k)
    for k in ks: discard areEqualCached(g, k)
    g.hits + g.misses == ks.len) and allOk

# P5: pin the order-sensitive key construction. Uses real terms through
# convKey so a future canonicalization shows up here.
block:
  let kab = convKey(2, star, one)
  let kba = convKey(2, one, star)
  if kab == kba:
    echo "FAIL [P5 key-order-pinning]: swapped key equals original; " &
      "expected order-sensitive construction"
    allOk = false
  else:
    var g = initEGraph()
    merge(g, kab)
    let (hit, _) = areEqualCached(g, kba)
    if hit:
      echo "FAIL [P5 key-order-pinning]: swapped probe hit without merge"
      allOk = false
    else:
      echo "ok [P5 key-order-pinning]: swapped key misses (pinned)"

if not allOk:
  echo "--- property failures (seed ", Seed, ") ---"
  quit(1)
echo "--- all egraph properties hold ---"
