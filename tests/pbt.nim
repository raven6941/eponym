## tests/pbt.nim — Issue #163: shared property-based testing harness.
##
## Why a house harness instead of a nimble PBT library: the only Nim
## PBT library (alehander92/nim-quicktest) is an unmaintained 2017
## alpha whose macros do not compile on the current toolchain (Nim
## 2.2.12; invalid indentation at quicktest.nim:5, plus dead imports of
## `future`/`breeze`), and nimble's package index is unreachable from
## this environment. The repo already has a house pattern — seeded
## xorshift64* RNG, deterministic across platforms, fixed seed in CI —
## used by tests/fuzz_soundness.nim and tests/adequacy_props.nim; this
## module codifies it so new property suites share generators,
## shrinking, and failure reporting.
##
## Usage:
##   import pbt
##   var r = initRng(Seed)
##   let ok = forAll("merge-then-hit", r, 200,
##     proc(r: var Rng): ConvKey = genConvKey(r),
##     proc(k: ConvKey): bool =
##       var g = initEGraph(); merge(g, k); areEqualCached(g, k) == (true, true))
##   if not ok: quit(1)

import hashes

type
  Rng* = object
    s: uint64

proc initRng*(seed: uint64): Rng =
  var s = seed
  if s == 0: s = 0x9E3779B97F4A7C15'u64
  Rng(s: s)

proc next*(r: var Rng): uint64 =
  ## xorshift64*: deterministic across platforms.
  var x = r.s
  x = x xor (x shr 12)
  x = x xor (x shl 25)
  x = x xor (x shr 27)
  r.s = x
  x * 0x2545F4914F6CDD1D'u64

proc below*(r: var Rng, n: int): int =
  ## Int in [0, n). Modulo bias is irrelevant for property testing.
  doAssert n > 0, "below: n must be positive"
  (r.next() mod n.uint64).int

proc genBool*(r: var Rng): bool =
  r.next() mod 2 == 0

proc genInt*(r: var Rng, lo, hi: int): int =
  ## Int in [lo, hi] inclusive.
  doAssert lo <= hi, "genInt: lo > hi"
  lo + r.below(hi - lo + 1)

proc genSeq*[T](r: var Rng, maxLen: int, gen: proc(r: var Rng): T): seq[T] =
  let n = r.below(maxLen + 1)
  result = newSeq[T](n)
  for i in 0 ..< n:
    result[i] = gen(r)

proc shrinkInt*(x: int): seq[int] =
  ## Shrink candidates for an int, most-aggressive first: 0, then the
  ## immediate neighbor toward 0, then halving toward 0. The neighbor
  ## step gives true minimality for threshold properties (e.g. x <= 7
  ## shrinks to exactly 8); halving covers the large-magnitude jumps.
  result = @[]
  if x != 0: result.add(0)
  if x > 0: result.add(x - 1)
  elif x < 0: result.add(x + 1)
  var v = x div 2
  while v != 0 and v != x:
    if v notin result: result.add(v)
    v = v div 2

proc shrinkConvKey*(k: (int, Hash, Hash)): seq[(int, Hash, Hash)] =
  ## Shrink a conversion-cache key toward (0, 0, 0).
  result = @[(0, Hash(0), Hash(0))]
  if k[0] != 0: result.add((0, k[1], k[2]))
  if k[1] != Hash(0): result.add((k[0], Hash(0), k[2]))
  if k[2] != Hash(0): result.add((k[0], k[1], Hash(0)))

proc forAll*[T](name: string, r: var Rng, n: int,
                gen: proc(r: var Rng): T,
                prop: proc(x: T): bool,
                shrink: proc(x: T): seq[T] = nil): bool =
  ## Run `prop` on `n` generated inputs. On the first failure, shrink
  ## (if a shrinker is given) and print the seed + minimal case, then
  ## return false. Returns true iff all cases pass.
  result = true
  for i in 0 ..< n:
    let x = gen(r)
    var failed = false
    try:
      failed = not prop(x)
    except CatchableError as e:
      echo "FAIL [", name, "]: exception on input: ", e.msg
      failed = true
    if failed:
      result = false
      var minimal = x
      if shrink != nil:
        var cands = shrink(minimal)
        while cands.len > 0:
          var progressed = false
          for c in cands:
            var cf = false
            try: cf = not prop(c)
            except CatchableError: cf = true
            if cf:
              minimal = c
              cands = shrink(minimal)
              progressed = true
              break
          if not progressed: break
      echo "FAIL [", name, "]: case ", i, ", minimal input: ", $minimal
      return false
  echo "ok [", name, "]: ", n, " cases"
