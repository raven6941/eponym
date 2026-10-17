## Issue #4: honest conversion-cache measurement.
##
## Elaborates the Nat prelude + nat_lemmas corpus (the heaviest realistic
## elaboration target: #55 attributes ~88% of elaboration time to it) once
## with the default conversion and once with `cacheConvHandler` installed,
## and reports wall-clock alongside cache probes/hits. A 1.0x with 0 hits
## and a 1.0x with 90% hits are very different findings — the counters are
## the "honest" part.
##
## Run: nim c --hints:off --path:src --path:src/eponym -r tests/bench_conv_cache.nim
## (paths follow tools/ci-local.sh's $P flags)

import std/[times, strformat, strutils]
import elab
import parse_surf

proc runOnce(src: string, useCache: bool): tuple[secs: float, probes, hits: int, decls: int] =
  let handlers = if useCache: @[cacheConvHandler()] else: @[]
  var drv = initModuleDriver(handlers)
  let t0 = cpuTime()
  let defs =
    if src.endsWith(".ep"): drv.elabFile(src)
    else: drv.elabDeclsDir(parseProgram(src), ".", "<bench>")
  let t1 = cpuTime()
  (t1 - t0, drv.ms.convCacheProbes, drv.ms.convCacheHits, defs.len)

const vecCorpus = """
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
data Vec (A : Type 0) : Nat -> Type 0 where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
def vappend : Pi {A : Type 0}. Pi {m : Nat}. Pi {n : Nat}. Vec A m -> Vec A n
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

proc bench(label, src: string) =
  discard runOnce(src, false)  # warmup
  var plain, cached: seq[tuple[secs: float, probes, hits: int, decls: int]]
  for _ in 0 ..< 3: plain.add runOnce(src, false)
  for _ in 0 ..< 3: cached.add runOnce(src, true)
  assert plain[0].decls == cached[0].decls, "cache changed elaborated output"
  let pMin = min(plain[0].secs, min(plain[1].secs, plain[2].secs))
  let cMin = min(cached[0].secs, min(cached[1].secs, cached[2].secs))
  let probes = cached[0].probes
  let hits = cached[0].hits
  let hitRate = if probes > 0: 100.0 * hits.float / probes.float else: 0.0
  echo &"[{label}] {plain[0].decls} decls, best of 3:"
  echo &"  default: {pMin:.3f}s   cache: {cMin:.3f}s   speedup: {pMin / cMin:.2f}x"
  echo &"  probes={probes} hits={hits} hit-rate={hitRate:.1f}%"

proc main() =
  bench("prelude", "lib/nat_lemmas.ep")
  bench("vec", vecCorpus)

when isMainModule:
  main()
