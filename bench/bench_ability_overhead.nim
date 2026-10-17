## Issue #177: elaboration-time overhead of ambient-ability threading on
## pure code (the opt-in promise: pure programs pay nothing measurable).
##
## Elaborates a fixed pure corpus (Nat, Vec, append, map, several uses —
## exercises global uses with per-use peg freshening, App-site peg checks,
## and Pi peg stamping) N times and reports ms/iteration. Run the same
## binary built from main for the before/after comparison.
##
## Usage: nim c -r --hints:off $P bench/bench_ability_overhead.nim

import elab
import times

const corpus = """
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : Type 0) : Nat -> Type 0 where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc constNat (x : Nat) (y : Nat) : Nat = x
proc t1 : Vec Nat (suc (suc zero)) =
  cons Nat (suc zero) zero (cons Nat zero zero (nil Nat))
proc t2 : Vec Nat (suc zero) =
  cons Nat zero zero (nil Nat)
proc useConst : Nat =
  constNat (suc zero) (constNat zero (suc zero))
proc polyId (A : Type 0) (x : A) : A = x
proc usePoly : Nat =
  polyId Nat (polyId Nat (suc zero))
"""

when isMainModule:
  const Iters = 60
  # warmup (module init, caches)
  for i in 0 ..< 3: discard elabCheck(corpus)
  let t0 = cpuTime()
  for i in 0 ..< Iters: discard elabCheck(corpus)
  let t1 = cpuTime()
  echo "ability-overhead corpus: ", (t1 - t0) / float(Iters) * 1000.0, " ms/iter"
