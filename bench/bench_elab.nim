## Benchmark: direct elaborator vs relational elaborator (unstaged)
##
## Measures wall-clock for both on the fragment corpus.

import minikanren
import rel_elab_dep
import elab
import times

proc benchDirect(src: string, iters: int): float =
  let t0 = cpuTime()
  for i in 0 ..< iters:
    try:
      discard elabCheck(src)
    except ElabError:
      discard
  let t1 = cpuTime()
  (t1 - t0) / float(iters) * 1000.0  # ms per iteration

proc benchRelational(tm, ty: RTerm, iters: int): float =
  let t0 = cpuTime()
  for i in 0 ..< iters:
    let g = checko(tm, ty, rnil())
    discard run(freshVar(), g, 1)
  let t1 = cpuTime()
  (t1 - t0) / float(iters) * 1000.0  # ms per iteration

when isMainModule:
  const Iters = 100

  # Test: cons(zero, nil) : Vec(Nat, suc(zero))
  let src = """data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc t : Vec Nat (suc zero) =
  cons Nat zero zero (nil Nat)
"""
  let tm = consTm(zeroTm(), nilTm())
  let ty = vecTy(natTy(), sucTm(zeroTm()))

  let dTime = benchDirect(src, Iters)
  let rTime = benchRelational(tm, ty, Iters)

  echo "Direct elaborator: ", dTime, " ms/iter"
  echo "Relational (unstaged): ", rTime, " ms/iter"
  echo "Ratio (relational/direct): ", rTime / dTime, "x"
