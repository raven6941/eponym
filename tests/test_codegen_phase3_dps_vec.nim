## Differential tests + benchmark for Phase-3 destination-passing folds
## (issue #331): cons-rebuild `vecElim` folds compile to a single
## preallocated destination instead of per-step `@[x] & acc` allocation.
##
## Uses the shared `differentialBlockRepr` driver
## (`tests/codegen_phase2_differential.nim`): each repr proc is checked
## against the interpreter (`callValueFuncDir`) and against its Phase-1
## compiled twin, then benchmarked per #19's framing (Phase 3 against
## Phase 1's compiled output; the Phase 3 vs Phase 2 delta is algorithmic
## — one allocation and O(n) writes vs O(n) allocations and O(n^2)
## copies — and was measured once during development, see #331). Benchmarks:
## `vmapDps` 2076.6x, `vappendDps` 18831.1x (n=50; Phase-1 side dominated by
## Value-level `natAdd` per cons step — the index the repr tier skips as
## type-level), `lmapDps` 1689.2x vs Phase 1.

import std/[sequtils, times]
import codegen_phase2_differential

const prog = """postulate Int : Type 0
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : Type 0) : Nat -> Type 0 where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc natAdd (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) n (lam (p : Nat). lam (ih : Nat). suc ih) m
proc vappendDps (m : Nat) (n : Nat) (xs : Vec Int m) (ys : Vec Int n)
    : Vec Int (natAdd m n) =
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Vec Int (natAdd i n))
            ys
            (lam (i : Nat). lam (x : Int). lam (xs2 : Vec Int i).
              lam (ih : Vec Int (natAdd i n)).
                cons Int (natAdd i n) x ih)
            m xs
proc vmapDps (n : Nat) (xs : Vec Int n) : Vec Int n =
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Vec Int i)
            (nil Int)
            (lam (i : Nat). lam (x : Int). lam (xs2 : Vec Int i).
              lam (ih : Vec Int i). cons Int i (addInt x x) ih)
            n xs
proc vmapLin (n : Nat) (1 xs : Vec Int n) : Vec Int n =
  ## Explicit quantity-1 on the input: the DPS fold must compose with
  ## declared linearity (the cons-case `ih` stays inferred).
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Vec Int i)
            (nil Int)
            (lam (i : Nat). lam (x : Int). lam (xs2 : Vec Int i).
              lam (ih : Vec Int i). cons Int i (addInt x x) ih)
            n xs
proc vlenDps (n : Nat) (xs : Vec Int n) : Nat =
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Nat)
            zero
            (lam (i : Nat). lam (x : Int). lam (xs2 : Vec Int i).
              lam (ih : Nat). suc ih)
            n xs
"""

differentialBlockRepr(prog, currentSourcePath(), "Int:int,Nat:int,Vec:vector")

let dpsGlobals = getGlobals(prog)

proc intEnc(x: int, g: Globals): Value = intToValue(x)
proc intDec(v: Value, g: Globals): int = valueToInt(v)

proc vecArg(items: seq[int]): Value =
  seqToVecValue(items, items.len, dpsGlobals, "Vec", intEnc)

proc natArg(n: int): Value = natToValue(n, dpsGlobals)

proc checkVecVec(name: string, args: seq[Value], expected: seq[int],
                 reprCall: proc(): seq[int]) =
  let got = reprCall()
  expect(got == expected, name & " repr computes " & $expected)
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, args, bnd)
  let n = expected.len
  expect(vecValueToSeq[int](want, n, dpsGlobals, "Vec", intDec) == expected,
    name & " interpreter agrees")
  let got1 = case name
    of "vappendDps": eponymCompiled_vappendDps(args, bnd)
    of "vmapDps": eponymCompiled_vmapDps(args, bnd)
    of "vmapLin": eponymCompiled_vmapLin(args, bnd)
    else: raise newException(ValueError, "unknown phase-1 def " & name)
  expect(vecValueToSeq[int](got1, n, dpsGlobals, "Vec", intDec) == expected,
    name & " phase-1 agrees")

for (xs, ys) in [(@[1, 2], @[3]), (@[], @[4, 5]), (@[1], @[]),
                 (@[1, 2, 3], @[4, 5, 6, 7])]:
  let want = xs & ys
  checkVecVec("vappendDps",
    @[natArg(xs.len), natArg(ys.len), vecArg(xs), vecArg(ys)], want,
    proc(): seq[int] =
      eponymCompiledRepr_vappendDps(xs.len, ys.len, xs, ys))

for xs in [@[], @[1], @[3, -2, 7], @[1, 2, 3, 4, 5]]:
  let n = xs.len
  let want = xs.mapIt(it * 2)
  checkVecVec("vmapDps", @[natArg(n), vecArg(xs)], want,
    proc(): seq[int] = eponymCompiledRepr_vmapDps(n, xs))
  checkVecVec("vmapLin", @[natArg(n), vecArg(xs)], want,
    proc(): seq[int] = eponymCompiledRepr_vmapLin(n, xs))

for xs in [@[], @[1], @[3, -2, 7], @[1, 2, 3, 4, 5]]:
  let n = xs.len
  let bnd = testPostulateBindings()
  let args = @[natArg(n), vecArg(xs)]
  expect(eponymCompiledRepr_vlenDps(n, xs) == n, "vlenDps repr computes " & $n)
  let want = callValueFuncDir("", prog, "vlenDps", args, bnd)
  expect(valueToNat(want, dpsGlobals) == n, "vlenDps interpreter agrees")
  let got1 = eponymCompiled_vlenDps(args, bnd)
  expect(valueToNat(got1, dpsGlobals) == n, "vlenDps phase-1 agrees")

for name in ["vappendDps", "vmapDps", "vmapLin", "vlenDps"]:
  expect(name in reprCompiledNames(), name & " has a repr proc")

# --- benchmark: Phase-1 compiled vs Phase-3 DPS repr (per #19's framing) ---
# The interpreter is context only (differential agreement is checked
# above); the comparison that matters is Phase 3 against Phase 1.
block:
  const iters = 20_000
  const n = 50
  let xs = toSeq(1 .. n)
  let argV = @[natArg(n), vecArg(xs)]
  let bnd = testPostulateBindings()
  var t0 = cpuTime()
  var acc1 = 0
  for i in 0 ..< iters:
    let v = eponymCompiled_vmapDps(argV, bnd)
    acc1 += vecValueToSeq[int](v, n, dpsGlobals, "Vec", intDec).len
  let tPhase1 = cpuTime() - t0
  t0 = cpuTime()
  var acc2 = 0
  for i in 0 ..< iters:
    acc2 += eponymCompiledRepr_vmapDps(n, xs).len
  let tPhase3 = cpuTime() - t0
  expect(acc1 == acc2, "vmapDps accumulators agree")
  echo "bench vmapDps x", iters, " (n=", n, "): phase-1 ",
    tPhase1.formatFloat(ffDecimal, 3), "s | phase-3 ",
    tPhase3.formatFloat(ffDecimal, 3), "s; phase-3 vs phase-1 ",
    (tPhase1 / tPhase3).formatFloat(ffDecimal, 1), "x"

block:
  const iters = 1_000
  const n = 50
  let xs = toSeq(1 .. n)
  let bnd = testPostulateBindings()
  var t0 = cpuTime()
  var acc1 = 0
  for i in 0 ..< iters:
    let v = eponymCompiled_vappendDps(
      @[natArg(n), natArg(n), vecArg(xs), vecArg(xs)], bnd)
    acc1 += vecValueToSeq[int](v, 2 * n, dpsGlobals, "Vec", intDec).len
  let tPhase1 = cpuTime() - t0
  t0 = cpuTime()
  var acc2 = 0
  for i in 0 ..< iters:
    acc2 += eponymCompiledRepr_vappendDps(n, n, xs, xs).len
  let tPhase3 = cpuTime() - t0
  expect(acc1 == acc2, "vappendDps accumulators agree")
  echo "bench vappendDps x", iters, " (n=", n, "): phase-1 ",
    tPhase1.formatFloat(ffDecimal, 3), "s | phase-3 ",
    tPhase3.formatFloat(ffDecimal, 3), "s; phase-3 vs phase-1 ",
    (tPhase1 / tPhase3).formatFloat(ffDecimal, 1), "x"

echo "all Phase 3 DPS Vec codegen differential checks passed"
