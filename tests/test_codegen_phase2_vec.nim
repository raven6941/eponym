## Differential tests + benchmark for the Phase 2 representation backend
## (Issue #330 v3: `Vec` as `seq[int]`).
##
## Uses the shared `differentialBlockRepr` driver
## (`tests/codegen_phase2_differential.nim`): each repr proc is checked
## against the interpreter (`callValueFuncDir`) and against its Phase-1
## compiled twin, then benchmarked per #19's framing (Phase 2 against
## Phase 1's compiled output).

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
proc vmapDouble (n : Nat) (xs : Vec Int n) : Vec Int n =
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Vec Int i)
            (nil Int)
            (lam (i : Nat). lam (x : Int). lam (xs2 : Vec Int i).
              lam (ih : Vec Int i). cons Int i (addInt x x) ih)
            n xs
proc vlength (n : Nat) (xs : Vec Int n) : Nat =
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Nat)
            zero
            (lam (i : Nat). lam (x : Int). lam (xs2 : Vec Int i).
              lam (ih : Nat). suc ih)
            n xs
proc vheadOr (n : Nat) (xs : Vec Int n) (d : Int) : Int =
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Int)
            d
            (lam (i : Nat). lam (x : Int). lam (xs2 : Vec Int i).
              lam (ih : Int). x)
            n xs
proc vappend (m : Nat) (n : Nat) (xs : Vec Int m) (ys : Vec Int n)
    : Vec Int (natAdd m n) =
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Vec Int (natAdd i n))
            ys
            (lam (i : Nat). lam (x : Int). lam (xs2 : Vec Int i).
              lam (ih : Vec Int (natAdd i n)).
                cons Int (natAdd i n) x ih)
            m xs
proc vconsStep (i : Nat) (x : Int) (xs2 : Vec Int i) (ih : Vec Int i)
    : Vec Int (suc i) =
  cons Int i x ih
proc vmapId (n : Nat) (xs : Vec Int n) : Vec Int n =
  vecElim Int (lam (i : Nat). lam (v : Vec Int i). Vec Int i)
            (nil Int) vconsStep n xs
"""

differentialBlockRepr(prog, currentSourcePath(), "Int:int,Nat:int,Vec:vector")

let vecGlobals = getGlobals(prog)

proc intEnc(x: int, g: Globals): Value = intToValue(x)
proc intDec(v: Value, g: Globals): int = valueToInt(v)

proc vecArg(items: seq[int]): Value =
  seqToVecValue(items, items.len, vecGlobals, "Vec", intEnc)

proc natArg(n: int): Value = natToValue(n, vecGlobals)

proc checkVecVec(name: string, args: seq[Value], expected: seq[int],
                 reprCall: proc(): seq[int]) =
  ## Repr proc (called via `reprCall`) vs literal expectation, vs the
  ## interpreter, vs the Phase-1 compiled proc (Vec results decoded with
  ## `vecValueToSeq`).
  let got = reprCall()
  expect(got == expected, name & " repr computes " & $expected)
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, args, bnd)
  let n = expected.len
  expect(vecValueToSeq[int](want, n, vecGlobals, "Vec", intDec) == expected,
    name & " interpreter agrees")
  let got1 = case name
    of "vmapDouble": eponymCompiled_vmapDouble(args, bnd)
    of "vappend": eponymCompiled_vappend(args, bnd)
    of "vmapId": eponymCompiled_vmapId(args, bnd)
    else: raise newException(ValueError, "unknown phase-1 def " & name)
  expect(vecValueToSeq[int](got1, n, vecGlobals, "Vec", intDec) == expected,
    name & " phase-1 agrees")

for xs in [@[], @[1], @[3, -2, 7], @[1, 2, 3, 4, 5]]:
  let n = xs.len
  let want = xs.mapIt(it * 2)
  checkVecVec("vmapDouble", @[natArg(n), vecArg(xs)], want,
    proc(): seq[int] = eponymCompiledRepr_vmapDouble(n, xs))

for xs in [@[], @[1], @[3, -2, 7], @[1, 2, 3, 4, 5]]:
  let n = xs.len
  let got = eponymCompiledRepr_vlength(n, xs)
  expect(got == n, "vlength repr computes " & $n)
  let bnd = testPostulateBindings()
  let args = @[natArg(n), vecArg(xs)]
  let want = callValueFuncDir("", prog, "vlength", args, bnd)
  expect(valueToNat(want, vecGlobals) == n, "vlength interpreter agrees")
  let got1 = eponymCompiled_vlength(args, bnd)
  expect(valueToNat(got1, vecGlobals) == n, "vlength phase-1 agrees")

for (xs, d) in [(@[], 99), (@[5], 99), (@[5, 6, 7], -3)]:
  let n = xs.len
  let want = if n == 0: d else: xs[0]
  let got = eponymCompiledRepr_vheadOr(n, xs, d)
  expect(got == want, "vheadOr repr computes " & $want)
  let bnd = testPostulateBindings()
  let args = @[natArg(n), vecArg(xs), intToValue(d)]
  let wantV = callValueFuncDir("", prog, "vheadOr", args, bnd)
  expect(valueToInt(wantV) == want, "vheadOr interpreter agrees")
  let got1 = eponymCompiled_vheadOr(args, bnd)
  expect(valueToInt(got1) == want, "vheadOr phase-1 agrees")

for (xs, ys) in [(@[1, 2], @[3]), (@[], @[4, 5]), (@[1], @[]),
                 (@[1, 2, 3], @[4, 5, 6, 7])]:
  let want = xs & ys
  checkVecVec("vappend",
    @[natArg(xs.len), natArg(ys.len), vecArg(xs), vecArg(ys)], want,
    proc(): seq[int] =
      eponymCompiledRepr_vappend(xs.len, ys.len, xs, ys))

for name in ["vmapDouble", "vlength", "vheadOr", "vappend", "vconsStep"]:
  expect(name in reprCompiledNames(), name & " has a repr proc")

# --- fragment boundary: non-lambda vecElim cons case falls back ---
expect("vmapId" notin reprCompiledNames(),
  "non-lambda vecElim cons case has no repr proc")
block:
  let bnd = testPostulateBindings()
  for xs in [@[], @[1, 2, 3]]:
    let args = @[natArg(xs.len), vecArg(xs)]
    let got = eponymCompiled_vmapId(args, bnd)
    let want = callValueFuncDir("", prog, "vmapId", args, bnd)
    expect(vecValueToSeq[int](got, xs.len, vecGlobals, "Vec", intDec) == xs,
      "vmapId via phase-1")
    expect(vecValueToSeq[int](want, xs.len, vecGlobals, "Vec", intDec) == xs,
      "vmapId interpreter agrees")

# --- entry check: the repr proc preserves the interpreter codec's loud
# --- failure on length mismatch (`seqToVecValue` raises ValueError).
block:
  var raised = false
  try:
    discard eponymCompiledRepr_vmapDouble(3, @[1, 2])
  except ValueError:
    raised = true
  expect(raised, "repr Vec entry check raises on length mismatch")
  expect(eponymCompiledRepr_vmapDouble(2, @[1, 2]) == @[2, 4],
    "repr Vec entry check passes on matching length")

# --- benchmark: Phase-1 compiled vs Phase-2 repr (per #19's framing) ---
# The interpreter is context only (differential agreement is checked
# above); the comparison that matters is Phase 2 against Phase 1.
block:
  const iters = 20_000
  const n = 50
  let xs = toSeq(1 .. n)
  let argV = @[natArg(n), vecArg(xs)]
  let bnd = testPostulateBindings()
  var t0 = cpuTime()
  var acc1 = 0
  for i in 0 ..< iters:
    let v = eponymCompiled_vmapDouble(argV, bnd)
    acc1 += vecValueToSeq[int](v, n, vecGlobals, "Vec", intDec).len
  let tPhase1 = cpuTime() - t0
  t0 = cpuTime()
  var acc2 = 0
  for i in 0 ..< iters:
    acc2 += eponymCompiledRepr_vmapDouble(n, xs).len
  let tPhase2 = cpuTime() - t0
  expect(acc1 == acc2, "vmapDouble accumulators agree")
  echo "bench vmapDouble x", iters, " (n=", n, "): phase-1 ",
    tPhase1.formatFloat(ffDecimal, 3), "s | phase-2 ",
    tPhase2.formatFloat(ffDecimal, 3), "s; phase-2 vs phase-1 ",
    (tPhase1 / tPhase2).formatFloat(ffDecimal, 1), "x"

echo "all Phase 2 Vec codegen differential checks passed"
