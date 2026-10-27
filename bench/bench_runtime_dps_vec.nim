## #432 runtime benchmark: Vec DPS folds (Phase-3 destination-passing shapes).
##
## Representative workload: cons-rebuild `vecElim` folds (`vmapDps`,
## `vappendDps`, `vlenDps`) from the #331 DPS work — the shapes the repr
## backend optimizes into a single preallocated destination.
##
## What each path does (fair-baseline names):
## - interpreter: prebuilt Value args + findDef + ETT interpreter over the
##   checked def + Value->host decode of the result. Elaboration is cached
##   (defCache) and warmed before timing.
## - value: prebuilt Value args + compiled Phase-1 Value-tier proc
##   (eponymCompiled_<name>) + decode.
## - repr: host-native seq[int] call (eponymCompiledRepr_<name>); no Value
##   values cross the boundary. Per-#19 framing this is the comparison
##   that matters; the interpreter is context.
##
## Build: nim c -r --path:src --path:src/eponym --path:tests --path:bench \
##   bench/bench_runtime_dps_vec.nim
## Dev-only: not wired into tools/ci-local.sh or any CI workflow.

import std/[sequtils, times, strutils]
import codegen_phase2_differential
import bench_runtime_harness

const prog = """postulate(Int, Univ)
data(Nat, Univ) where
| zero : Nat
| suc (n : Nat) : Nat
data(Vec, [A: Univ], Nat -> Univ) where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc natAdd (m : Nat) (n : Nat) : Nat =
  natElim (lam(u: Nat) => Nat) n (lam(p: Nat) => lam(ih: Nat) => suc ih) m
proc vappendDps (m : Nat) (n : Nat) (xs : Vec Int m) (ys : Vec Int n)
    : Vec Int (natAdd m n) =
  vecElim Int (lam(i: Nat) => lam(v: Vec Int i) => Vec Int (natAdd i n))
            ys
            (lam(i: Nat) => lam(x: Int) => lam(xs2: Vec Int i) => lam(ih: Vec Int (natAdd i n)) => cons Int (natAdd i n) x ih)
            m xs
proc vmapDps (n : Nat) (xs : Vec Int n) : Vec Int n =
  vecElim Int (lam(i: Nat) => lam(v: Vec Int i) => Vec Int i)
            (nil Int)
            (lam(i: Nat) => lam(x: Int) => lam(xs2: Vec Int i) => lam(ih: Vec Int i) => cons Int i (addInt x x) ih)
            n xs
proc vlenDps (n : Nat) (xs : Vec Int n) : Nat =
  vecElim Int (lam(i: Nat) => lam(v: Vec Int i) => Nat)
            zero
            (lam(i: Nat) => lam(x: Int) => lam(xs2: Vec Int i) => lam(ih: Nat) => suc ih)
            n xs
"""

differentialBlockRepr(prog, currentSourcePath(), "Int:int,Nat:int,Vec:vector")

let dpsGlobals = getGlobals(prog)

proc intEnc(x: int, g: Globals): Value = intToValue(x)
proc intDec(v: Value, g: Globals): int = valueToInt(v)

proc vecArg(items: seq[int]): Value =
  seqToVecValue(items, items.len, dpsGlobals, "Vec", intEnc)

proc natArg(n: int): Value = natToValue(n, dpsGlobals)

proc checkAgreementVec(name: string, args: seq[Value], n: int,
                       reprCall: proc(): seq[int], expected: seq[int]) =
  ## Differential sanity before timing: all three paths agree.
  doAssert name in reprCompiledNames(), name & " has a repr proc"
  let gotRepr = reprCall()
  doAssert gotRepr == expected, name & " repr computes " & $expected
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, args, bnd)
  doAssert vecValueToSeq[int](want, n, dpsGlobals, "Vec", intDec) == expected,
    name & " interpreter agrees"
  let got1 = case name
    of "vappendDps": eponymCompiled_vappendDps(args, bnd)
    of "vmapDps": eponymCompiled_vmapDps(args, bnd)
    of "vlenDps": eponymCompiled_vlenDps(args, bnd)
    else: raise newException(ValueError, "unknown def " & name)
  doAssert vecValueToSeq[int](got1, n, dpsGlobals, "Vec", intDec) == expected,
    name & " value backend agrees"

proc benchVecFold(name: string, args: seq[Value], n: int,
                  reprCall: proc(): seq[int], hostN: int) =
  let bnd = testPostulateBindings()
  # Warm the interpreter cache (elaboration) outside the timed section.
  discard callValueFuncDir("", prog, name, args, bnd)
  let interpBody = proc(acc: var int) =
    let v = callValueFuncDir("", prog, name, args, bnd)
    acc += vecValueToSeq[int](v, n, dpsGlobals, "Vec", intDec).len
  let valueBody = proc(acc: var int) =
    let v = case name
      of "vappendDps": eponymCompiled_vappendDps(args, bnd)
      of "vmapDps": eponymCompiled_vmapDps(args, bnd)
      of "vlenDps": eponymCompiled_vlenDps(args, bnd)
      else: raise newException(ValueError, "unknown def " & name)
    acc += vecValueToSeq[int](v, n, dpsGlobals, "Vec", intDec).len
  let reprBody = proc(acc: var int) =
    acc += reprCall().len
  let iIters = calibrateIters(interpBody)
  let vIters = calibrateIters(valueBody)
  let rIters = calibrateIters(reprBody)
  printProgramHeader(name & "  (Vec n=" & $hostN & ")",
    "interpreter: findDef + ETT interpreter + decode | " &
    "value: compiled Value proc + decode | repr: host-native seq[int] call")
  let paths = @[
    ("interpreter", timeIters(interpBody, iIters), iIters).PathTime,
    ("value", timeIters(valueBody, vIters), vIters).PathTime,
    ("repr", timeIters(reprBody, rIters), rIters).PathTime,
  ]
  for p in paths:
    printPathRow(p)
  printComparisons(paths)

when isMainModule:
  const n = 200
  let xs = toSeq(1 .. n)

  block:
    let args = @[natArg(n), vecArg(xs)]
    let want = xs.mapIt(it * 2)
    checkAgreementVec("vmapDps", args, n,
      proc(): seq[int] = eponymCompiledRepr_vmapDps(n, xs), want)
    benchVecFold("vmapDps", args, n,
      proc(): seq[int] = eponymCompiledRepr_vmapDps(n, xs), n)

  block:
    let args = @[natArg(n), natArg(n), vecArg(xs), vecArg(xs)]
    let want = xs & xs
    checkAgreementVec("vappendDps", args, 2 * n,
      proc(): seq[int] = eponymCompiledRepr_vappendDps(n, n, xs, xs), want)
    benchVecFold("vappendDps", args, 2 * n,
      proc(): seq[int] = eponymCompiledRepr_vappendDps(n, n, xs, xs), n)

  block:
    let args = @[natArg(n), vecArg(xs)]
    let bnd = testPostulateBindings()
    doAssert eponymCompiledRepr_vlenDps(n, xs) == n
    doAssert valueToNat(callValueFuncDir("", prog, "vlenDps", args, bnd),
                        dpsGlobals) == n
    doAssert valueToNat(eponymCompiled_vlenDps(args, bnd), dpsGlobals) == n
    # vlenDps returns Nat; time with an int-yielding body instead.
    discard callValueFuncDir("", prog, "vlenDps", args, bnd)
    let interpBody = proc(acc: var int) =
      acc += valueToNat(callValueFuncDir("", prog, "vlenDps", args, bnd),
                        dpsGlobals)
    let valueBody = proc(acc: var int) =
      acc += valueToNat(eponymCompiled_vlenDps(args, bnd), dpsGlobals)
    let reprBody = proc(acc: var int) =
      acc += eponymCompiledRepr_vlenDps(n, xs)
    let iIters = calibrateIters(interpBody)
    let vIters = calibrateIters(valueBody)
    let rIters = calibrateIters(reprBody)
    printProgramHeader("vlenDps  (Vec n=" & $n & ")",
      "interpreter: findDef + ETT interpreter + decode | " &
      "value: compiled Value proc + decode | repr: host-native int call")
    let paths = @[
      ("interpreter", timeIters(interpBody, iIters), iIters).PathTime,
      ("value", timeIters(valueBody, vIters), vIters).PathTime,
      ("repr", timeIters(reprBody, rIters), rIters).PathTime,
    ]
    for p in paths:
      printPathRow(p)
    printComparisons(paths)

  echo ""
  echo "bench_runtime_dps_vec: all agreement checks passed"
