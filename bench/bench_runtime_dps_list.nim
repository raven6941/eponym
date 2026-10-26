## #432 runtime benchmark: List DPS folds (Phase-3 destination-passing shapes).
##
## Representative workload: cons-rebuild `listElim` folds (`lmapDps`,
## `lappendDps`, `lfilterNonZero`) from the #331 DPS work — the List-side
## shapes the repr backend optimizes into a single preallocated
## destination, including the conditional-cons (filter) shape.
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
## Build: nim c -r -d:nimCallDepthLimit=30000 \
##   --path:src --path:src/eponym --path:tests --path:bench \
##   bench/bench_runtime_dps_list.nim
## The depth knob is needed because the ETT interpreter recurses per list
## element (stack depth scales with n); it changes no semantics, it only
## raises the debug-build safety rail. The Vec driver does not need it.
## Dev-only: not wired into tools/ci-local.sh or any CI workflow.

import std/[sequtils, times, strutils]
import codegen_phase2_differential
import bench_runtime_harness

const prog = """postulate(Int, Univ)
data(Nat, Univ) where
| zero : Nat
| suc (n : Nat) : Nat
data(Bool, Univ) where
| true : Bool
| false : Bool
data(List, [A: Univ], Univ) where
| nil : List A
| cons (x : A) (xs : List A) : List A
proc isZero (n : Nat) : Bool =
  natElim (lam(u, Nat, Bool)) true (lam(p, Nat, lam(ih, Bool, false))) n
proc notb (b : Bool) : Bool =
  boolElim (lam(u, Bool, Bool)) false true b
proc lappendDps (xs : List Int) (ys : List Int) : List Int =
  listElim Int (lam(u, List Int, List Int))
           ys
           (lam(x, Int, lam(tl, List Int, lam(ih, List Int, cons Int x ih))))
           xs
proc lmapDps (xs : List Int) : List Int =
  listElim Int (lam(u, List Int, List Int))
           (nil Int)
           (lam(x, Int, lam(tl, List Int, lam(ih, List Int, cons Int (addInt x x) ih))))
           xs
proc lfilterNonZero (xs : List Nat) : List Nat =
  listElim Nat (lam(u, List Nat, List Nat))
           (nil Nat)
           (lam(x, Nat, lam(tl, List Nat, lam(ih, List Nat, boolElim (lam(u, Bool, List Nat)) (cons Nat x ih) ih (notb (isZero x))))))
           xs
"""

differentialBlockRepr(prog, currentSourcePath(), "Int:int,Nat:int,Bool:int,List:list")

let dpsGlobals = getGlobals(prog)

proc intEnc(x: int, g: Globals): Value = intToValue(x)
proc intDec(v: Value, g: Globals): int = valueToInt(v)
proc natEnc(x: int, g: Globals): Value = natToValue(x, g)

proc listArg(items: seq[int]): Value =
  seqToListValue(items, dpsGlobals, "List", intEnc)

proc natListArg(items: seq[int]): Value =
  seqToListValue(items, dpsGlobals, "List", natEnc)

proc checkAgreementList(name: string, args: seq[Value],
                        reprCall: proc(): seq[int], expected: seq[int],
                        enc: proc(x: int, g: Globals): Value,
                        dec: proc(v: Value, g: Globals): int) =
  ## Differential sanity before timing: all three paths agree.
  doAssert name in reprCompiledNames(), name & " has a repr proc"
  let gotRepr = reprCall()
  doAssert gotRepr == expected, name & " repr computes " & $expected
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, args, bnd)
  doAssert listValueToSeq[int](want, dpsGlobals, "List", dec) == expected,
    name & " interpreter agrees"
  let got1 = case name
    of "lappendDps": eponymCompiled_lappendDps(args, bnd)
    of "lmapDps": eponymCompiled_lmapDps(args, bnd)
    of "lfilterNonZero": eponymCompiled_lfilterNonZero(args, bnd)
    else: raise newException(ValueError, "unknown def " & name)
  doAssert listValueToSeq[int](got1, dpsGlobals, "List", dec) == expected,
    name & " value backend agrees"

proc benchListFold(name: string, args: seq[Value],
                   reprCall: proc(): seq[int], hostN: int,
                   dec: proc(v: Value, g: Globals): int) =
  let bnd = testPostulateBindings()
  # Warm the interpreter cache (elaboration) outside the timed section.
  discard callValueFuncDir("", prog, name, args, bnd)
  let interpBody = proc(acc: var int) =
    let v = callValueFuncDir("", prog, name, args, bnd)
    acc += listValueToSeq[int](v, dpsGlobals, "List", dec).len
  let valueBody = proc(acc: var int) =
    let v = case name
      of "lappendDps": eponymCompiled_lappendDps(args, bnd)
      of "lmapDps": eponymCompiled_lmapDps(args, bnd)
      of "lfilterNonZero": eponymCompiled_lfilterNonZero(args, bnd)
      else: raise newException(ValueError, "unknown def " & name)
    acc += listValueToSeq[int](v, dpsGlobals, "List", dec).len
  let reprBody = proc(acc: var int) =
    acc += reprCall().len
  let iIters = calibrateIters(interpBody)
  let vIters = calibrateIters(valueBody)
  let rIters = calibrateIters(reprBody)
  printProgramHeader(name & "  (List n=" & $hostN & ")",
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
    let args = @[listArg(xs)]
    let want = xs.mapIt(it * 2)
    checkAgreementList("lmapDps", args,
      proc(): seq[int] = eponymCompiledRepr_lmapDps(xs), want, intEnc, intDec)
    benchListFold("lmapDps", args,
      proc(): seq[int] = eponymCompiledRepr_lmapDps(xs), n, intDec)

  block:
    let args = @[listArg(xs), listArg(xs)]
    let want = xs & xs
    checkAgreementList("lappendDps", args,
      proc(): seq[int] = eponymCompiledRepr_lappendDps(xs, xs), want,
      intEnc, intDec)
    benchListFold("lappendDps", args,
      proc(): seq[int] = eponymCompiledRepr_lappendDps(xs, xs), n, intDec)

  block:
    # Filter shape: every third element is zero -> dropped.
    let zs = toSeq(0 ..< n).mapIt(if it mod 3 == 0: 0 else: it + 1)
    let args = @[natListArg(zs)]
    let want = zs.filterIt(it != 0)
    checkAgreementList("lfilterNonZero", args,
      proc(): seq[int] = eponymCompiledRepr_lfilterNonZero(zs), want,
      natEnc, proc(v: Value, g: Globals): int = valueToNat(v, g))
    benchListFold("lfilterNonZero", args,
      proc(): seq[int] = eponymCompiledRepr_lfilterNonZero(zs), n,
      proc(v: Value, g: Globals): int = valueToNat(v, g))

  echo ""
  echo "bench_runtime_dps_list: all agreement checks passed"
