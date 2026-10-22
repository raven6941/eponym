## Differential tests + benchmark for the Phase 2 representation backend
## (Issue #330 v3: `Option` as `Option[int]`).
##
## Uses the shared `differentialBlockRepr` driver
## (`tests/codegen_phase2_differential.nim`): each repr proc is checked
## against the interpreter (`callValueFuncDir`) and against its Phase-1
## compiled twin, then benchmarked per #19's framing (Phase 2 against
## Phase 1's compiled output).

import std/[options, times]
import codegen_phase2_differential

const prog = """postulate Int : Type 0
data Option (A : Type 0) : Type 0 where
| none : Option A
| some (value : A) : Option A
proc optDouble (o : Option Int) : Option Int =
  optionElim Int (lam (u : Option Int). Option Int)
             (none Int)
             (lam (v : Int). some Int (addInt v v))
             o
proc optDefault (o : Option Int) (d : Int) : Int =
  optionElim Int (lam (u : Option Int). Int)
             d
             (lam (v : Int). v)
             o
proc osomeStep (v : Int) : Option Int = some Int (addInt v v)
proc optDoubleFn (o : Option Int) : Option Int =
  optionElim Int (lam (u : Option Int). Option Int)
             (none Int) osomeStep o
"""

differentialBlockRepr(prog, currentSourcePath(), "Int:int,Option:option")

let optGlobals = getGlobals(prog)

proc intEnc(x: int, g: Globals): Value = intToValue(x)
proc intDec(v: Value, g: Globals): int = valueToInt(v)

proc optArg(o: Option[int]): Value =
  optionToValue(o, optGlobals, "Option", intEnc)

proc checkOptOpt(name: string, args: seq[Value], expected: Option[int],
                 reprCall: proc(): Option[int]) =
  ## Repr proc (called via `reprCall`) vs literal expectation, vs the
  ## interpreter, vs the Phase-1 compiled proc (Option results decoded
  ## with `valueToOption`).
  let got = reprCall()
  expect(got == expected, name & " repr computes " & $expected)
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, args, bnd)
  expect(valueToOption[int](want, optGlobals, "Option", intDec) == expected,
    name & " interpreter agrees")
  let got1 = case name
    of "optDouble": eponymCompiled_optDouble(args, bnd)
    of "optDoubleFn": eponymCompiled_optDoubleFn(args, bnd)
    else: raise newException(ValueError, "unknown phase-1 def " & name)
  expect(valueToOption[int](got1, optGlobals, "Option", intDec) == expected,
    name & " phase-1 agrees")

for o in [none(int), some(0), some(7), some(-3)]:
  let want = o.map(proc(x: int): int = x * 2)
  checkOptOpt("optDouble", @[optArg(o)], want,
    proc(): Option[int] = eponymCompiledRepr_optDouble(o))

for (o, d) in [(none(int), 99), (some(0), 99), (some(7), -3)]:
  let want = if o.isSome: o.get else: d
  let got = eponymCompiledRepr_optDefault(o, d)
  expect(got == want, "optDefault repr computes " & $want)
  let bnd = testPostulateBindings()
  let args = @[optArg(o), intToValue(d)]
  let wantV = callValueFuncDir("", prog, "optDefault", args, bnd)
  expect(valueToInt(wantV) == want, "optDefault interpreter agrees")
  let got1 = eponymCompiled_optDefault(args, bnd)
  expect(valueToInt(got1) == want, "optDefault phase-1 agrees")

for name in ["optDouble", "optDefault", "osomeStep"]:
  expect(name in reprCompiledNames(), name & " has a repr proc")

# --- fragment boundary: non-lambda optionElim some case falls back ---
expect("optDoubleFn" notin reprCompiledNames(),
  "non-lambda optionElim some case has no repr proc")
block:
  let bnd = testPostulateBindings()
  for o in [none(int), some(4)]:
    let args = @[optArg(o)]
    let got = eponymCompiled_optDoubleFn(args, bnd)
    let want = callValueFuncDir("", prog, "optDoubleFn", args, bnd)
    let expected = o.map(proc(x: int): int = x * 2)
    expect(valueToOption[int](got, optGlobals, "Option", intDec) == expected,
      "optDoubleFn via phase-1")
    expect(valueToOption[int](want, optGlobals, "Option", intDec) == expected,
      "optDoubleFn interpreter agrees")

# --- benchmark: Phase-1 compiled vs Phase-2 repr (per #19's framing) ---
block:
  const iters = 200_000
  let o = some(21)
  let argV = @[optArg(o)]
  let bnd = testPostulateBindings()
  var t0 = cpuTime()
  var acc1 = 0
  for i in 0 ..< iters:
    let v = eponymCompiled_optDouble(argV, bnd)
    acc1 += valueToOption[int](v, optGlobals, "Option", intDec).get
  let tPhase1 = cpuTime() - t0
  t0 = cpuTime()
  var acc2 = 0
  for i in 0 ..< iters:
    acc2 += eponymCompiledRepr_optDouble(o).get
  let tPhase2 = cpuTime() - t0
  expect(acc1 == acc2, "optDouble accumulators agree")
  echo "bench optDouble x", iters, ": phase-1 ",
    tPhase1.formatFloat(ffDecimal, 3), "s | phase-2 ",
    tPhase2.formatFloat(ffDecimal, 3), "s; phase-2 vs phase-1 ",
    (tPhase1 / tPhase2).formatFloat(ffDecimal, 1), "x"

echo "all Phase 2 Option codegen differential checks passed"
