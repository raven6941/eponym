## Differential tests + benchmark for the Phase 2 representation backend
## (Issue #330 v3: `List` as `seq[int]`).
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
data List (A : Type 0) : Type 0 where
| nil : List A
| cons (x : A) (xs : List A) : List A
proc lmapDouble (xs : List Int) : List Int =
  listElim Int (lam (u : List Int). List Int)
           (nil Int)
           (lam (x : Int). lam (tl : List Int). lam (ih : List Int).
             cons Int (addInt x x) ih)
           xs
proc llength (xs : List Int) : Nat =
  listElim Int (lam (u : List Int). Nat)
           zero
           (lam (x : Int). lam (tl : List Int). lam (ih : Nat). suc ih)
           xs
proc lappend (xs : List Int) (ys : List Int) : List Int =
  listElim Int (lam (u : List Int). List Int)
           ys
           (lam (x : Int). lam (tl : List Int). lam (ih : List Int).
             cons Int x ih)
           xs
proc lheadOr (xs : List Int) (d : Int) : Int =
  listElim Int (lam (u : List Int). Int)
           d
           (lam (x : Int). lam (tl : List Int). lam (ih : Int). x)
           xs
proc lconsStep (x : Int) (tl : List Int) (ih : List Int) : List Int =
  cons Int x ih
proc lmapId (xs : List Int) : List Int =
  listElim Int (lam (u : List Int). List Int) (nil Int) lconsStep xs
"""

differentialBlockRepr(prog, currentSourcePath(), "Int:int,Nat:int,List:list")

let listGlobals = getGlobals(prog)

proc intEnc(x: int, g: Globals): Value = intToValue(x)
proc intDec(v: Value, g: Globals): int = valueToInt(v)

proc listArg(items: seq[int]): Value =
  seqToListValue(items, listGlobals, "List", intEnc)

proc checkListList(name: string, args: seq[Value], expected: seq[int],
                   reprCall: proc(): seq[int]) =
  ## Repr proc (called via `reprCall`) vs literal expectation, vs the
  ## interpreter, vs the Phase-1 compiled proc (List results decoded with
  ## `listValueToSeq`).
  let got = reprCall()
  expect(got == expected, name & " repr computes " & $expected)
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, args, bnd)
  expect(listValueToSeq[int](want, listGlobals, "List", intDec) == expected,
    name & " interpreter agrees")
  let got1 = case name
    of "lmapDouble": eponymCompiled_lmapDouble(args, bnd)
    of "lappend": eponymCompiled_lappend(args, bnd)
    of "lmapId": eponymCompiled_lmapId(args, bnd)
    else: raise newException(ValueError, "unknown phase-1 def " & name)
  expect(listValueToSeq[int](got1, listGlobals, "List", intDec) == expected,
    name & " phase-1 agrees")

for xs in [@[], @[1], @[3, -2, 7], @[1, 2, 3, 4, 5]]:
  let want = xs.mapIt(it * 2)
  checkListList("lmapDouble", @[listArg(xs)], want,
    proc(): seq[int] = eponymCompiledRepr_lmapDouble(xs))

for xs in [@[], @[1], @[3, -2, 7], @[1, 2, 3, 4, 5]]:
  let got = eponymCompiledRepr_llength(xs)
  expect(got == xs.len, "llength repr computes " & $xs.len)
  let bnd = testPostulateBindings()
  let args = @[listArg(xs)]
  let want = callValueFuncDir("", prog, "llength", args, bnd)
  expect(valueToNat(want, listGlobals) == xs.len,
    "llength interpreter agrees")
  let got1 = eponymCompiled_llength(args, bnd)
  expect(valueToNat(got1, listGlobals) == xs.len, "llength phase-1 agrees")

for (xs, ys) in [(@[1, 2], @[3]), (@[], @[4, 5]), (@[1], @[]),
                 (@[1, 2, 3], @[4, 5, 6, 7])]:
  let want = xs & ys
  checkListList("lappend", @[listArg(xs), listArg(ys)], want,
    proc(): seq[int] = eponymCompiledRepr_lappend(xs, ys))

for (xs, d) in [(@[], 99), (@[5], 99), (@[5, 6, 7], -3)]:
  let want = if xs.len == 0: d else: xs[0]
  let got = eponymCompiledRepr_lheadOr(xs, d)
  expect(got == want, "lheadOr repr computes " & $want)
  let bnd = testPostulateBindings()
  let args = @[listArg(xs), intToValue(d)]
  let wantV = callValueFuncDir("", prog, "lheadOr", args, bnd)
  expect(valueToInt(wantV) == want, "lheadOr interpreter agrees")
  let got1 = eponymCompiled_lheadOr(args, bnd)
  expect(valueToInt(got1) == want, "lheadOr phase-1 agrees")

for name in ["lmapDouble", "llength", "lappend", "lheadOr", "lconsStep"]:
  expect(name in reprCompiledNames(), name & " has a repr proc")

# --- fragment boundary: non-lambda listElim cons case falls back ---
expect("lmapId" notin reprCompiledNames(),
  "non-lambda listElim cons case has no repr proc")
block:
  let bnd = testPostulateBindings()
  for xs in [@[], @[1, 2, 3]]:
    let args = @[listArg(xs)]
    let got = eponymCompiled_lmapId(args, bnd)
    let want = callValueFuncDir("", prog, "lmapId", args, bnd)
    expect(listValueToSeq[int](got, listGlobals, "List", intDec) == xs,
      "lmapId via phase-1")
    expect(listValueToSeq[int](want, listGlobals, "List", intDec) == xs,
      "lmapId interpreter agrees")

# --- benchmark: Phase-1 compiled vs Phase-2 repr (per #19's framing) ---
block:
  const iters = 20_000
  const n = 50
  let xs = toSeq(1 .. n)
  let argV = @[listArg(xs)]
  let bnd = testPostulateBindings()
  var t0 = cpuTime()
  var acc1 = 0
  for i in 0 ..< iters:
    let v = eponymCompiled_lmapDouble(argV, bnd)
    acc1 += listValueToSeq[int](v, listGlobals, "List", intDec).len
  let tPhase1 = cpuTime() - t0
  t0 = cpuTime()
  var acc2 = 0
  for i in 0 ..< iters:
    acc2 += eponymCompiledRepr_lmapDouble(xs).len
  let tPhase2 = cpuTime() - t0
  expect(acc1 == acc2, "lmapDouble accumulators agree")
  echo "bench lmapDouble x", iters, " (n=", n, "): phase-1 ",
    tPhase1.formatFloat(ffDecimal, 3), "s | phase-2 ",
    tPhase2.formatFloat(ffDecimal, 3), "s; phase-2 vs phase-1 ",
    (tPhase1 / tPhase2).formatFloat(ffDecimal, 1), "x"

echo "all Phase 2 List codegen differential checks passed"
