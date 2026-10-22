## Differential tests + benchmark for Phase-3 destination-passing folds
## (issue #331): cons-rebuild `listElim` folds compile to a single
## preallocated destination instead of per-step `@[x] & acc` allocation.
##
## Uses the shared `differentialBlockRepr` driver
## (`tests/codegen_phase2_differential.nim`): each repr proc is checked
## against the interpreter (`callValueFuncDir`) and against its Phase-1
## compiled twin, then benchmarked per #19's framing (Phase 3 against
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
proc lappendDps (xs : List Int) (ys : List Int) : List Int =
  listElim Int (lam (u : List Int). List Int)
           ys
           (lam (x : Int). lam (tl : List Int). lam (ih : List Int).
             cons Int x ih)
           xs
proc lmapDps (xs : List Int) : List Int =
  listElim Int (lam (u : List Int). List Int)
           (nil Int)
           (lam (x : Int). lam (tl : List Int). lam (ih : List Int).
             cons Int (addInt x x) ih)
           xs
proc ldoubleCons (xs : List Int) : List Int =
  ## Cons body whose tail is not the accumulator: exercises the fallback
  ## to the allocating fold inside the DPS test module.
  listElim Int (lam (u : List Int). List Int)
           (nil Int)
           (lam (x : Int). lam (tl : List Int). lam (ih : List Int).
             cons Int x (cons Int x ih))
           xs
"""

differentialBlockRepr(prog, currentSourcePath(), "Int:int,Nat:int,List:list")

let dpsGlobals = getGlobals(prog)

proc intEnc(x: int, g: Globals): Value = intToValue(x)
proc intDec(v: Value, g: Globals): int = valueToInt(v)

proc listArg(items: seq[int]): Value =
  seqToListValue(items, dpsGlobals, "List", intEnc)

proc checkListList(name: string, args: seq[Value], expected: seq[int],
                   reprCall: proc(): seq[int]) =
  let got = reprCall()
  expect(got == expected, name & " repr computes " & $expected)
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, args, bnd)
  expect(listValueToSeq[int](want, dpsGlobals, "List", intDec) == expected,
    name & " interpreter agrees")
  let got1 = case name
    of "lappendDps": eponymCompiled_lappendDps(args, bnd)
    of "lmapDps": eponymCompiled_lmapDps(args, bnd)
    of "ldoubleCons": eponymCompiled_ldoubleCons(args, bnd)
    else: raise newException(ValueError, "unknown phase-1 def " & name)
  expect(listValueToSeq[int](got1, dpsGlobals, "List", intDec) == expected,
    name & " phase-1 agrees")

for (xs, ys) in [(@[1, 2], @[3]), (@[], @[4, 5]), (@[1], @[]),
                 (@[1, 2, 3], @[4, 5, 6, 7])]:
  let want = xs & ys
  checkListList("lappendDps", @[listArg(xs), listArg(ys)], want,
    proc(): seq[int] = eponymCompiledRepr_lappendDps(xs, ys))

for xs in [@[], @[1], @[3, -2, 7], @[1, 2, 3, 4, 5]]:
  let want = xs.mapIt(it * 2)
  checkListList("lmapDps", @[listArg(xs)], want,
    proc(): seq[int] = eponymCompiledRepr_lmapDps(xs))
  var want2: seq[int] = @[]
  for x in xs:
    want2.add(x)
    want2.add(x)
  checkListList("ldoubleCons", @[listArg(xs)], want2,
    proc(): seq[int] = eponymCompiledRepr_ldoubleCons(xs))

for name in ["lappendDps", "lmapDps", "ldoubleCons"]:
  expect(name in reprCompiledNames(), name & " has a repr proc")

# --- benchmark: Phase-1 compiled vs Phase-3 DPS repr (per #19's framing) ---
block:
  const iters = 20_000
  const n = 50
  let xs = toSeq(1 .. n)
  let argV = @[listArg(xs)]
  let bnd = testPostulateBindings()
  var t0 = cpuTime()
  var acc1 = 0
  for i in 0 ..< iters:
    let v = eponymCompiled_lmapDps(argV, bnd)
    acc1 += listValueToSeq[int](v, dpsGlobals, "List", intDec).len
  let tPhase1 = cpuTime() - t0
  t0 = cpuTime()
  var acc2 = 0
  for i in 0 ..< iters:
    acc2 += eponymCompiledRepr_lmapDps(xs).len
  let tPhase3 = cpuTime() - t0
  expect(acc1 == acc2, "lmapDps accumulators agree")
  echo "bench lmapDps x", iters, " (n=", n, "): phase-1 ",
    tPhase1.formatFloat(ffDecimal, 3), "s | phase-3 ",
    tPhase3.formatFloat(ffDecimal, 3), "s; phase-3 vs phase-1 ",
    (tPhase1 / tPhase3).formatFloat(ffDecimal, 1), "x"

echo "all Phase 3 DPS List codegen differential checks passed"
