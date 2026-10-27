## Explicitly require typed wrappers backed by generated code.

import eponym_mac
import std/[osproc, os, strutils]

eponymBlock:
  requireCompiled()
  import "fixtures/require_compiled_imported.ep"
  import "../lib/vec.ep"
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  proc addOne(value: Int): Int = value + 1
  proc importedAddTwo(value: Int): Int = importedPlusTwo(value)
  proc doubleVector(n: Nat, values: Vec[Int, n]): Vec[Int, n] =
    vecElim[Int](lam(i: Nat) => lam(v: Vec[Int, i]) => Vec[Int, i],
      vecnil[Int](),
      lam(i: Nat) => lam(x: Int) => lam(xs: Vec[Int, i]) => lam(ih: Vec[Int, i]) => cons[Int, i](addInt(x, x), ih), n, values)
  # Issue #407 slice 3: function types are representable — a higher-order
  # definition compiles at the repr tier and its wrapper takes an
  # ordinary {.closure.} proc.
  proc applyOnce(f: Int -> Int, x: Int): Int = f x
  proc doubleFn(x: Int): Int = x + x
  proc doubleIt(x: Int): Int = applyOnce doubleFn x

doAssert addOne(41) == 42
doAssert importedAddTwo(41) == 43
doAssert applyOnce(proc (v: int): int {.closure.} = v * 3, 5) == 15
doAssert doubleIt(21) == 42
doAssert doubleVector(3, @[2, 3, 5]) == @[4, 6, 10]
var vectorLengthRejected = false
try:
  discard doubleVector(2, @[2, 3, 5])
except ValueError:
  vectorLengthRejected = true
doAssert vectorLengthRejected, "compiled wrapper must check the Vec index"
let (symbols, nmStatus) = execCmdEx("nm " & quoteShell(getAppFilename()))
doAssert nmStatus == 0, "could not inspect compiled test artifact with nm"
for interpreterSymbol in ["evalWhnf", "evalWithBindings", "callValueFuncDir",
    "getGlobalsDir", "elabCheckDirStateAll"]:
  doAssert interpreterSymbol notin symbols,
    "representation-compiled static wrapper linked " & interpreterSymbol
echo "test_require_compiled: strict generated wrapper passed"
