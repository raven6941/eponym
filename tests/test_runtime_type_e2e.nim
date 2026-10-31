## Issue #499 phase 3: production pragma-to-residual end-to-end coverage.
import eponym_mac
import staged_inject
import std/[osproc, os, strutils]

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/text.ep"
  runtimeType(Nat, int)
  runtimeType(String, string)
  proc myArrow: Univ {.runtimeType.} = Pi(n: Nat, String)
  proc myParameterizedArrow(n: Nat): Univ {.runtimeType.} = Pi(x: Nat, String)

doAssert myArrowRuntimeType() == arrowRep(natRep(), stringRep())
doAssert myParameterizedArrowRuntimeType(7) == arrowRep(natRep(), stringRep())

let (symbols, status) = execCmdEx("nm " & quoteShell(getAppFilename()))
doAssert status == 0
for interpreterSymbol in ["evalWhnf", "evalWithBindings", "callValueFuncDir",
    "getGlobalsDir", "elabCheckDirStateAll"]:
  doAssert interpreterSymbol notin symbols,
    "production residual binary references interpreter symbol " & interpreterSymbol

echo "test_runtime_type_e2e: passed"
