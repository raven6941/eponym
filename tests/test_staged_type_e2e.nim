## Issue #499 phase 3: production pragma-to-residual end-to-end coverage.
## Issue #524: the staging pragma is `{.stagedType.}` (renamed from
## `{.runtimeType.}`); the `runtimeType(EponymType, NimType)` mapping form
## keeps its name.
import eponym_mac
import staged_inject
import std/[osproc, os, strutils]

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/text.ep"
  runtimeType(Nat, int)
  runtimeType(String, string)
  proc myArrow: Univ {.stagedType.} = Pi(n: Nat, String)
  proc myParameterizedArrow(n: Nat): Univ {.stagedType.} = Pi(x: Nat, String)

doAssert myArrowStagedType() == arrowRep(natRep(), stringRep())
doAssert myParameterizedArrowStagedType(7) == arrowRep(natRep(), stringRep())

let (symbols, status) = execCmdEx("nm " & quoteShell(getAppFilename()))
doAssert status == 0
for interpreterSymbol in ["evalWhnf", "evalWithBindings", "callValueFuncDir",
    "getGlobalsDir", "elabCheckDirStateAll"]:
  doAssert interpreterSymbol notin symbols,
    "production residual binary references interpreter symbol " & interpreterSymbol

echo "test_staged_type_e2e: passed"
