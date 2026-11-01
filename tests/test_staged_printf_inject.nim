## Issue #491: residual runtime computation of a type structure.

import std/[os, osproc, strutils]
import ../src/experimental/staging/printf_inject

proc expect(ok: bool, message: string) =
  if not ok: quit("FAIL: " & message, 1)
  echo "ok: ", message

let dynamicSuffix = number(stringArg(endFormat()))
let expectedSuffix = arrowRep(natRep(),
  arrowRep(stringRep(), stringRep()))
expect(injectPrintfType("", dynamicSuffix) == expectedSuffix,
  "residual PrintfType follows a runtime format suffix")

let specialized = injectPrintfType("NS", dynamicSuffix)
let expectedSpecialized = arrowRep(natRep(), arrowRep(stringRep(),
  arrowRep(natRep(), arrowRep(stringRep(), stringRep()))))
expect(specialized == expectedSpecialized,
  "stager evaluates a static prefix and residualizes the dynamic suffix")

let (symbols, status) = execCmdEx("nm " & quoteShell(getAppFilename()))
expect(status == 0, "inspect prototype binary symbols")
for interpreterSymbol in ["evalWhnf", "evalWithBindings", "callValueFuncDir",
    "getGlobalsDir", "elabCheckDirStateAll"]:
  expect(interpreterSymbol notin symbols,
    "residual binary excludes interpreter symbol " & interpreterSymbol)

echo "all staged PrintfType injection checks passed"
