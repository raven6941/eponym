## Issue #240: profile the proof-carrying Nat arithmetic path.
##
## Run from the repository root:
##   nim c -r -d:elabProfile --hints:off --path:src --path:src/eponym \
##     tools/profile_nat_arith.nim
##
## The ordinary phase report stays exclusive. The evidence-path section
## separately reports normalization, evidence construction excluding that
## normalization, and the bare-core evidence check.

import std/[strutils, times]
import elab
import elab_prof

when not ElabProfile:
  {.error: "compile this profiler with -d:elabProfile".}

let started = cpuTime()
var driver = initModuleDriver()
discard driver.elabFile("lib/nat_lemmas.ep")
echo "nat_lemmas.ep wall time: ", cpuTime() - started, " s"
let report = reportPhases()
doAssert "epdArithNormalize" in report
doAssert "epdArithBuild" in report
doAssert "epdEvidenceCheck" in report
echo report
