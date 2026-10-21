## Issues #240/#241: profile the proof-carrying Nat arithmetic path and count
## safe memoization candidates without changing checking behavior.
##
## Run from the repository root:
##   nim c -r -d:elabProfile --hints:off --path:src --path:src/eponym \
##     tools/profile_nat_arith.nim
## Add `-d:profileArithEvidenceCacheCandidates=false` to measure without the
## read-only candidate-key scan.
##
## The ordinary phase report stays exclusive. The evidence-path section
## separately reports normalization, evidence construction excluding that
## normalization, and the bare-core evidence check. Candidate counts compare
## alpha-stable closed goal shapes and exact goal/evidence pairs.

import std/[strutils, monotimes, times]
import elab
import elab_prof

when not ElabProfile:
  {.error: "compile this profiler with -d:elabProfile".}

let started = getMonoTime()
var driver = initModuleDriver()
discard driver.elabFile("lib/nat_lemmas.ep")
let elapsedNs = (getMonoTime() - started).inNanoseconds
echo "nat_lemmas.ep wall time: ", elapsedNs.float / 1e9, " s"
let evidencePairHitRate =
  if driver.ms.arithEvidencePairProbes > 0:
    100.0 * driver.ms.arithEvidencePairHits.float /
      driver.ms.arithEvidencePairProbes.float
  else:
    0.0
echo "same goal-and-evidence shape: probes=", driver.ms.arithEvidencePairProbes,
     " hits=", driver.ms.arithEvidencePairHits,
     " hit-rate=", evidencePairHitRate, "%"
let goalHitRate =
  if driver.ms.arithEvidenceGoalProbes > 0:
    100.0 * driver.ms.arithEvidenceGoalHits.float /
      driver.ms.arithEvidenceGoalProbes.float
  else:
    0.0
echo "same goal shape: probes=", driver.ms.arithEvidenceGoalProbes,
     " hits=", driver.ms.arithEvidenceGoalHits,
     " hit-rate=", goalHitRate, "%"
let normalizedHitRate =
  if driver.ms.arithEvidenceNormalizedProbes > 0:
    100.0 * driver.ms.arithEvidenceNormalizedHits.float /
      driver.ms.arithEvidenceNormalizedProbes.float
  else:
    0.0
echo "same normalized arithmetic goal: probes=",
     driver.ms.arithEvidenceNormalizedProbes,
     " hits=", driver.ms.arithEvidenceNormalizedHits,
     " hit-rate=", normalizedHitRate, "%"
let report = reportPhases()
doAssert "epdArithNormalize" in report
doAssert "epdArithBuild" in report
doAssert "epdEvidenceCheck" in report
when ProfileArithEvidenceCacheCandidates:
  doAssert driver.ms.arithEvidenceGoalProbes > 0
  doAssert driver.ms.arithEvidencePairProbes > 0
  doAssert driver.ms.arithEvidenceNormalizedProbes > 0
echo report
