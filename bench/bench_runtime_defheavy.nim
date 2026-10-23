## #432 runtime benchmark: definition-heavy program.
##
## Representative workload: `pipelineRep`/`scoreOfRep` from
## bench/fixtures/defheavy_lib.ep and bench/fixtures/defheavy_score.ep —
## nested calls across definitions (`pipeline` = `addInt` over `vsum` over
## `vmapDbl`, over a vector built by `ones`), so the benchmark measures
## call-heavy generated code rather than a single hot loop. The block
## entries stay first-order over `Int` (no `Vec`-typed wrapper arguments);
## all `Vec` plumbing is inside the measured code.
##
## What each path does (fair-baseline names):
## - interpreter: prebuilt Value args + findDef + ETT interpreter over the
##   checked def + decode. Elaboration is cached (defCache) and warmed
##   before timing. No postulates are called, so empty bindings suffice.
## - value (`scoreOfRep` only): prebuilt Value args + compiled Phase-1
##   Value-tier proc + Score decode. The derived #402 codec is what makes
##   this row possible.
## - repr (same-block): host-native typed wrapper `entryA` emitted by
##   block A; its call to `pipelineRep` is a same-block direct call.
## - repr (cross-block): host-native typed wrapper `entryB` emitted by
##   block B; block B imports the same fixture, so its call to
##   `pipelineRep` reuses block A's already-emitted procs through the
##   #408 compile-time export registry — a cross-block direct call, not a
##   Value crossing and not a re-emission.
##
## Coverage findings, recorded honestly rather than worked around:
## - `Score` exercises the #402 derived mapping: the one-arg
##   `runtimeDerive(Score)` derives the representation from the checked
##   structure of the single-constructor family (no hand-written codec, no
##   postulate, no host binding). The derivation succeeds at compile time,
##   but the derived single-field-variant representation is outside the
##   Phase-2 codegen fragment ("runtime representation outside the
##   fragment"), so `scoreOfRep` has interpreter and value rows but no
##   repr row. The `pipelineRep` program carries the wall-clock comparison
##   including the cross-block pair.
## - There is no value row for `pipelineRep`: under `requireCompiled()`
##   the macro filters non-repr procs out of the emitted output
##   (interpreter-freedom), so no `eponymCompiled_` procs exist to time.
## - Elements and results are `Int`, not `Nat`: Nat-*returning* typed
##   wrappers are broken (issue #441 — the wrapper's `valueToNat` decode
##   fails at runtime), an unrelated defect.
##
## Build: nim c -r --path:src --path:src/eponym --path:tests --path:bench \
##   bench/bench_runtime_defheavy.nim
## Dev-only: not wired into tools/ci-local.sh or any CI workflow.

import std/strutils
import eponym_mac
import codegen_phase2_differential
import bench_runtime_harness

const libSrc = staticRead("fixtures/defheavy_lib.ep")
const scoreSrc = staticRead("fixtures/defheavy_score.ep")
const prog = libSrc & scoreSrc & """
proc entryA (n : Nat) (x : Int) : Int = pipelineRep n x
proc entryB (n : Nat) (x : Int) : Int = pipelineRep n x
proc entryC (n : Nat) (x : Int) : Score = scoreOfRep n x
"""

eponymBlock:
  requireCompiled()
  import "fixtures/defheavy_lib.ep"
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  proc entryA(n: Nat, x: Int): Int = pipelineRep(n, x)

eponymBlock:
  requireCompiled()
  import "fixtures/defheavy_lib.ep"
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  proc entryB(n: Nat, x: Int): Int = pipelineRep(n, x)

eponymBlock:
  import "fixtures/defheavy_lib.ep"
  import "fixtures/defheavy_score.ep"
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  runtimeDerive(Score)
  proc entryC(n: Nat, x: Int): Score = scoreOfRep(n, x)

let dhGlobals = getGlobals(prog)

proc natArgDh(n: int): Value = natToValue(n, dhGlobals)

proc scoreToInt(v: Value): int =
  ## Decode a `Score` value (`mkScore s`) to the wrapped int.
  valueToInt(v.whnfSpineArg(0))

proc checkAgreementDh(n: int, wantPipe, wantScore: int) =
  let args = @[natArgDh(n), intToValue(1)]
  let bnd = initRuntimeBindings()
  # Warm the interpreter cache (elaboration) outside the timed section.
  discard callValueFuncDir("", prog, "pipelineRep", args, bnd)
  let gotInterpPipe =
    valueToInt(callValueFuncDir("", prog, "pipelineRep", args, bnd))
  doAssert gotInterpPipe == wantPipe,
    "interpreter pipelineRep computes " & $wantPipe
  let gotInterpScore =
    scoreToInt(callValueFuncDir("", prog, "scoreOfRep", args, bnd))
  doAssert gotInterpScore == wantScore,
    "interpreter scoreOfRep computes " & $wantScore
  let gotValueScore =
    scoreToInt(eponymCompiled_entryC(args, bnd))
  doAssert gotValueScore == wantScore, "value scoreOfRep agrees"
  doAssert entryA(n, 1) == wantPipe, "repr same-block pipelineRep agrees"
  doAssert entryB(n, 1) == wantPipe, "repr cross-block pipelineRep agrees"

proc benchDhPipeline(n: int, args: seq[Value]) =
  let bnd = initRuntimeBindings()
  discard callValueFuncDir("", prog, "pipelineRep", args, bnd)
  let interpBody = proc(acc: var int) =
    acc += valueToInt(callValueFuncDir("", prog, "pipelineRep", args, bnd))
  let sbBody = proc(acc: var int) = acc += entryA(n, 1)
  let xbBody = proc(acc: var int) = acc += entryB(n, 1)
  let iIters = calibrateIters(interpBody)
  let sIters = calibrateIters(sbBody)
  let xIters = calibrateIters(xbBody)
  printProgramHeader("pipelineRep  (n=" & $n & ", nested cross-def Vec calls)",
    "interpreter: findDef + ETT interpreter + decode | " &
    "repr (same-block): host-native wrapper, same-block direct call | " &
    "repr (cross-block): host-native wrapper, #408 registry direct call | " &
    "no value row: requireCompiled blocks emit no Value-tier procs")
  let iMs = timeIters(interpBody, iIters)
  let sMs = timeIters(sbBody, sIters)
  let xMs = timeIters(xbBody, xIters)
  printPathRow(("interpreter", iMs, iIters).PathTime)
  printPathRow(("repr (same-block)", sMs, sIters).PathTime)
  printPathRow(("repr (cross-block)", xMs, xIters).PathTime)
  if sMs > 0.0:
    echo "   repr vs interpreter: ", (iMs / sMs).formatFloat(ffDecimal, 1), "x"
  if xMs > 0.0 and sMs > 0.0:
    echo "   cross-block vs same-block: ",
      (sMs / xMs).formatFloat(ffDecimal, 2), "x",
      "  (1.00 = the #408 registry call costs nothing measurable)"

proc benchDhScore(args: seq[Value], n: int) =
  let bnd = initRuntimeBindings()
  discard callValueFuncDir("", prog, "scoreOfRep", args, bnd)
  let interpBody = proc(acc: var int) =
    acc += scoreToInt(callValueFuncDir("", prog, "scoreOfRep", args, bnd))
  let valueBody = proc(acc: var int) =
    acc += scoreToInt(eponymCompiled_entryC(args, bnd))
  let iIters = calibrateIters(interpBody)
  let vIters = calibrateIters(valueBody)
  printProgramHeader("scoreOfRep  (n=" & $n & ", #402 derived Score mapping)",
    "interpreter: findDef + ETT interpreter + Score decode | " &
    "value: compiled Value proc + Score decode | " &
    "no repr row: the derived single-field-variant representation is " &
    "outside the Phase-2 codegen fragment (coverage finding, not a driver bug)")
  let iMs = timeIters(interpBody, iIters)
  let vMs = timeIters(valueBody, vIters)
  printPathRow(("interpreter", iMs, iIters).PathTime)
  printPathRow(("value", vMs, vIters).PathTime)
  if vMs > 0.0:
    echo "   value vs interpreter: ", (iMs / vMs).formatFloat(ffDecimal, 1), "x"

when isMainModule:
  const n = 200
  # pipelineRep = sum(ones) + sum(map dbl (ones)) = S + 2S, S = n
  let wantPipe = 3 * n
  checkAgreementDh(n, wantPipe, wantPipe)

  block:
    let args = @[natArgDh(n), intToValue(1)]
    benchDhPipeline(n, args)

  block:
    let args = @[natArgDh(n), intToValue(1)]
    benchDhScore(args, n)

  echo ""
  echo "bench_runtime_defheavy: all agreement checks passed"
