## A checked debug postulate emits one trace per runtime call and returns its
## input unchanged.

import falsify
import eponym_mac
import eponym_embed

var debugTrace: seq[string] = @[]
var debugCalls = 0

proc captureDebugEcho(args: seq[RuntimeValue],
                      globals: RuntimeGlobals): RuntimeValue =
  inc debugCalls
  debugTrace.add(runtimeValueDebugString(args[1], globals))
  args[1]

eponymBlock:
  postulate(Int, Univ)
  import "../lib/debug.ep"
  bindPostulateValue(debugEcho, captureDebugEcho)
  proc checkedDebugEchoInt(value: Int): Int = debugEcho[Int](value)

when isMainModule:
  var rng = initRng(20261021'u64)
  let debugCases = forAll("checked debug echo preserves values and emits once",
    rng, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let priorCount = debugTrace.len
      let resultValue = checkedDebugEchoInt(value)
      resultValue == value and debugTrace.len == priorCount + 1 and
        debugTrace[^1] == $value,
    shrinkInt)
  if not debugCases or debugCalls != 200:
    quit(1)
  echo "test_debug_echo: runtime trace property passed"
