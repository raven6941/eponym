## Issue #409: `bindPostulateValue`-bound postulates applied at statically
## known types go through a generated typed adapter — a direct Nim call to
## the user's `(args, globals)` proc with baked type witnesses — instead of
## the `postulateValue` bindings-table lookup plus per-argument
## `vCompiledAppWithBindings` fold.
##
## The key assertion calls the compiled definition proc directly with
## EMPTY runtime bindings. The old fold path resolves the postulate through
## the bindings table, so it cannot produce a real result without the
## binding; the typed adapter calls the user's Nim proc by name and never
## consults the table. Observing the correct value therefore proves the
## call site was rerouted through the adapter.

import eponym_mac
import eponym_embed

var adapterArgCounts: seq[int] = @[]

proc recordingDebugEcho(args: seq[RuntimeValue],
                        globals: RuntimeGlobals): RuntimeValue =
  adapterArgCounts.add(args.len)
  args[1]

eponymBlock:
  postulate(Int, Univ)
  import "../lib/debug.ep"
  import "../lib/bool.ep"
  bindPostulateValue(debugEcho, recordingDebugEcho)
  proc echoInt(value: Int): Int = debugEcho[Int](value)
  proc echoBool(value: Bool): Bool = debugEcho[Bool](value)

when isMainModule:
  # 1. Direct call to the compiled proc with empty bindings: only the
  #    typed adapter can serve this, since the fold path needs the
  #    postulate's runtime binding.
  let direct = eponymCompiled_echoInt(@[intToValue(41)], initRuntimeBindings())
  doAssert valueToInt(direct) == 41,
    "issue #409: typed adapter should serve the call without runtime bindings"
  doAssert adapterArgCounts == @[2],
    "typed adapter should pass [typeWitness, value], got " & $adapterArgCounts

  # 2. End-to-end behavior through the wrappers is unchanged.
  doAssert echoInt(42) == 42
  doAssert echoBool(true) == true
  doAssert echoBool(false) == false
  doAssert adapterArgCounts == @[2, 2, 2, 2]
  echo "test_postulate_typed_adapter: typed-adapter reroute passed"
