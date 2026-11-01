## Runtime shape failure at a bindPostulateValue boundary (issue #501).
import eponym_mac
import eponym_embed
import eponym_init

proc fixtureEcho(args: seq[RuntimeValue],
                globals: RuntimeGlobals): RuntimeValue = args[1]

eponymRuntimeBridgeTestBlock:
  postulate(Int, Univ)
  runtimeType(Int, int)
  import "../../lib/debug.ep"
  bindPostulateValue(debugEcho, fixtureEcho)
  proc keepTypedAdapterLive(): Int = debugEcho[Int](0)

when isMainModule:
  # Exercise the generated adapter directly with a Bool-shaped Value.
  discard eponymTypedAdapter_debugEcho_Int_1(initRuntimeBindings(),
    constValue(cVoid))
