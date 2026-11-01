## Runtime function-shape failure at a bindPostulateValue boundary (issue #501).
import eponym_mac
import eponym_embed

proc fixtureApply(args: seq[RuntimeValue],
                 globals: RuntimeGlobals): RuntimeValue = args[0]

eponymRuntimeBridgeTestBlock:
  postulate(Int, Univ)
  postulate(applyCallback,
    Pi(k: Pi(x: Int, Int), Int))
  runtimeType(Int, int)
  import "../../lib/debug.ep"
  bindPostulateValue(applyCallback, fixtureApply)
  proc keepTypedAdapterLive(): Int =
    applyCallback(lam(x: Int) => x)

when isMainModule:
  # The adapter expects a function-shaped Value, but receives a scalar.
  discard eponymTypedAdapter_applyCallback_1(initRuntimeBindings(),
    intToValue(7))
