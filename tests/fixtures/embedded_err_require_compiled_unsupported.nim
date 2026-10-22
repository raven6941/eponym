import eponym_mac

eponymBlock:
  requireCompiled()
  import "../../lib/float.ep"
  runtimeType(Float, float64)
  proc identity(value: Float): Float = value
