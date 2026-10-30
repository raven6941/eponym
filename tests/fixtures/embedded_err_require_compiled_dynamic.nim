import eponym_mac

eponymBlock:
  postulate(Int, Univ)
  runtimeType(Int, int)
  proc identity(value: Int): Int = value
  runtimeValue(identity)
