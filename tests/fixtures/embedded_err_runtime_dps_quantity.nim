import eponym_mac

eponymBlock:
  postulate(Int, Univ)
  proc repeated(x: Int): Int = addInt(x, x)
  runtimeDps(repeated)
