import eponym_mac

eponymBlock:
  postulate(Int, Univ)
  postulate(identityInt, Int -> Int)
  proc throughPostulate(x {.linear.}: Int): Int = identityInt(x)
  runtimeDps(throughPostulate)
