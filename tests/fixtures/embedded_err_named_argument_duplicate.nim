import eponym_mac

eponymBlock:
  postulate(Int, Univ)
  proc target(left, right: Int): Int = left
  proc bad(): Int = target(left = 1, left = 2)
