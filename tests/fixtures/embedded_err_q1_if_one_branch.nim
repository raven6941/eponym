import eponym_mac

eponymBlock:
  import "../../lib/bool.ep"
  postulate(Int, Univ)
  proc dropsLinearValue(flag: Bool, value {.linear.}: Int): Int =
    if flag: value else: 0
