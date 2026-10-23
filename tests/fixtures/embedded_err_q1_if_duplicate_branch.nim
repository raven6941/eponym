import eponym_mac

eponymBlock:
  import "../../lib/bool.ep"
  postulate(Int, Univ)
  proc duplicatesLinearValue(flag: Bool, value {.linear.}: Int): Int =
    if flag:
      addInt (value) (value)
    else:
      value
