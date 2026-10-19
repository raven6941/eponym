import eponym_mac
import std/options

eponymBlock:
  postulate(Int, Univ)
  data(Option, Univ):
    proc none(): Option
    proc some(value: Int): Option
  runtimeOption(Option)
  proc identity(value: Option): Option = value

discard identity(none())
