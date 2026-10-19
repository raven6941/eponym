import std/options
import ../../src/eponym/eponym_mac

proc boolOptionIdentity(value: Option[bool]): Option[bool] = value

eponymBlock:
  import "../../lib/bool.ep"
  import "../../lib/option.ep"
  postulate(Int, Univ)
  postulate(useIntOption, Option[Int] -> Option[Int])
  runtimeOption(Option)
  bindPostulate(useIntOption, boolOptionIdentity,
    Option[Bool], Option[Bool])
  proc badRole(value: Option[Int]): Option[Int] = useIntOption(value)
