import std/options
import ../../src/eponym/eponym_mac

proc boolOptionIdentity(value: Option[bool]): Option[bool] = value

eponymBlock:
  import "runtime_imported_option.ep"
  runtimeOption(Option)
  bindPostulate(useIntOption, boolOptionIdentity,
    Option[Bool], Option[Bool])
  proc badRole(value: Option[Int]): Option[Int] = useIntOption(value)
