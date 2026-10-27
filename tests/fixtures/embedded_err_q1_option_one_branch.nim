import std/options
import eponym_mac

eponymBlock:
  import "../../lib/option.ep"
  postulate(Int, Univ)
  runtimeOption(Option)
  proc badLinearOptionDrop(optionValue: Option[Int],
                           value {.linear.}: Int): Int =
    (optionElim[Int, lam(u: Option[Int]) => Pi(unit: unitTy, Int)](
      lam(unit: unitTy) => value,
      lam(payload: Int) => lam(unit: unitTy) => 0,
      optionValue))(unitv)

discard badLinearOptionDrop(none(int), 7)
