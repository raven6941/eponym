import std/options
import eponym_mac

eponymBlock:
  import "../../lib/option.ep"
  postulate(Int, Univ)
  runtimeOption(Option)
  postulate(addInt, Int -> Int -> Int)
  proc badLinearOptionDuplicate(optionValue: Option[Int],
                                value {.linear.}: Int): Int =
    (optionElim[Int, lam(u: Option[Int]) => Pi(unit: unitTy, Int)](
      lam(unit: unitTy) => value,
      lam(payload: Int) => lam(unit: unitTy) => addInt(value, value),
      optionValue))(unitv)

discard badLinearOptionDuplicate(none(int), 7)
