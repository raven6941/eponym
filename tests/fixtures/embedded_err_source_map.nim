import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  postulate(Nat, Univ)
  proc badResult(value: Int): Nat =
    value
