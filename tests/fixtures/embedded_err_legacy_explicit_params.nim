import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  proc oldCons(value: Nat): Vec[Nat, 1] =
    cons(Nat, zero(), value, vecnil[Nat]())
