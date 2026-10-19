import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  proc legacyPartialCons(value: Nat, tail: Vec[Nat, 0]): Vec[Nat, 1] =
    cons[Nat](zero(), value, tail)
