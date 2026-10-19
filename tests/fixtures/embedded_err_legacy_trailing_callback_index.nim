import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"

  proc oldTrailingCallbackIndexApplication(
      callback: Pi(value: Nat, n: Nat, Vec[Nat, n]), value: Nat):
      Vec[Nat, 0] = callback(value, zero())
