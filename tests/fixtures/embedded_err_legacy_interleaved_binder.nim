import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  proc oldTypeArgumentAfterIndex(
      callback: Pi(n: Nat, A: Univ, value: A, Vec[A, n])):
      Pi(value: Nat, Vec[Nat, 0]) =
    callback[zero()](Nat)
