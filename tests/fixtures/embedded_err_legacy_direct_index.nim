import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"

  data(LocalAt, Nat -> Univ):
    proc localAt(n: Nat, value: Nat): LocalAt[n]

  proc oldIndexArgument(value: Nat): LocalAt[zero()] =
    localAt(zero(), value)
