import eponym_mac

eponymBlock:
  proc identity[A: Univ](value: A): A = value

  proc oldIdentity(value: Nat): Nat = identity Nat value
