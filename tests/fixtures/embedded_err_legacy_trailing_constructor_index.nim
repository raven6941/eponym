import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"

  data(LocalLastAt, Nat -> Univ):
    proc localLastAt(value: Nat, n: Nat): LocalLastAt[n]

  proc oldTrailingConstructorIndexApplication(value: Nat):
      LocalLastAt[0] = localLastAt(value, zero())
