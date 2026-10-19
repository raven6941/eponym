import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"

  data(LocalAt, Nat -> Univ):
    proc localAt(n: Nat, value: Nat): LocalAt[n]

  record(LocalIndexedCallableField):
    field(make, Pi(value: Nat, n: Nat, LocalAt[n]))

  proc oldTrailingCallableFieldIndexApplication(
      handler: LocalIndexedCallableField, value: Nat): LocalAt[0] =
    handler.make(value, zero())
