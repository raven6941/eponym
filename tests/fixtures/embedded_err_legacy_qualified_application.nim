import eponym_mac

eponymBlock:
  postulate(Nat, Univ)

  proc identity[A: Univ](value: A): A = value

  proc legacyQualified(value: Nat): Nat =
    namespace.identity(Nat, value)
