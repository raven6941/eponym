import eponym_mac

eponymBlock:
  postulate(Nat, Univ)
  postulate(identityPostulate, Pi(A: Univ, x: A, A))

  proc oldIdentity(value: Nat): Nat = identityPostulate(Nat, value)
