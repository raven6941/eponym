import eponym_mac

eponymBlock:
  postulate(Nat, Univ)

  proc identityFactory(): Pi(A: Univ, value: A, A) =
    lam(A, Univ, lam(value, A, value))

  proc legacyAlias(value: Nat): Nat =
    let callback = identityFactory()
    callback(Nat, value)
