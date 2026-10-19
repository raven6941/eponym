import eponym_mac

eponymBlock:
  postulate(Nat, Univ)

  proc makeIdentity(): Pi(A: Univ, value: A, A) =
    lam(A, Univ, lam(value, A, value))

  proc legacyHigherOrder(value: Nat): Nat =
    makeIdentity()(Nat, value)
