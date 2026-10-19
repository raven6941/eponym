import eponym_mac

eponymBlock:
  postulate(Nat, Univ)

  proc legacyCallbackAfterTerm(
      callback: Nat -> Pi(A: Univ, value: A, A), argument, value: Nat): Nat =
    callback(argument)(Nat, value)
