import eponym_mac

eponymBlock:
  postulate(Nat, Univ)

  proc legacyCallback(
      callback: Pi(A: Univ, value: A, A), value: Nat): Nat =
    callback(Nat, value)
