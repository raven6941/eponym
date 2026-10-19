import eponym_mac

eponymBlock:
  postulate(Nat, Univ)

  proc legacyAscribedCallback(
      callback: Pi(A: Univ, value: A, A), value: Nat): Nat =
    (callback : Pi(A: Univ, value: A, A))(Nat, value)
