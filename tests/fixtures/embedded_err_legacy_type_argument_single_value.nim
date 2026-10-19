import eponym_mac

eponymBlock:
  proc oldTypeArgumentLooksLikeValue(
      callback: Pi(A: Univ, value: A, A), value: Nat): Nat =
    callback(value)
