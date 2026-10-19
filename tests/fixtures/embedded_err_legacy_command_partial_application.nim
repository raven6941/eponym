import eponym_mac

eponymBlock:
  proc oldCallStyleAfterCommandPartial(
      callback: Pi(flag: Bool, value: Nat, A: Univ, input: A, A),
      flag: Bool, value: Nat): Nat =
    (callback flag value)(Nat, value)
