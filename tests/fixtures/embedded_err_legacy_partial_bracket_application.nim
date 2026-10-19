import eponym_mac

eponymBlock:
  postulate(Nat, Univ)
  postulate(Bool, Univ)

  proc genericTwo[A: Univ, B: Univ](value: A): A = value

  proc missingBracket(value: Nat): Nat =
    genericTwo[Nat](value)
