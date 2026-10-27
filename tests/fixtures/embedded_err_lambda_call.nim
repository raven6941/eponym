import eponym_mac

eponymBlock:
  postulate(Nat, Univ)
  proc bad(x: Nat): Nat = lam(x, Nat, x)
