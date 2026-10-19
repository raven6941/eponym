import eponym_mac

eponymBlock:
  import "../../lib/bool.ep"
  postulate(Nat, Univ)

  proc makeIdentity(): Pi(A: Univ, value: A, A) =
    lam(A, Univ, lam(value, A, value))

  proc legacyConditionalHigherOrder(flag: Bool, value: Nat): Nat =
    (if flag: makeIdentity() else: makeIdentity())(Nat, value)
