import eponym_mac

eponymBlock:
  import "../../lib/bool.ep"

  data(LocalAt, Nat -> Univ):
    proc localAt(n: Nat, value: Nat): LocalAt[n]

  proc oldConditionalTrailingIndex(
      chooseFirst: Bool,
      first: Pi(value: Nat, n: Nat, LocalAt[n]),
      second: Pi(value: Nat, n: Nat, LocalAt[n]),
      value: Nat): LocalAt[0] =
    ((if chooseFirst: first else: second)(value))(zero())
