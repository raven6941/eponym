import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/bool.ep"
  import "../../lib/vec.ep"

  data(LocalAt, Nat -> Univ):
    proc localAt(n: Nat, value: Nat): LocalAt[n]

  proc oldCallbackApplication(
      callback: Pi(flag: Bool, n: Nat, values: Vec[Nat, n], LocalAt[n]),
      flag: Bool, values: Vec[Nat, 0]): LocalAt[0] =
    callback(flag, zero(), values)
