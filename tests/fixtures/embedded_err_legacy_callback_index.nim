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

  proc oldResultOnlyCallbackApplication(
      callback: Pi(n: Nat, Vec[Nat, n])): Vec[Nat, 0] =
    callback(zero())

  proc oldConditionalCallbackApplication(
      left, right: Pi(n: Nat, Vec[Nat, n]), flag: Bool): Vec[Nat, 0] =
    let selected = if flag: left else: right
    selected(zero())

  proc oldShadowedCallbackApplication(
      callback: Pi(n: Nat, Pi(n: Nat, Vec[Nat, n]))): Vec[Nat, 0] =
    callback(zero(), zero())
