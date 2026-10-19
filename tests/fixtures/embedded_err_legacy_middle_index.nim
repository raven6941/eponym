import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/bool.ep"
  import "../../lib/vec.ep"

  data(LocalMiddleIndex, Nat -> Univ):
    proc localMiddleIndex(flag: Bool, n: Nat, values: Vec[Nat, n]):
        LocalMiddleIndex[n]

  proc oldCall(flag: Bool, values: Vec[Nat, 0]): LocalMiddleIndex[0] =
    localMiddleIndex(flag, zero(), values)
