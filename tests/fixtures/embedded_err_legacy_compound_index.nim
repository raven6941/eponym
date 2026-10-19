import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"

  data(LocalPairIndex, Nat -> Univ):
    proc localPairIndex(m: Nat, n: Nat,
        left: Vec[Nat, m], right: Vec[Nat, n]): LocalPairIndex[add(m, n)]

  proc oldCall(left: Vec[Nat, 1], right: Vec[Nat, 2]):
      LocalPairIndex[add(1, 2)] =
    localPairIndex(1, 2, left, right)
