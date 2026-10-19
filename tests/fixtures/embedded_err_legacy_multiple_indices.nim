import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  data(LocalPairIndex, Nat -> Univ):
    proc localPairIndex(m: Nat, n: Nat,
        left: Vec[Nat, m], right: Vec[Nat, n]): LocalPairIndex[add(m, n)]

  postulate(localIndexedPair,
    Pi(m: Nat, n: Nat, left: Vec[Nat, m], right: Vec[Nat, n],
      LocalPairIndex[add(m, n)]))

  proc oldPositionalIndexCall(m, n: Nat, left: Vec[Nat, m], right: Vec[Nat, n]):
      LocalPairIndex[add(m, n)] = localIndexedPair(m, n, left, right)
