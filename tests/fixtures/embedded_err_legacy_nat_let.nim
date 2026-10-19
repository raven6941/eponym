import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  proc indexHead[n: Nat](xs, ys: Vec[Nat, n]): Vec[Nat, n] = xs

  proc oldIndexCall():
      Vec[Nat, 0] -> Vec[Nat, 0] -> Vec[Nat, 0] =
    let index = zero()
    indexHead(index)
