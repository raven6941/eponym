import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"
  import "../../lib/bool.ep"

  proc indexHead[n: Nat](xs, ys: Vec[Nat, n]): Vec[Nat, n] = xs

  proc oldIndexCall(enabled: Bool):
      Vec[Nat, 0] -> Vec[Nat, 0] -> Vec[Nat, 0] =
    let index = if enabled: zero() else: suc(zero())
    indexHead(index)
