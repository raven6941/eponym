import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"
  postulate(Int, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  proc keepVector(n: Nat, values: Vec[Int, n]): Vec[Int, n] = values
