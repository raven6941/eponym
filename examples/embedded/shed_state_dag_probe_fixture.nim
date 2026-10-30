import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  postulate(Int, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  proc double(x: Int): Int = addInt(x, x)
  proc first(x: Int): Int = ![firstBody]
  proc sibling(x: Int): Int = ![siblingBody]
