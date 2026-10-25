import sheds_mac

shedsBlock:
  import "../../lib/nat.ep"
  postulate(Int, Univ)
  proc double(x: Int): Int = addInt(x, x)
  proc first(x: Int): Int = ![firstBody]
  proc sibling(x: Int): Int = ![siblingBody]
