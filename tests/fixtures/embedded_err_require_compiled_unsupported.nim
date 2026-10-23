import eponym_mac

eponymBlock:
  requireCompiled()
  postulate(Int, Univ)
  runtimeType(Int, int)
  # Higher-order binder domains stay outside the representation fragment:
  # the repr tier compiles first-order host signatures only.
  proc applyTwice(f: Int -> Int, x: Int): Int = f x
