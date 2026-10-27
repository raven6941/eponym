import eponym_mac

eponymBlock:
  postulate(Int, Univ)
  proc generatedAdder(seed: Int): proc(value: Int): Int =
    lam(value: Int) => addInt(seed, value)

discard generatedAdder(3)
