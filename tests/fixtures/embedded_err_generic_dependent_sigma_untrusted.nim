import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  postulate(Int, Univ)
  proc generatedDependentPairValue[
      pair: Sig(length: Nat, Vec[Int, length])](ignored: Int):
      Sig(length: Nat, Vec[Int, length]) = pair
  runtimeValue(generatedDependentPairValue)
