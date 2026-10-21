import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  proc generatedDependentPairValue[
      pair: Sig(length: Nat, Sig(marker: Int, Vec[Int, length]))](ignored: Int):
      Sig(length: Nat, Sig(marker: Int, Vec[Int, length])) = pair
  runtimeValue(generatedDependentPairValue)
