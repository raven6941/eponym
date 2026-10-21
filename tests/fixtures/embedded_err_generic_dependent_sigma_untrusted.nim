import eponym_mac

type RuntimeChannel = object
  id: int

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  postulate(Int, Univ)
  postulate(Channel, Nat -> Univ)
  runtimeVector(Vec)
  runtimeType(Channel, RuntimeChannel)
  proc generatedDependentPairValue[
      pair: Sig(length: Nat, Channel[length])](ignored: Int):
      Sig(length: Nat, Channel[length]) = pair
  runtimeValue(generatedDependentPairValue)
