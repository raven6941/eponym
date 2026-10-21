import eponym_mac

type RuntimeSizedChannel = object
  id: int

type RuntimeSizedVec = object
  length: int
  values: seq[int]
  pair: tuple[index: int, channel: RuntimeSizedChannel]

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  postulate(Int, Univ)
  postulate(Channel, Nat -> Univ)
  runtimeType(Channel, RuntimeSizedChannel)
  runtimeVector(Vec)
  record(SizedVec):
    field(length, Nat)
    field(values, Vec[Int, length])
    field(pair, Sig(index: Nat, Channel[index]))
  runtimeType(SizedVec, RuntimeSizedVec)
  proc generatedDependentRecordValue[value: SizedVec](ignored: Int):
      SizedVec = value
  runtimeValue(generatedDependentRecordValue)
