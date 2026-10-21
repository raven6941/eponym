import eponym_mac

type RuntimeSizedVec = object
  length: int
  values: seq[int]

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  postulate(Int, Univ)
  record(SizedVec):
    field(length, Nat)
    field(values, Vec[Int, length])
  runtimeType(SizedVec, RuntimeSizedVec)
  proc generatedDependentRecordValue[value: SizedVec](ignored: Int):
      SizedVec = value
  runtimeValue(generatedDependentRecordValue)
