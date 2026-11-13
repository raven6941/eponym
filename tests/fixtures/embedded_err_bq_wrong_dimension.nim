import eponym_mac

type FMat = seq[seq[float]]

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  import "../../lib/float.ep"
  postulate(Mat, Nat -> Nat -> Univ)
  runtimeType(Float, float)
  runtimeType(Mat, FMat)
  runtimeVector(Vec)
  postulate(matVec, Pi(n: Nat, Mat[n, n] -> Vec[Float, n] -> Vec[Float, n]))
  proc wrongDimension(K: Mat[2, 2], z: Vec[Float, 3]): Vec[Float, 3] =
    matVec(2, K, z)
  compileTimeOnly(wrongDimension)
