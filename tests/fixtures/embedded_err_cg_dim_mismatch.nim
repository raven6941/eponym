import eponym_mac
eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  import "../../lib/float.ep"
  postulate(Mat, Nat -> Nat -> Univ)
  postulate(VecMatVec, Pi(n: Nat, Mat[n,n] -> Vec[Float,n] -> Vec[Float,n]))
  proc wrong(n: Nat, m: Mat[n,n], y: Vec[Float, 2]): Vec[Float,n] =
    VecMatVec(n, m, y)
  compileTimeOnly(wrong)
