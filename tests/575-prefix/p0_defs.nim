## CG-as-Bayesian-inference proof smoke test for #569, Phase 3.
## (A) is Corollary 2.4 at M = 1.  (B) is Lemma 3.2 at M = 2 only.
## (B) takes two named hypotheses: conjugacy (c1^T y2 = 0, gramOffDiag)
## and cross-symmetry (d1^T y2 = d2^T y1, crossSym); lemmaB is
## sequential2 = batch2, assembled from lemmaA31/lemmaA32, distribU1/U2,
## single/double scalar bridges, and the regroup procs.
## The 4.14 object checked below is a variance identity, not a bound.
## Elaboration needs raised VM fuel: --maxCallDepthVM:30000
## --maxLoopIterationsVM:1000000000 (see tools/ci-local.sh).
## halfF (the value 1/2) is an unbound postulate, part of the trust
## boundary; used only in compileTimeOnly proof types.
import eponym_mac
import math

type FMat = seq[seq[float]]
proc hMul(a,b: float): float = a*b
proc hDiv(a,b: float): float = a/b
proc hRecip(a: float): float = 1.0/a
proc hSub(a,b: float): float = a-b
proc hSubV(a,b: seq[float]): seq[float] =
  result = newSeq[float](a.len)
  for i in 0..<a.len: result[i] = a[i]-b[i]
proc addv(a,b: seq[float]): seq[float] =
  result = newSeq[float](a.len)
  for i in 0..<a.len: result[i] = a[i]+b[i]
proc subv(a,b: seq[float]): seq[float] =
  result = newSeq[float](a.len)
  for i in 0..<a.len: result[i] = a[i]-b[i]
proc sv(c: float, a: seq[float]): seq[float] =
  result = newSeq[float](a.len)
  for i in 0..<a.len: result[i] = c*a[i]
proc hOuter(a,b: seq[float]): FMat =
  result = newSeq[seq[float]](a.len)
  for i in 0..<a.len:
    result[i] = newSeq[float](b.len)
    for j in 0..<b.len: result[i][j] = a[i]*b[j]
proc hTranspose(a: FMat): FMat =
  result = newSeq[seq[float]](a[0].len)
  for i in 0..<a[0].len:
    result[i] = newSeq[float](a.len)
    for j in 0..<a.len: result[i][j] = a[j][i]
proc hMatAdd(a,b: FMat): FMat =
  result = newSeq[seq[float]](a.len)
  for i in 0..<a.len:
    result[i] = newSeq[float](a[i].len)
    for j in 0..<a[i].len: result[i][j] = a[i][j]+b[i][j]
proc hMatSub(a,b: FMat): FMat =
  result = newSeq[seq[float]](a.len)
  for i in 0..<a.len:
    result[i] = newSeq[float](a[i].len)
    for j in 0..<a[i].len: result[i][j] = a[i][j]-b[i][j]
proc hScal(a: float; b: FMat): FMat =
  result = newSeq[seq[float]](b.len)
  for i in 0..<b.len:
    result[i] = newSeq[float](b[i].len)
    for j in 0..<b[i].len: result[i][j] = a*b[i][j]
proc hDot(a,b: seq[float]): float =
  for i in 0..<a.len: result += a[i]*b[i]
proc hVec(a: FMat; x: seq[float]): seq[float] =
  result = newSeq[float](a.len)
  for i in 0..<a.len:
    for j in 0..<x.len: result[i] += a[i][j]*x[j]

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/vec.ep"
  import "../lib/float.ep"
  import "../lib/eq.ep"
  import "../lib/calc.ep"
  postulate(Int, Univ)
  runtimeType(Float, float)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  postulate(Mat, Nat -> Nat -> Univ)
  runtimeType(Mat, FMat)
  postulate(mulF, Float -> Float -> Float)
  bindPostulate(mulF, hMul, Float, Float, Float)
  postulate(subF, Float -> Float -> Float)
  bindPostulate(subF, hSub, Float, Float, Float)
  postulate(divF, Float -> Float -> Float)
  bindPostulate(divF, hDiv, Float, Float, Float)
  postulate(recipF, Float -> Float)
  bindPostulate(recipF, hRecip, Float, Float)
  postulate(dot, Pi(n: Nat, Vec[Float,n] -> Vec[Float,n] -> Float))
  bindPostulate(dot, hDot, Vec, Vec, Float)
  postulate(matVec, Pi(n: Nat, Mat[n,n] -> Vec[Float,n] -> Vec[Float,n]))
  bindPostulate(matVec, hVec, Mat, Vec, Vec)
  postulate(outer, Pi(n: Nat, Vec[Float,n] -> Vec[Float,n] -> Mat[n,n]))
  bindPostulate(outer, hOuter, Vec, Vec, Mat)
  postulate(transpose, Pi(n: Nat, Mat[n,n] -> Mat[n,n]))
  bindPostulate(transpose, hTranspose, Mat, Mat)
  postulate(matAdd, Pi(n: Nat, Mat[n,n] -> Mat[n,n] -> Mat[n,n]))
  bindPostulate(matAdd, hMatAdd, Mat, Mat, Mat)
  postulate(matSub, Pi(n: Nat, Mat[n,n] -> Mat[n,n] -> Mat[n,n]))
  bindPostulate(matSub, hMatSub, Mat, Mat, Mat)
  postulate(scalMat, Pi(n: Nat, Float -> Mat[n,n] -> Mat[n,n]))
  bindPostulate(scalMat, hScal, Float, Mat, Mat)
  postulate(halfF, Float)
  postulate(zeroF, Float)

  # These are algebraic/model facts, not the identities under test.
  postulate(matVecWSym, Pi(n: Nat, W: Mat[n,n], y: Vec[Float,n],
    Eq[Vec[Float,n], matVec(n, transpose(n, W), y), matVec(n,W,y)]))
  postulate(dotSymW, Pi(n: Nat, W: Mat[n,n], y: Vec[Float,n],
    Eq[Float, dot(n,matVec(n,W,y),y), dot(n,y,matVec(n,W,y))]))
  postulate(solCov, Pi(n: Nat, Mat[n,n] -> Vec[Float,n] -> Mat[n,n]))
  postulate(kronProj, Pi(n: Nat, W: Mat[n,n], y: Vec[Float,n], Mat[n,n]))
  postulate(projectionRule, Pi(n: Nat, W: Mat[n,n], y: Vec[Float,n],
    Eq[Mat[n,n], solCov(n,W,y), kronProj(n,W,y)]))
  postulate(symKronAction, Pi(n: Nat, W: Mat[n,n], y: Vec[Float,n],
    Eq[Mat[n,n], kronProj(n,W,y),
      scalMat(n, halfF, matAdd(n, scalMat(n, dot(n,y,matVec(n,W,y)), W),
        outer(n, matVec(n,W,y), matVec(n,W,y))))]))
  postulate(matSubVec, Pi(n: Nat, Vec[Float,n] -> Vec[Float,n] -> Vec[Float,n]))
  bindPostulate(matSubVec, hSubV, Vec, Vec, Vec)
  postulate(vecAdd, Pi(n: Nat, Vec[Float,n] -> Vec[Float,n] -> Vec[Float,n]))
  bindPostulate(vecAdd, addv, Vec, Vec, Vec)
  postulate(scalVec, Pi(n: Nat, Float -> Vec[Float,n] -> Vec[Float,n]))
  bindPostulate(scalVec, sv, Float, Vec, Vec)
  proc dennis(n: Nat, H: Mat[n,n], s: Vec[Float,n], y: Vec[Float,n],
      c: Vec[Float,n]): Mat[n,n] =
      matAdd(n, H, matSub(n,
      matAdd(n, scalMat(n, recipF(dot(n,c,y)), outer(n, matSubVec(n,s,matVec(n,H,y)), c)),
        scalMat(n, recipF(dot(n,c,y)), outer(n, c, matSubVec(n,s,matVec(n,H,y))))),
      scalMat(n, divF(dot(n,y,matSubVec(n,s,matVec(n,H,y))),
        mulF(dot(n,c,y),dot(n,c,y))), outer(n,c,c))))
  proc postMean(n: Nat, H: Mat[n,n], W: Mat[n,n], s: Vec[Float,n], y: Vec[Float,n]): Mat[n,n] =
    matAdd(n, H, matSub(n,
      matAdd(n, scalMat(n, recipF(dot(n,y,matVec(n,W,y))),
        outer(n, matSubVec(n,s,matVec(n,H,y)), matVec(n,transpose(n, W),y))),
        scalMat(n, recipF(dot(n,y,matVec(n,W,y))),
          outer(n,matVec(n,W,y),matSubVec(n,s,matVec(n,H,y))))),
      scalMat(n, divF(dot(n,y,matSubVec(n,s,matVec(n,H,y))),
        mulF(dot(n,y,matVec(n,W,y)),dot(n,y,matVec(n,W,y)))),
        outer(n,matVec(n,W,y),matVec(n,transpose(n,W),y)))))
  postulate(gramOffDiag, Pi(n: Nat, W: Mat[n,n], y1: Vec[Float,n], y2: Vec[Float,n],
    Eq[Float, dot(n,matVec(n,W,y1),y2), zeroF]))
  # (B) single-step algebra (postulated, same trust class as matVecWSym).
  postulate(zeroVec, Pi(n: Nat, Vec[Float,n]))
  postulate(matVecAdd, Pi(n: Nat, A: Mat[n,n], B: Mat[n,n], y: Vec[Float,n],
    Eq[Vec[Float,n], matVec(n, matAdd(n,A,B), y),
      vecAdd(n, matVec(n,A,y), matVec(n,B,y))]))
  postulate(matVecSub, Pi(n: Nat, A: Mat[n,n], B: Mat[n,n], y: Vec[Float,n],
    Eq[Vec[Float,n], matVec(n, matSub(n,A,B), y),
      matSubVec(n, matVec(n,A,y), matVec(n,B,y))]))
  postulate(matVecScal, Pi(n: Nat, a: Float, A: Mat[n,n], y: Vec[Float,n],
    Eq[Vec[Float,n], matVec(n, scalMat(n,a,A), y), scalVec(n, a, matVec(n,A,y))]))
  postulate(matVecOuter, Pi(n: Nat, u: Vec[Float,n], v: Vec[Float,n], y: Vec[Float,n],
    Eq[Vec[Float,n], matVec(n, outer(n,u,v), y), scalVec(n, dot(n,v,y), u)]))
  postulate(dotSub, Pi(n: Nat, u: Vec[Float,n], v: Vec[Float,n], y: Vec[Float,n],
    Eq[Float, dot(n, matSubVec(n,u,v), y), subF(dot(n,u,y), dot(n,v,y))]))
  postulate(dotScal, Pi(n: Nat, a: Float, u: Vec[Float,n], y: Vec[Float,n],
    Eq[Float, dot(n, scalVec(n,a,u), y), mulF(a, dot(n,u,y))]))
  postulate(dotSym, Pi(n: Nat, u: Vec[Float,n], v: Vec[Float,n],
    Eq[Float, dot(n,u,v), dot(n,v,u)]))
  postulate(mulFZero, Pi(a: Float, Eq[Float, mulF(a, zeroF), zeroF]))
  postulate(subFZero, Pi(a: Float, Eq[Float, subF(a, zeroF), a]))
  postulate(mulFRecipDiv, Pi(a: Float, b: Float,
    Eq[Float, mulF(recipF(a), b), divF(b, a)]))
  postulate(vecAddZero, Pi(n: Nat, u: Vec[Float,n],
    Eq[Vec[Float,n], vecAdd(n, u, zeroVec(n)), u]))
  postulate(vecAddZeroL, Pi(n: Nat, u: Vec[Float,n],
    Eq[Vec[Float,n], vecAdd(n, zeroVec(n), u), u]))
  postulate(vecSubZero, Pi(n: Nat, u: Vec[Float,n],
    Eq[Vec[Float,n], matSubVec(n, u, zeroVec(n)), u]))
  postulate(scalVecZero, Pi(n: Nat, u: Vec[Float,n],
    Eq[Vec[Float,n], scalVec(n, zeroF, u), zeroVec(n)]))
  postulate(scalVecComp, Pi(n: Nat, a: Float, b: Float, u: Vec[Float,n],
    Eq[Vec[Float,n], scalVec(n, a, scalVec(n, b, u)), scalVec(n, mulF(a,b), u)]))
  postulate(matSubVecAdd, Pi(n: Nat, s: Vec[Float,n], u: Vec[Float,n], v: Vec[Float,n],
    Eq[Vec[Float,n], matSubVec(n, s, vecAdd(n,u,v)),
      matSubVec(n, matSubVec(n,s,u), v)]))
  postulate(outerSubL, Pi(n: Nat, u: Vec[Float,n], v: Vec[Float,n], w: Vec[Float,n],
    Eq[Mat[n,n], outer(n, matSubVec(n,u,v), w),
      matSub(n, outer(n,u,w), outer(n,v,w))]))
  postulate(outerSubR, Pi(n: Nat, u: Vec[Float,n], v: Vec[Float,n], w: Vec[Float,n],
    Eq[Mat[n,n], outer(n, u, matSubVec(n,v,w)),
      matSub(n, outer(n,u,v), outer(n,u,w))]))
  postulate(outerScalL, Pi(n: Nat, a: Float, u: Vec[Float,n], v: Vec[Float,n],
    Eq[Mat[n,n], outer(n, scalVec(n,a,u), v), scalMat(n, a, outer(n,u,v))]))
  postulate(outerScalR, Pi(n: Nat, a: Float, u: Vec[Float,n], v: Vec[Float,n],
    Eq[Mat[n,n], outer(n, u, scalVec(n,a,v)), scalMat(n, a, outer(n,u,v))]))
  # (B) assembly algebra: single-step distribution / regrouping.
  postulate(scalMatSub, Pi(n: Nat, a: Float, A: Mat[n,n], B: Mat[n,n],
    Eq[Mat[n,n], scalMat(n,a,matSub(n,A,B)),
      matSub(n,scalMat(n,a,A),scalMat(n,a,B))]))
  postulate(scalMatComp, Pi(n: Nat, a: Float, b: Float, A: Mat[n,n],
    Eq[Mat[n,n], scalMat(n,a,scalMat(n,b,A)), scalMat(n,mulF(a,b),A)]))
  postulate(scalMatAdd, Pi(n: Nat, a: Float, A: Mat[n,n], B: Mat[n,n],
    Eq[Mat[n,n], scalMat(n,a,matAdd(n,A,B)),
      matAdd(n,scalMat(n,a,A),scalMat(n,a,B))]))
  postulate(mulFRecipDiv2, Pi(a: Float, b: Float, c: Float,
    Eq[Float, mulF(recipF(a),divF(b,c)), divF(b,mulF(c,a))]))
  postulate(mulFComm, Pi(a: Float, b: Float, Eq[Float, mulF(a,b), mulF(b,a)]))
  postulate(matAddAssoc, Pi(n: Nat, A: Mat[n,n], B: Mat[n,n], C: Mat[n,n],
    Eq[Mat[n,n], matAdd(n,matAdd(n,A,B),C), matAdd(n,A,matAdd(n,B,C))]))
  postulate(matAddComm, Pi(n: Nat, A: Mat[n,n], B: Mat[n,n],
    Eq[Mat[n,n], matAdd(n,A,B), matAdd(n,B,A)]))
  postulate(matSubAdd, Pi(n: Nat, A: Mat[n,n], B: Mat[n,n], C: Mat[n,n],
    Eq[Mat[n,n], matSub(n,matAdd(n,A,B),C), matAdd(n,matSub(n,A,C),B)]))
  postulate(matAddSub, Pi(n: Nat, A: Mat[n,n], B: Mat[n,n], C: Mat[n,n],
    Eq[Mat[n,n], matAdd(n,A,matSub(n,B,C)), matSub(n,matAdd(n,A,B),C)]))
  postulate(matSubSub, Pi(n: Nat, A: Mat[n,n], B: Mat[n,n], C: Mat[n,n],
    Eq[Mat[n,n], matSub(n,matSub(n,A,B),C), matSub(n,A,matAdd(n,B,C))]))
  # xHat is computed by the host cross-check; it is not a checked primitive.

  proc resid(n: Nat, H: Mat[n,n], s: Vec[Float,n], y: Vec[Float,n]): Vec[Float,n] =
    matSubVec(n,s,matVec(n,H,y))
  proc dennisStep(n: Nat, H: Mat[n,n], W: Mat[n,n], s: Vec[Float,n], y: Vec[Float,n]): Mat[n,n] =
    dennis(n,H,s,y,matVec(n,W,y))
  proc sequential2(n: Nat, H: Mat[n,n], W: Mat[n,n], s1: Vec[Float,n], y1: Vec[Float,n], s2: Vec[Float,n], y2: Vec[Float,n]): Mat[n,n] =
    dennisStep(n,dennisStep(n,H,W,s1,y1),W,s2,y2)
  proc batchSingle(n: Nat, H: Mat[n,n], W: Mat[n,n], s1: Vec[Float,n], y1: Vec[Float,n], s2: Vec[Float,n], y2: Vec[Float,n]): Mat[n,n] =
    matAdd(n,scalMat(n,recipF(dot(n,y1,matVec(n,W,y1))),matAdd(n,outer(n,resid(n,H,s1,y1),matVec(n,W,y1)),outer(n,matVec(n,W,y1),resid(n,H,s1,y1)))),scalMat(n,recipF(dot(n,y2,matVec(n,W,y2))),matAdd(n,outer(n,resid(n,H,s2,y2),matVec(n,W,y2)),outer(n,matVec(n,W,y2),resid(n,H,s2,y2)))))
  proc batchDouble(n: Nat, H: Mat[n,n], W: Mat[n,n], s1: Vec[Float,n], y1: Vec[Float,n], s2: Vec[Float,n], y2: Vec[Float,n]): Mat[n,n] =
    matAdd(n,matAdd(n,scalMat(n,divF(dot(n,resid(n,H,s1,y1),y1),mulF(dot(n,y1,matVec(n,W,y1)),dot(n,y1,matVec(n,W,y1)))),outer(n,matVec(n,W,y1),matVec(n,W,y1))),scalMat(n,divF(dot(n,resid(n,H,s1,y1),y2),mulF(dot(n,y1,matVec(n,W,y1)),dot(n,y2,matVec(n,W,y2)))),outer(n,matVec(n,W,y1),matVec(n,W,y2)))),matAdd(n,scalMat(n,divF(dot(n,resid(n,H,s2,y2),y1),mulF(dot(n,y2,matVec(n,W,y2)),dot(n,y1,matVec(n,W,y1)))),outer(n,matVec(n,W,y2),matVec(n,W,y1))),scalMat(n,divF(dot(n,resid(n,H,s2,y2),y2),mulF(dot(n,y2,matVec(n,W,y2)),dot(n,y2,matVec(n,W,y2)))),outer(n,matVec(n,W,y2),matVec(n,W,y2)))))
  proc batch2(n: Nat, H: Mat[n,n], W: Mat[n,n], s1: Vec[Float,n], y1: Vec[Float,n], s2: Vec[Float,n], y2: Vec[Float,n]): Mat[n,n] =
    matAdd(n,H,matSub(n,batchSingle(n,H,W,s1,y1,s2,y2),batchDouble(n,H,W,s1,y1,s2,y2)))



# --- #575 measurement stubs: trivial uses so cut-off prefixes elaborate ---
  proc use575SubF(a0: Float, a1: Float): Float =
    subF(a0, a1)
  proc use575VecAdd(n: Nat, a0: Vec[Float,n], a1: Vec[Float,n]): Vec[Float,n] =
    vecAdd(n, a0, a1)
  proc use575ScalVec(n: Nat, a0: Float, a1: Vec[Float,n]): Vec[Float,n] =
    scalVec(n, a0, a1)

  compileTimeOnly(dennis)
  compileTimeOnly(postMean)
  compileTimeOnly(resid)
  compileTimeOnly(dennisStep)
  compileTimeOnly(sequential2)
  compileTimeOnly(batchSingle)
  compileTimeOnly(batchDouble)
  compileTimeOnly(batch2)
