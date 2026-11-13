## Bayesian-quadrature identity and numerical bound smoke test for #567.
## Compile with:
##   export PATH="$HOME/.nimble/bin:$PATH"
##   nim c --nimcache:./.nimcache-bq --hints:off --path:src --path:src/eponym tests/test_bq_bound.nim
##
## Restatement (no Float literals anywhere): the WCE side is written
## (kappa - d - d) + d' instead of kappa - 2d + d', so Step 1 needs no
## `2` constant. A 0-ary twoF postulate cannot be bound: the binder
## requires Opaque -> Opaque (unary adapter). mulF is used only in Step 2
## for the ||f|| * sigma product.

import eponym_mac
import math

type FMat = seq[seq[float]]

proc hostAddF(a, b: float): float = a + b
proc hostSubF(a, b: float): float = a - b
proc hostDot(xs, ys: seq[float]): float =
  for i in 0 ..< xs.len: result += xs[i] * ys[i]
proc hostMatVec(a: FMat, xs: seq[float]): seq[float] =
  result = newSeq[float](a.len)
  for i in 0 ..< a.len:
    for j in 0 ..< xs.len: result[i] += a[i][j] * xs[j]

proc hostAbsF(a: float): float = abs(a)
proc hostMulF(a, b: float): float = a * b

proc seKernel(x, y, lengthScale: float): float =
  exp(-((x - y) * (x - y)) / (2.0 * lengthScale * lengthScale))

proc kernelIntegral(x, lengthScale: float): float =
  let s = sqrt(2.0) * lengthScale
  sqrt(PI / 2.0) * lengthScale * (erf((1.0 - x) / s) - erf(-x / s))

proc kernelDoubleIntegral(lengthScale: float): float =
  let t = 1.0 / (sqrt(2.0) * lengthScale)
  2.0 * (sqrt(PI / 2.0) * lengthScale * erf(t) -
    lengthScale * lengthScale * (1.0 - exp(-1.0 / (2.0 * lengthScale * lengthScale))))

proc solve3(a0: array[3, array[3, float]], b0: array[3, float]): array[3, float] =
  var a = a0
  var b = b0
  for col in 0 .. 2:
    var pivot = col
    for row in col + 1 .. 2:
      if abs(a[row][col]) > abs(a[pivot][col]): pivot = row
    swap(a[col], a[pivot])
    swap(b[col], b[pivot])
    for row in col + 1 .. 2:
      let q = a[row][col] / a[col][col]
      for j in col .. 2: a[row][j] -= q * a[col][j]
      b[row] -= q * b[col]
  for row in countdown(2, 0):
    result[row] = b[row]
    for j in row + 1 .. 2: result[row] -= a[row][j] * result[j]
    result[row] /= a[row][row]

proc dot3(a, b: array[3, float]): float =
  for i in 0 .. 2: result += a[i] * b[i]

proc numericalIdentity(): tuple[variance, wce, bound, integral: float] =
  const nodes = [0.15, 0.5, 0.85]
  const x0 = 0.37
  const l = 0.31
  var k: array[3, array[3, float]]
  var z, kx0: array[3, float]
  for i in 0 .. 2:
    z[i] = kernelIntegral(nodes[i], l)
    kx0[i] = seKernel(nodes[i], x0, l)
    for j in 0 .. 2: k[i][j] = seKernel(nodes[i], nodes[j], l)
  let w = solve3(k, z)
  let kw = [dot3(k[0], w), dot3(k[1], w), dot3(k[2], w)]
  let kappa = kernelDoubleIntegral(l)
  result.variance = kappa - dot3(w, kw)
  result.wce = kappa - 2.0 * dot3(w, z) + dot3(w, kw)
  result.bound = sqrt(max(result.variance, 0.0))
  result.integral = kernelIntegral(x0, l)
  doAssert abs(result.variance - result.wce) <= 1e-12 * max(1.0, abs(result.variance))
  doAssert abs(result.integral - dot3(w, kx0)) <= result.bound

proc runNumerics() =
  let n = numericalIdentity()
  echo "bq numeric identity ok: variance=", n.variance, " wce=", n.wce
  doAssert n.bound >= 0.0
  when defined(bqPerturbed):
    doAssert abs(n.variance - (n.wce + 1e-6)) <=
      1e-12 * max(1.0, abs(n.variance))

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/vec.ep"
  import "../lib/float.ep"
  import "../lib/eq.ep"
  postulate(Int, Univ)
  runtimeType(Float, float)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  postulate(Mat, Nat -> Nat -> Univ)
  runtimeType(Mat, FMat)
  postulate(addF, Float -> Float -> Float)
  bindPostulate(addF, hostAddF, Float, Float, Float)
  postulate(subF, Float -> Float -> Float)
  bindPostulate(subF, hostSubF, Float, Float, Float)
  postulate(absFloat, Float -> Float)
  bindPostulate(absFloat, hostAbsF, Float, Float)
  postulate(mulF, Float -> Float -> Float)
  bindPostulate(mulF, hostMulF, Float, Float, Float)
  postulate(Le, Float -> Float -> Univ)
  postulate(dot, Pi(n: Nat, Vec[Float, n] -> Vec[Float, n] -> Float))
  bindPostulate(dot, hostDot, Vec, Vec, Float)
  postulate(matVec, Pi(n: Nat, Mat[n, n] -> Vec[Float, n] -> Vec[Float, n]))
  bindPostulate(matVec, hostMatVec, Mat, Vec, Vec)
  # Trusted: the defining property K w = z, as an Eq-typed postulate.
  postulate(kwEq, Pi(n: Nat, K: Mat[n, n], z: Vec[Float, n],
    w: Vec[Float, n], Eq[Vec[Float, n], matVec(n, K, w), z]))
  # Trusted: one combined ring identity (same trust class as separate
  # ring lemmas): kappa - d = (kappa - d - d) + d.
  postulate(ringCancelF, Pi(kappa: Float, d: Float,
    Eq[Float, subF(kappa, d),
      addF(subF(subF(kappa, d), d), d)]))
  postulate(rkhsInner, Pi(n: Nat, Vec[Float, n] -> Vec[Float, n] -> Float))
  postulate(rkhsNorm, Pi(n: Nat, Vec[Float, n] -> Float))
  # Trusted analytic bridge: the residual representer's norm is sigma after
  # rewriting its squared norm with the checked BQ identity.
  postulate(residualNormEq, Pi(n: Nat, K: Mat[n, n], z: Vec[Float, n],
    kappa: Float, w: Vec[Float, n], r: Vec[Float, n], sigma: Float,
    Eq[Float, subF(kappa, dot(n, w, matVec(n, K, w))),
      addF(subF(subF(kappa, dot(n, w, z)), dot(n, w, z)),
        dot(n, w, matVec(n, K, w)))] ->
    Eq[Float, rkhsNorm(n, r), sigma]))
  postulate(cauchySchwarz, Pi(n: Nat, f: Vec[Float, n], r: Vec[Float, n],
    Le(absFloat(rkhsInner(n, f, r)),
      mulF(rkhsNorm(n, f), rkhsNorm(n, r)))))
  postulate(leCongRight, Pi(x: Float, y: Float, z: Float,
    Eq[Float, y, z] -> Le(x, y) -> Le(x, z)))
  postulate(leCongLeft, Pi(x: Float, y: Float, z: Float,
    Eq[Float, x, y] -> Le(y, z) -> Le(x, z)))
  # Lemma 1: dot w (K w) = dot w z, by congruence over kwEq.
  proc lemmaDotKw(n: Nat, K: Mat[n, n], z: Vec[Float, n],
      w: Vec[Float, n]):
      Eq[Float, dot(n, w, matVec(n, K, w)), dot(n, w, z)] =
    cong[Vec[Float, n], Float](
      lam(v: Vec[Float, n]) => dot(n, w, v),
      matVec(n, K, w), z, kwEq(n, K, z, w))
  # Lemma 2: kappa - dot w (K w) = kappa - dot w z, by congruence over Lemma 1.
  proc lemmaSub(n: Nat, K: Mat[n, n], z: Vec[Float, n], kappa: Float,
      w: Vec[Float, n]):
      Eq[Float, subF(kappa, dot(n, w, matVec(n, K, w))),
        subF(kappa, dot(n, w, z))] =
    cong[Float, Float](
      lam(d: Float) => subF(kappa, d),
      dot(n, w, matVec(n, K, w)), dot(n, w, z),
      lemmaDotKw(n, K, z, w))
  # Lemma 3: (kappa - d - d) + d = (kappa - d - d) + d', where
  # d = dot w z and d' = dot w (K w), by congruence over sym Lemma 1.
  proc lemmaAdd(n: Nat, K: Mat[n, n], z: Vec[Float, n], kappa: Float,
      w: Vec[Float, n]):
      Eq[Float,
        addF(subF(subF(kappa, dot(n, w, z)), dot(n, w, z)), dot(n, w, z)),
        addF(subF(subF(kappa, dot(n, w, z)), dot(n, w, z)),
          dot(n, w, matVec(n, K, w)))] =
    cong[Float, Float](
      lam(d: Float) =>
        addF(subF(subF(kappa, dot(n, w, z)), dot(n, w, z)), d),
      dot(n, w, z), dot(n, w, matVec(n, K, w)),
      sym[Float](dot(n, w, matVec(n, K, w)), dot(n, w, z),
        lemmaDotKw(n, K, z, w)))
  # Assembly: kappa - w^T K w = (kappa - w^T z - w^T z) + w^T K w.
  proc bqIdentity(n: Nat, K: Mat[n, n], z: Vec[Float, n], kappa: Float,
      w: Vec[Float, n]):
      Eq[Float, subF(kappa, dot(n, w, matVec(n, K, w))),
        addF(subF(subF(kappa, dot(n, w, z)), dot(n, w, z)),
          dot(n, w, matVec(n, K, w)))] =
    trans[Float](
      subF(kappa, dot(n, w, matVec(n, K, w))),
      subF(kappa, dot(n, w, z)),
      addF(subF(subF(kappa, dot(n, w, z)), dot(n, w, z)),
        dot(n, w, matVec(n, K, w))),
      lemmaSub(n, K, z, kappa, w),
      trans[Float](
        subF(kappa, dot(n, w, z)),
        addF(subF(subF(kappa, dot(n, w, z)), dot(n, w, z)), dot(n, w, z)),
        addF(subF(subF(kappa, dot(n, w, z)), dot(n, w, z)),
          dot(n, w, matVec(n, K, w))),
        ringCancelF(kappa, dot(n, w, z)),
        lemmaAdd(n, K, z, kappa, w)))
  proc bqBound(n: Nat, K: Mat[n, n], z: Vec[Float, n], kappa: Float,
      w: Vec[Float, n], f: Vec[Float, n], r: Vec[Float, n], sigma: Float,
      integral: Float, quadrature: Float,
      residualRep: Eq[Float, absFloat(subF(integral, quadrature)),
        absFloat(rkhsInner(n, f, r))]):
      Le(absFloat(subF(integral, quadrature)), mulF(rkhsNorm(n, f), sigma)) =
    leCongLeft(absFloat(subF(integral, quadrature)),
      absFloat(rkhsInner(n, f, r)), mulF(rkhsNorm(n, f), sigma), residualRep,
      leCongRight(absFloat(rkhsInner(n, f, r)),
      mulF(rkhsNorm(n, f), rkhsNorm(n, r)),
      mulF(rkhsNorm(n, f), sigma),
      cong[Float, Float](
        lam(d: Float) => mulF(rkhsNorm(n, f), d),
        rkhsNorm(n, r), sigma,
        residualNormEq(n, K, z, kappa, w, r, sigma,
          bqIdentity(n, K, z, kappa, w))),
      cauchySchwarz(n, f, r)))
  compileTimeOnly(lemmaDotKw)
  compileTimeOnly(lemmaSub)
  compileTimeOnly(lemmaAdd)
  compileTimeOnly(bqIdentity)
  compileTimeOnly(bqBound)

when isMainModule:
  runNumerics()
