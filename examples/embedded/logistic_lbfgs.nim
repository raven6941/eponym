## Checked logistic regression with LBFGS over sized vectors (Issue #555).
##
## Checked: the logistic objective is accepted only after the DCP Convex
## certificate is elaborated at compile time; dimensions occur in the
## certified term (`Mat[m, n]`, `VectorData[m]`, `VectorData[n]` indices)
## and in the checked wrapper types at literal m, n.  Trusted: the host
## objective and gradient implement that same `lrTerm`, LBFGS and
## line-search numerics, and the dataset shape check at the boundary.  The
## certified problem and host objective are the same by construction, not
## by passing a term at runtime: the term has no runtime representation.
##
## The weight vector crosses as `VectorData[n]`, NOT as `Vec Float n`:
## the repr tier's collections are int-fragment-only (`checkIntElem` in
## codegen.nim), so `Vec Float n` has no boundary representation — see
## issue #556. `VectorData[n]` still carries the dimension in the checked
## wrapper types; lengths are validated at the boundary by `checkShapes`.
##
## The DCP rules below are the trimmed vector fragment from convex_opt_vec.nim
## (Issue #110).  The checked entry points use literal dimensions because the
## current opaque adapter cannot bind a postulate whose Pi binders are used as
## indices; LBFGS itself remains generic over seq and sized Nim arrays.

import std/[math, times, random, algorithm]
import eponym_mac

type FMat = seq[seq[float]]
type FVec = seq[float]

proc checkShapes(a: FMat, b, w: FVec) =
  if a.len == 0 or b.len != a.len or a[0].len != w.len:
    raise newException(ValueError, "logistic boundary shape mismatch")
  for row in a:
    if row.len != a[0].len:
      raise newException(ValueError, "logistic boundary ragged matrix")

proc hostLogisticLoss*(a: FMat, b, w: FVec): float =
  checkShapes(a, b, w)
  for i, row in a:
    var z = -b[i]
    for j, x in row: z += x * w[j]
    result += (if z > 0: z + ln(1.0 + exp(-z)) else: ln(1.0 + exp(z)))

proc hostLogisticGrad*(a: FMat, b, w: FVec): FVec =
  checkShapes(a, b, w)
  result = newSeq[float](w.len)
  for i, row in a:
    var z = -b[i]
    for j, x in row: z += x * w[j]
    let s = (if z >= 0: 1.0 / (1.0 + exp(-z)) else: exp(z) / (1.0 + exp(z)))
    for j, x in row: result[j] += x * s

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  postulate(Int, Univ)
  postulate(Float, Univ)
  postulate(Mat, Nat -> Nat -> Univ)
  postulate(VectorData, Nat -> Univ)

  data(VExpr, Nat -> Univ):
    proc vVar(n: Nat): VExpr[n]
    proc vData(n: Nat, values: VectorData[n]): VExpr[n]
    proc vMinus(n: Nat, e1: VExpr[n], e2: VExpr[n]): VExpr[n]
    proc vMatVec(m: Nat, n: Nat, A: Mat[m, n], e: VExpr[n]): VExpr[m]
  data(CExpr, Univ):
    proc vLogSum(n: Nat, e: VExpr[n]): CExpr
  data(VAffine, [n: Nat], VExpr[n] -> Univ):
    proc vafVar(): VAffine[n, vVar[n]()]
    proc vafData(values: VectorData[n]): VAffine[n, vData[n](values)]
    proc vafMinus(e1: VExpr[n], e2: VExpr[n], h1: VAffine[n, e1], h2: VAffine[n, e2]):
      VAffine[n, vMinus[n](e1, e2)]
  postulate(vafMatVec, Pi(m: Nat, n: Nat, A: Mat[m, n], e: VExpr[n],
    VAffine[n, e] -> VAffine[m, vMatVec[m, n](A, e)]))
  data(Convex, CExpr -> Univ):
    proc cvLogSum(n: Nat, e: VExpr[n], h: VAffine[n, e]): Convex[vLogSum[n](e)]
  proc lrTerm(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]): CExpr =
    vLogSum[m](vMinus[m](vMatVec[m, n](A, vVar[n]()), vData[m](b)))
  proc lrCert(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]):
      Convex[lrTerm(m, n, A, b)] =
    cvLogSum[m](vMinus[m](vMatVec[m, n](A, vVar[n]()), vData[m](b)),
      vafMinus[m](vMatVec[m, n](A, vVar[n]()), vData[m](b),
        vafMatVec[m, n](A, vVar[n](), vafVar[n]()), vafData[m](b)))
  proc minimize(e: CExpr, h: Convex[e]): CExpr = e
  proc lrProb(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]): CExpr =
    minimize(lrTerm(m, n, A, b), lrCert(m, n, A, b))
  compileTimeOnly(lrTerm)
  compileTimeOnly(lrCert)
  compileTimeOnly(lrProb)
  compileTimeOnly(minimize)

  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeType(Float, float)
  runtimeType(Mat, FMat)
  runtimeType(VectorData, FVec)
  runtimeVector(Vec)

  postulate(logisticLossSmall, Mat[4, 2] -> VectorData[4] -> VectorData[2] -> Float)
  postulate(logisticGradSmall, Mat[4, 2] -> VectorData[4] -> VectorData[2] -> VectorData[2])
  postulate(logisticLossLarge, Mat[500, 50] -> VectorData[500] -> VectorData[50] -> Float)
  postulate(logisticGradLarge, Mat[500, 50] -> VectorData[500] -> VectorData[50] -> VectorData[50])
  bindPostulate(logisticLossSmall, hostLogisticLoss, Mat, VectorData, VectorData, Float)
  bindPostulate(logisticGradSmall, hostLogisticGrad, Mat, VectorData, VectorData, VectorData)
  bindPostulate(logisticLossLarge, hostLogisticLoss, Mat, VectorData, VectorData, Float)
  bindPostulate(logisticGradLarge, hostLogisticGrad, Mat, VectorData, VectorData, VectorData)

  proc logisticLossAtSmall(a: Mat[4, 2], b: VectorData[4], w: VectorData[2]): Float =
    logisticLossSmall(a, b, w)
  proc logisticGradAtSmall(a: Mat[4, 2], b: VectorData[4], w: VectorData[2]): VectorData[2] =
    logisticGradSmall(a, b, w)
  proc logisticLossAtLarge(a: Mat[500, 50], b: VectorData[500], w: VectorData[50]): Float =
    logisticLossLarge(a, b, w)
  proc logisticGradAtLarge(a: Mat[500, 50], b: VectorData[500], w: VectorData[50]): VectorData[50] =
    logisticGradLarge(a, b, w)

type LbfgsResult*[V] = object
  weights*: V
  iterations*: int
  loss*: float
  gradNorm*: float

proc dot[V](a, b: V): float =
  for i in 0 ..< a.len: result += a[i] * b[i]
proc norm[V](a: V): float = sqrt(dot(a, a))
proc axpy[V](a: var V, scale: float, b: V) =
  for i in 0 ..< a.len: a[i] += scale * b[i]
proc copyVector[V](a: V): V =
  when V is seq[float]: result = newSeq[float](a.len)
  else: result = a
  for i in 0 ..< a.len: result[i] = a[i]
proc difference[V](a, b: V): V =
  result = copyVector(a)
  for i in 0 ..< a.len: result[i] = a[i] - b[i]

proc lbfgs*[V](initial: V, loss: proc(x: V): float {.closure.},
    gradient: proc(x: V): V {.closure.}): LbfgsResult[V] =
  var x = initial
  var pairs: seq[tuple[s, y: V, rho: float]] = @[]
  var g = gradient(x)
  var f = loss(x)
  for iteration in 0 ..< 1000:
    let gn = norm(g)
    if gn < 1e-8:
      return LbfgsResult[V](weights: x, iterations: iteration, loss: f, gradNorm: gn)
    var q = copyVector(g)
    var alpha: seq[float] = @[]
    for k in countdown(pairs.high, 0):
      let a = pairs[k].rho * dot(pairs[k].s, q)
      alpha.add(a)
      axpy(q, -a, pairs[k].y)
    var gamma = 1.0
    if pairs.len > 0:
      let last = pairs[^1]
      gamma = dot(last.s, last.y) / dot(last.y, last.y)
    for i in 0 ..< q.len: q[i] *= gamma
    for k in 0 ..< pairs.len:
      let a = alpha[pairs.len - 1 - k]
      # Nocedal & Wright Alg. 7.5: r += s_k * (alpha_k - beta_k),
      # beta_k = rho_k * y_k^T r. (The opposite sign does not implement
      # the two-loop recursion: it stalls near the optimum.)
      axpy(q, a - pairs[k].rho * dot(pairs[k].y, q), pairs[k].s)
    var direction = copyVector(q)
    for i in 0 ..< direction.len: direction[i] = -direction[i]
    var slope = dot(g, direction)
    if slope >= 0:
      pairs.setLen(0)
      direction = copyVector(g)
      for i in 0 ..< direction.len: direction[i] = -direction[i]
      slope = dot(g, direction)
    var step = 1.0
    var next = copyVector(x)
    # Armijo alone cannot certify a step once the expected decrease falls
    # below the loss's own float64 rounding noise (here f ~ 320, a
    # 500-term sum, so the computed loss wobbles by ~1e-13 while a Newton
    # step near the optimum decreases the true loss by ~1e-15). Without
    # a tolerance the line search halves until the step stops moving x
    # at all and the optimizer stalls with |grad| ~ 4e-7 for the remaining
    # 950 iterations. The tolerance below is a few dozen ulps of f: it
    # never binds while the decrease is resolvable, and in the polishing
    # regime it lets the (gradient-certified) Newton step through. The
    # gradient norm remains the stopping signal.
    let lossTol = 32.0 * 2.220446049250313e-16 * max(1.0, abs(f)) # 32 ulps of f
    while step > 1e-20:
      next = copyVector(x)
      axpy(next, step, direction)
      if loss(next) <= f + 1e-4 * step * slope + lossTol: break
      step *= 0.5
    let nextG = gradient(next)
    let s = difference(next, x)
    let y = difference(nextG, g)
    let sy = dot(s, y)
    if sy > 1e-14:
      pairs.add((s, y, 1.0 / sy))
      if pairs.len > 10: pairs.delete(0)
    x = next
    g = nextG
    f = loss(x)
  LbfgsResult[V](weights: x, iterations: 1000, loss: f, gradNorm: norm(g))

proc zeroLike[V](x: V): V =
  result = copyVector(x)
  for i in 0 ..< result.len: result[i] = 0.0

let smallA*: FMat = @[@[1.0, 0.0], @[-1.0, 0.0], @[0.0, 1.0], @[0.0, -1.0]]
let smallB*: FVec = @[1.0, 0.0, 0.5, -0.5]

proc runCheckedSmall*(): LbfgsResult[FVec] =
  let z = @[0.0, 0.0]
  lbfgs(z, proc(x: FVec): float = logisticLossAtSmall(smallA, smallB, x),
    proc(x: FVec): FVec = logisticGradAtSmall(smallA, smallB, x))
proc runPlainSmall*(): LbfgsResult[FVec] =
  let z = @[0.0, 0.0]
  lbfgs(z, proc(x: FVec): float = hostLogisticLoss(smallA, smallB, x),
    proc(x: FVec): FVec = hostLogisticGrad(smallA, smallB, x))
proc runArraySmall*(): LbfgsResult[array[2, float]] =
  let z = [0.0, 0.0]
  lbfgs(z, proc(x: array[2, float]): float = hostLogisticLoss(smallA, smallB, @[x[0], x[1]]),
    proc(x: array[2, float]): array[2, float] =
      let g = hostLogisticGrad(smallA, smallB, @[x[0], x[1]])
      [g[0], g[1]])

proc makeLarge*(): tuple[a: FMat, b: FVec] =
  var rng = initRand(555)
  var truth = newSeq[float](50)
  for j in 0 ..< 50: truth[j] = gauss(rng)
  result.a = newSeq[FVec](500)
  result.b = newSeq[float](500)
  for i in 0 ..< 500:
    result.a[i] = newSeq[float](50)
    for j in 0 ..< 50: result.a[i][j] = gauss(rng)
    for j in 0 ..< 50: result.b[i] += result.a[i][j] * truth[j]
    result.b[i] += 0.1 * gauss(rng)

proc runCheckedLarge*(a: FMat, b: FVec): LbfgsResult[FVec] =
  let z = newSeq[float](50)
  lbfgs(z, proc(x: FVec): float = logisticLossAtLarge(a, b, x),
    proc(x: FVec): FVec = logisticGradAtLarge(a, b, x))
proc runPlainLarge*(a: FMat, b: FVec): LbfgsResult[FVec] =
  let z = newSeq[float](50)
  lbfgs(z, proc(x: FVec): float = hostLogisticLoss(a, b, x),
    proc(x: FVec): FVec = hostLogisticGrad(a, b, x))

proc median(xs: seq[float]): float =
  var ys = xs
  ys.sort()
  ys[ys.len div 2]

proc main*() =
  let optimum = @[0.5, 0.5]
  let large = makeLarge()
  for problem in ["small", "large"]:
    for checked in [true, false]:
      var timesRun: seq[float] = @[]
      var r: LbfgsResult[FVec]
      for run in 0 ..< 5:
        let t = cpuTime()
        if problem == "small": r = if checked: runCheckedSmall() else: runPlainSmall()
        else: r = if checked: runCheckedLarge(large.a, large.b) else: runPlainLarge(large.a, large.b)
        timesRun.add(cpuTime() - t)
      let distance = if problem == "small": sqrt((r.weights[0] - optimum[0]) ^ 2 + (r.weights[1] - optimum[1]) ^ 2) else: 0.0
      echo "path=", (if checked: "checked" else: "plain"), " problem=", problem,
        " iterations=", r.iterations, " final_loss=", r.loss,
        " final_grad=", r.gradNorm, " distance=", distance,
        " wall_seconds_median=", median(timesRun), " times=", timesRun
      doAssert r.gradNorm < 1e-8
      if problem == "small": doAssert distance < 1e-6

when isMainModule:
  main()
