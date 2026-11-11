## End-to-end wrapper test for the Phase 2 representation backend
## (Issue #330 v3: `Vec` as `seq[int]`).
##
## A separate file from `test_codegen_phase2_vec.nim`: both elaborate a
## `vecElim`, and each elaboration emits `eponymElim_vecElim`, so they cannot
## share a module. This file checks the typed wrapper path (`eponymBlock`):
## a `Vec`-typed wrapper must reroute through the repr proc
## (`eponymCompiledRepr_wVMapDouble`) via the identity boundary, and must
## preserve the entry length check.
##
## Call-form lambdas are used: the command-form `lam (v : Vec Int i). ...`
## does not survive blockToEponym's command-lambda converter (the established
## `lam(binder: type) => body` call form comes from test_embedded_macro_forms).
## `vecnil` is the eponymBlock spelling of the `nil` constructor (`nil` is a
## Nim keyword); explicit type/index args use square brackets.

import std/sequtils
import eponym_mac

proc hostFloatZero(_: int): float = 0.0
proc hostFloatAdd(a, b: float): float = a + b
proc hostSumVec(xs: seq[float]): float =
  for x in xs: result += x
type FMat = seq[seq[float]]
type FVec = seq[float]
proc hostGenericLoss(a: FMat, b, w: seq[float]): float =
  for row in a:
    for x in row: result += x
  for x in b: result += x
  for x in w: result += x
proc hostGenericGrad(a: FMat, b, w: seq[float]): seq[float] =
  result = newSeq[float](w.len)
  for i in 0 ..< result.len: result[i] = b[i] + w[i] + a[0][i]

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/vec.ep"
  import "../lib/float.ep"
  postulate(Int, Univ)
  runtimeType(Float, float)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  proc wVMapDouble(n: Nat, xs: Vec[Int, n]): Vec[Int, n] = vecElim[Int](lam(i: Nat) => lam(v: Vec[Int, i]) => Vec[Int, i], vecnil[Int](), lam(i: Nat) => lam(x: Int) => lam(xs2: Vec[Int, i]) => lam(ih: Vec[Int, i]) => cons[Int, i](addInt(x, x), ih), n, xs)
  postulate(floatZero, Int -> Float)
  bindPostulate(floatZero, hostFloatZero, Int, Float)
  postulate(floatAdd, Float -> Float -> Float)
  bindPostulate(floatAdd, hostFloatAdd, Float, Float, Float)
  postulate(sumVec, Pi(n: Nat, Vec[Float, n] -> Float))
  bindPostulate(sumVec, hostSumVec, Vec, Float)
  proc wGenericSum(n: Nat, xs: Vec[Float, n]): Float = sumVec(n, xs)
  postulate(Mat, Nat -> Nat -> Univ)
  postulate(VectorData, Nat -> Univ)
  runtimeType(Mat, FMat)
  runtimeType(VectorData, FVec)
  postulate(genericLoss, Pi(m: Nat, n: Nat, Mat[m, n] -> VectorData[m] ->
    Vec[Float, n] -> Float))
  postulate(genericGrad, Pi(m: Nat, n: Nat, Mat[m, n] -> VectorData[m] ->
    Vec[Float, n] -> Vec[Float, n]))
  bindPostulate(genericLoss, hostGenericLoss, Mat, VectorData, Vec, Float)
  bindPostulate(genericGrad, hostGenericGrad, Mat, VectorData, Vec, Vec)
  proc wGenericLoss(m, n: Nat, a: Mat[m, n], b: VectorData[m],
      w: Vec[Float, n]): Float = genericLoss(m, n, a, b, w)
  proc wGenericGrad(m, n: Nat, a: Mat[m, n], b: VectorData[m],
      w: Vec[Float, n]): Vec[Float, n] = genericGrad(m, n, a, b, w)
  proc wVSum(n: Nat, xs: Vec[Float, n]): Float =
    vecElim[Float](lam(i: Nat) => lam(v: Vec[Float, i]) => Float,
      floatZero(0),
      lam(i: Nat) => lam(x: Float) => lam(xs2: Vec[Float, i]) =>
        lam(ih: Float) => floatAdd(x, ih), n, xs)
  proc wVSum3(xs: Vec[Float, 3]): Float =
    vecElim[Float](lam(i: Nat) => lam(v: Vec[Float, i]) => Float,
      floatZero(0),
      lam(i: Nat) => lam(x: Float) => lam(xs2: Vec[Float, i]) =>
        lam(ih: Float) => floatAdd(x, ih), 3, xs)

proc expect(ok: bool, message: string) =
  if not ok:
    quit("FAIL: " & message, 1)
  echo "ok: ", message

when isMainModule:
  for xs in [@[], @[5], @[1, 2, 3, 4]]:
    expect(wVMapDouble(xs.len, xs) == xs.mapIt(it * 2),
      "e2e wrapper wVMapDouble on " & $xs)
  var raised = false
  try:
    discard wVMapDouble(2, @[1, 2, 3])
  except ValueError:
    raised = true
  expect(raised, "e2e wrapper preserves the Vec entry check")
  expect(abs(wVSum(2, @[1.25, 2.75]) - 4.0) < 1e-12,
    "e2e wrapper crosses Vec Float as seq[float] and computes a sum")
  expect(abs(wVSum3([1.25, 2.75, 0.0]) - 4.0) < 1e-12,
    "e2e wrapper crosses literal Vec Float as array[3, float] and computes a sum")
  doAssert not compiles(wVSum3([1.25, 2.75]))
  raised = false
  try:
    discard wVSum(3, @[1.25, 2.75])
  except ValueError:
    raised = true
  expect(raised, "e2e wrapper preserves the Float Vec entry check")
  expect(abs(wGenericSum(2, @[1.25, 2.75]) - 4.0) < 1e-12,
    "generic postulate sumVec works at length 2")
  expect(abs(wGenericSum(1, @[4.5]) - 4.5) < 1e-12,
    "generic postulate sumVec works at length 1")
  raised = false
  try:
    discard wGenericSum(3, @[1.25, 2.75])
  except ValueError:
    raised = true
  expect(raised, "generic postulate sumVec preserves the Vec entry check")
  let mat2 = @[@[1.0, 2.0], @[3.0, 4.0]]
  let b2 = @[5.0, 6.0]
  let w2 = @[7.0, 8.0]
  expect(abs(wGenericLoss(2, 2, mat2, b2, w2) - 36.0) < 1e-12,
    "generic multi-argument loss works at 2x2")
  expect(wGenericGrad(2, 2, mat2, b2, w2) == @[13.0, 16.0],
    "generic multi-argument gradient works at 2x2")
  let mat1 = @[@[2.0]]
  expect(abs(wGenericLoss(1, 1, mat1, @[3.0], @[4.0]) - 9.0) < 1e-12,
    "generic multi-argument loss works at 1x1")
  expect(wGenericGrad(1, 1, mat1, @[3.0], @[4.0]) == @[9.0],
    "generic multi-argument gradient works at 1x1")
  echo "all Phase 2 Vec end-to-end wrapper checks passed"
