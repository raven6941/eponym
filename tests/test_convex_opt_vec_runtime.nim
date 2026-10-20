## Differentially check the interpreter against the intended logistic model.
import std/math
import falsify
import ../examples/embedded/convex_opt_vec as convex

static:
  doAssert compiles(convex.lrProbRuntimeValue(1, 1, @[@[1.0]], @[0.0]))
  doAssert not compiles(convex.lrProbRuntimeValue(1, 1, "not a matrix", @[0.0]))

proc referenceLoss(A: convex.FMat, b, weights: convex.FVec): float =
  for i in 0 ..< A.len:
    var affine = -b[i]
    for j in 0 ..< weights.len: affine += A[i][j] * weights[j]
    result += ln(1.0 + exp(affine))

proc referenceGradient(A: convex.FMat, b,
                       weights: convex.FVec): convex.FVec =
  result = newSeq[float](weights.len)
  for i in 0 ..< A.len:
    var affine = -b[i]
    for j in 0 ..< weights.len: affine += A[i][j] * weights[j]
    let sigmoid = 1.0 / (1.0 + exp(-affine))
    for j in 0 ..< weights.len: result[j] += A[i][j] * sigmoid

when isMainModule:
  var rng = initRng(771923'u64)
  let cases = forAll(
    "checked logistic expression drives objective and finite-difference gradient",
    rng, 200,
    proc(r: var Rng): int = r.genInt(-10000, 10000),
    proc(seed: int): bool =
      let a = float((seed mod 19) - 9) / 10.0
      let c = float(((seed div 3) mod 17) - 8) / 10.0
      let A: convex.FMat = @[@[a, c], @[-c, a + 0.3], @[c - 0.2, -a]]
      let b: convex.FVec = @[
        float(seed mod 13) / 10.0,
        float((seed div 5) mod 11) / 10.0,
        float((seed div 7) mod 9) / 10.0]
      let weights: convex.FVec = @[
        float((seed mod 23) - 11) / 10.0,
        float(((seed div 2) mod 21) - 10) / 10.0]
      let expected = referenceLoss(A, b, weights)
      let actual = convex.evalCheckedLogistic(A, b, weights)
      let shifted = convex.evalCheckedShiftedLogistic(A, b, weights)
      let expectedGradient = referenceGradient(A, b, weights)
      let actualGradient = convex.evalCheckedGradient(A, b, weights)
      abs(actual - expected) < 1.0e-10 and
        abs(shifted - expected - 5.0) < 1.0e-10 and
        abs(actualGradient[0] - expectedGradient[0]) < 1.0e-7 and
        abs(actualGradient[1] - expectedGradient[1]) < 1.0e-7,
    shrinkInt)
  if not cases:
    quit(1)
  echo "test_convex_opt_vec_runtime: checked objective and gradient verified"
