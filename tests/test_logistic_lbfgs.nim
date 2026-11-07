## Tests for the checked logistic regression program (issue #555).
import std/math
import ../examples/embedded/logistic_lbfgs as logistic

static:
  # Positive control for the negative below: the same call with a
  # 2-vector DOES compile, so the failure is the size, not the shape.
  doAssert compiles(
    logistic.lbfgs([0.0, 0.0],
      proc(x: array[2, float]): float =
        logistic.hostLogisticLoss(logistic.smallA, logistic.smallB, @[x[0], x[1]]),
      proc(x: array[2, float]): array[2, float] =
        let g = logistic.hostLogisticGrad(logistic.smallA, logistic.smallB, @[x[0], x[1]])
        [g[0], g[1]]))
  # A wrong-size call does not compile: the initial point is a 3-vector
  # while the closures are over array[2, float]. The Nim-side size check
  # is the array instantiation; the Eponym-side dimension check lives
  # inside the block (cf. the 18a/18b negatives), and the boundary
  # wrappers take seqs and check lengths at runtime (checkShapes).
  doAssert not compiles(
    logistic.lbfgs([0.0, 0.0, 0.0],
      proc(x: array[2, float]): float =
        logistic.hostLogisticLoss(logistic.smallA, logistic.smallB, @[x[0], x[1]]),
      proc(x: array[2, float]): array[2, float] =
        let g = logistic.hostLogisticGrad(logistic.smallA, logistic.smallB, @[x[0], x[1]])
        [g[0], g[1]]))

when isMainModule:
  let checked = logistic.runCheckedSmall()
  let plain = logistic.runPlainSmall()
  let arr = logistic.runArraySmall()
  # Both paths converge to the analytic optimum w* = (0.5, 0.5).
  for r in [checked, plain]:
    doAssert r.gradNorm < 1e-8
    doAssert abs(r.weights[0] - 0.5) < 1e-6
    doAssert abs(r.weights[1] - 0.5) < 1e-6
  doAssert abs(checked.loss - plain.loss) < 1e-9
  # The sized-array LBFGS agrees with the seq[float] path.
  doAssert abs(arr.weights[0] - checked.weights[0]) < 1e-9
  doAssert abs(arr.weights[1] - checked.weights[1]) < 1e-9
  doAssert abs(arr.loss - checked.loss) < 1e-9
  echo "test_logistic_lbfgs: small checked/plain/array agree at w* = (0.5, 0.5)"
