## Fixture for tests/test_embedded_error_path.nim (issue #574).
## The checked logistic AST is not a runtime value: the shared fragment
## from examples/embedded/logistic_lbfgs.nim (indexed VExpr/CExpr data)
## has no runtime representation, so strict codegen must reject a callable
## wrapper over it. This is the #574 spike's blocker reproducer: executing
## the checked objective needs a runtime representation (or staged
## compilation) for indexed data families. If this fixture ever compiles,
## the route is open and #574 should be revisited.
import eponym_mac

type FMat = seq[seq[float]]
type FVec = seq[float]

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

  proc lrTerm(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]): CExpr =
    vLogSum[m](vMinus[m](vMatVec[m, n](A, vVar[n]()), vData[m](b)))
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeType(Float, float)
  runtimeType(Mat, FMat)
  runtimeType(VectorData, FVec)
  runtimeVector(Vec)
  requireCompiled()

  # This is the concrete route under test: call the same checked definition
  # from a runtime wrapper. Strict codegen must reject it because CExpr/VExpr
  # are indexed data families with no runtime representation/codec.
  proc executeChecked(m, n: Nat, a: Mat[m, n], b: VectorData[m]): CExpr =
    lrTerm(m, n, a, b)

when isMainModule:
  # This line is unreachable: compiling the block is the reproducer.
  echo "unreachable: checked AST has no strict runtime representation"
