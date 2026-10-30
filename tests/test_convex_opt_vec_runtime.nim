## Strict eponymBlock keeps indexed DCP proofs without Value-backed APIs.
import ../examples/embedded/convex_opt_vec as convex

static:
  doAssert not compiles(convex.lrProb(1, 1, @[@[1.0]], @[0.0]))
  doAssert not compiles(convex.shiftedLrProb(1, 1, @[@[1.0]], @[0.0]))
  doAssert not compiles(convex.twoVarProb(1, 1, 1, @[@[1.0]]))
  doAssert not compiles(convex.qfProb())

when isMainModule:
  echo "test_convex_opt_vec_runtime: certified objectives are compile-time-only"
