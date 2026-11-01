## Strict eponymBlock keeps the DCP proof but emits no Value-backed runtime API.
import ../examples/embedded/convex_opt as convex

static:
  doAssert not compiles(convex.prob())
  doAssert not compiles(convex.shiftedProb())

when isMainModule:
  echo "test_convex_opt_runtime: certified objectives are compile-time-only"
