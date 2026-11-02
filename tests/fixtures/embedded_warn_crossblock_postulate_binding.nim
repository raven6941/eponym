## Fixture for tests/test_embedded_error_path.nim (issue #522).
## Two eponymBlocks import the same .ep file and bind the same imported
## postulate to different host procedures. Postulate bindings are
## per-block, so the second block must not reuse the first block's
## compiled forwarder: it emits its own (`eponymCompiledRepr_op_2`) and its
## own representation-tier copy of `applyOp`, and the compiler warns,
## explaining the reuse restriction instead of failing with a Nim-level
## redefinition error.
import eponym_mac

proc hostAdd(x, y: int): int = x + y
proc hostMul(x, y: int): int = x * y

eponymBlock:
  requireCompiled()
  import "crossblock_postulate_fixture.ep"
  runtimeType(Int, int)
  bindPostulate(op, hostAdd, Int, Int, Int)
  proc useA(x: Int): Int = applyOp x 1

eponymBlock:
  requireCompiled()
  import "crossblock_postulate_fixture.ep"
  runtimeType(Int, int)
  bindPostulate(op, hostMul, Int, Int, Int)
  proc useB(x: Int): Int = applyOp x 2

when isMainModule:
  doAssert useA(10) == 11
  doAssert useB(10) == 20
  echo "embedded_warn_crossblock_postulate_binding: per-block bindings ok"
