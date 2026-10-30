## The checked borrow clients have no interpreter-backed runtime wrappers.
import ../examples/embedded/qtt_borrow as borrow

static:
  doAssert not compiles(borrow.borrowClient(1))
  doAssert not compiles(borrow.failingBorrowClient(1))

when isMainModule:
  echo "test_borrow_runtime: callback clients are compile-time-only"
