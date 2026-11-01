## Fixture for tests/test_embedded_error_path.nim (issue #519).
## A host-bound postulate applied inside an erased (quantity-0) argument
## must still compile, but the compiler must warn loudly: the argument is
## erased at compile time, so the host call never runs.
import eponym_mac

proc nimTrace(x: int): int = x

eponymBlock:
  postulate(Int, Univ)
  runtimeType(Int, int)
  postulate(traceIt, Int -> Int)
  bindPostulate(traceIt, nimTrace, Int, Int)
  compileTimeOnly(useErased)
  compileTimeOnly(main)
  proc useErased(p {.erased.}: Int, x: Int): Int = x
  proc main(x: Int): Int = useErased((traceIt x), x)
