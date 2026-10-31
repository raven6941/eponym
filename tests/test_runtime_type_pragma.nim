## Issue #499: host staging metadata survives Eponym elaboration.
import eponym_mac

eponymBlock:
  postulate(Int, Univ)
  runtimeType(Int, int)
  proc marked(n: Int): Int {.runtimeType.} = n

doAssert marked(7) == 7
echo "test_runtime_type_pragma: passed"
