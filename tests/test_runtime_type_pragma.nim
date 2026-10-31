## Issue #499: host staging metadata survives Eponym elaboration.
import eponym_mac

eponymBlock:
  import "../lib/nat.ep"
  proc marked: Univ {.runtimeType.} = Nat

echo "test_runtime_type_pragma: passed"
