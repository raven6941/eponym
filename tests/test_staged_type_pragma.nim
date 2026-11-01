## Issue #499: host staging metadata survives Eponym elaboration.
## Issue #524: the staging pragma is `{.stagedType.}` (renamed from
## `{.runtimeType.}`); the `runtimeType(EponymType, NimType)` mapping form
## keeps its name.
import eponym_mac

eponymBlock:
  import "../lib/nat.ep"
  proc marked: Univ {.stagedType.} = Nat

echo "test_staged_type_pragma: passed"
