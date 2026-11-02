## Fixture for tests/test_embedded_error_path.nim (issue #516).
## The definition checks, but its erased function argument has no Nim runtime
## representation, so strict eponymBlock codegen must explain the boundary.
import eponym_mac

eponymBlock:
  postulate(Int, Univ)
  postulate(Nat, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  proc applyQ0(f: Pi(p {.erased.}: Nat, Int), x: Int): Int = f 0
