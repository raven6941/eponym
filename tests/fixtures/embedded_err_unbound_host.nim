## Fixture for tests/test_embedded_error_path.nim (issue #511).
## A bare Nim identifier inside eponymBlock must explain the phase boundary.
import eponym_mac
import eponym_embed

proc hostDouble(x: int): int = x * 2

eponymBlock:
  postulate(Int, Univ)
  proc bad(x: Int): Int = hostDouble(x)
