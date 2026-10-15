## Fixture for tests/test_embedded_error_path.nim (issue #74).
## A literal that does not inhabit the expected singleton type:
## `exactly2` demands the literal 2, but gets 3.
## Compiling this file must FAIL with a clean "eponymBlock elaboration
## error" -- never a compiler SIGSEGV.
import eponym_mac
import eponym_embed

eponymBlock:
  import "../../lib/nat.ep"
  proc exactly2(d: 2): Nat = d
  proc bad(): Nat = exactly2(3)
