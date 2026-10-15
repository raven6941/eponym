## Fixture for tests/test_embedded_error_path.nim (issue #199).
## Ill-typed eponymBlock (body type does not match the ascribed type).
## Compiling this file must FAIL with a clean "eponymBlock elaboration
## error" -- never a compiler SIGSEGV.
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  postulate(Nat, Univ)
  proc bad(x: Int): Nat = x
