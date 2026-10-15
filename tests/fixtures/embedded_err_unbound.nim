## Fixture for tests/test_embedded_error_path.nim (issue #199).
## Ill-typed eponymBlock (unbound variable in the body). Compiling this file
## must FAIL with a clean "eponymBlock elaboration error" -- never a
## compiler SIGSEGV (Nim VM bare-`raise` re-raise bug).
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  proc bad(x: Int): Int = y
