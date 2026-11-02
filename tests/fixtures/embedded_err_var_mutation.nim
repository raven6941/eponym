## Fixture for tests/test_embedded_error_path.nim (issue #513).
## A `var` declaration inside eponymBlock must fail with a diagnostic
## explaining the conceptual mistake -- the block body is translated to an
## Eponym term, and Eponym terms have no mutable variables (every binding is
## single-assignment) -- not the generic "proc body must be lets followed by
## single expr" message. Compiling this file must FAIL with that explanation
## in the output.
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  proc mutatedCounter(): Int =
    var x = 1
    x = x
    x
