## Fixture for tests/test_embedded_error_path.nim (issue #512).
## A string literal inside eponymBlock must fail with a diagnostic explaining
## the conceptual mistake -- Eponym has no string literal syntax; `String`
## (lib/text.ep) is an opaque host type whose values are constructed in Nim
## and cross the boundary through the runtime mapping -- not the generic
## "unsupported Nim expression shape" message. Compiling this file must FAIL
## with that explanation in the output.
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  proc unsupportedString(): Int = "host string"
