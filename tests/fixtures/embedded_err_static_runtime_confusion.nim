## Fixture for tests/test_embedded_error_path.nim (issue #515).
## A `[n: Nat]` static binder used as a runtime value in the body must fail
## with a diagnostic explaining the static/runtime distinction -- `[n: Nat]`
## is a compile-time parameter (Nim `static[int]` at the generated boundary)
## while `(n: Nat)` is an ordinary runtime value -- not the generic
## "no supported Nim runtime representation" message. Compiling this file
## must FAIL with that explanation in the output.
import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  postulate(Int, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  proc getN[n: Nat](x: Nat): Nat = n
