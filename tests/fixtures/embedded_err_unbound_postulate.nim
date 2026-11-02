## Fixture for tests/test_embedded_error_path.nim (issue #518).
## A postulate declared but never host-bound must fail with a diagnostic
## explaining the actual conceptual mistake -- the Eponym signature is only
## half of the contract; a host procedure must be supplied via
## bindPostulate (or bindPostulateValue / bindPostulateMutable) before any
## definition using the postulate can be used at runtime -- not the generic
## "Phase 2 unavailable" representation-machinery message.
## Compiling this file must FAIL with that explanation in the output.
import eponym_mac

eponymBlock:
  postulate(Int, Univ)
  runtimeType(Int, int)
  postulate(hostOp, Int -> Int)
  proc f(x: Int): Int = hostOp(x)
