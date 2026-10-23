## Fixture for tests/test_embedded_error_path.nim (issue #409).
## A `bindPostulateValue`-bound postulate applied at a non-static type must
## fail with a NAMED macro-time error ("applied at a non-static type"), not
## a silent Value-tier fallback. Compiling this file must FAIL with that
## marker in the output.
import eponym_mac
import eponym_embed

proc fixtureEcho(args: seq[RuntimeValue],
                globals: RuntimeGlobals): RuntimeValue =
  args[1]

eponymBlock:
  postulate(Int, Univ)
  import "../../lib/debug.ep"
  bindPostulateValue(debugEcho, fixtureEcho)
  proc genericEcho[A: Univ](x: A): A = debugEcho[A](x)
