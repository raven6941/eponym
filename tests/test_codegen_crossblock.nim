## Issue #408: cross-block direct calls via a compile-time export registry.
##
## Two `requireCompiled()` eponymBlock invocations in one Nim module import
## the same `.ep` fixture. Without the registry each block re-emits the
## deterministically-named `eponymCompiledRepr_double` proc and the module
## fails with a redefinition error; with it, block B reuses block A's
## already-emitted procs through direct calls.
##
## NOTE: block order matters — exports flow in macro-expansion (source)
## order, so the exporting block must come first in the file.

import eponym_mac

eponymBlock:
  requireCompiled()
  import "fixtures/crossblock_fixture.ep"
  runtimeType(Int, int)
  proc useA(x: Int): Int = double(x)

eponymBlock:
  requireCompiled()
  import "fixtures/crossblock_fixture.ep"
  runtimeType(Int, int)
  proc quad(x: Int): Int = double(double(x))

when isMainModule:
  doAssert useA(21) == 42
  doAssert quad(21) == 84
  echo "test_codegen_crossblock: cross-block direct calls passed"
