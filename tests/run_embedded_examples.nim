## Compiles and runs every embedded demo (Issue #149).
##
## The embedded examples are Nim programs whose Eponym code is elaborated at
## compile time by the `eponymBlock` macro, so compiling *is* the typecheck:
## a broken Eponym definition is a compile error. Running the binary then
## exercises the backend demos and their runtime asserts. A failure of
## either step fails this test.
##
## Run from the repo root (like tests/run_examples.nim):
##   nim c -r --hints:off --path:src --path:src/eponym \
##       --path:src/relational --path:src/staging tests/run_embedded_examples.nim
import os
import osproc
import sequtils

const pathFlags =
  "--path:src --path:src/eponym --path:src/relational --path:src/staging"

let tmpDir = getTempDir() / "eponym-embedded-tests"
createDir(tmpDir)

proc compileAndRun(path: string): bool =
  let name = path.splitFile().name
  let bin = tmpDir / name
  let (cOut, cCode) = execCmdEx("nim c --hints:off " & pathFlags &
    " --out:" & quoteShell(bin) & " " & quoteShell(path))
  if cCode != 0:
    echo "FAIL (compile): ", path
    echo cOut
    return false
  let (rOut, rCode) = execCmdEx(quoteShell(bin))
  if rCode != 0:
    echo "FAIL (run): ", path, " — exit code ", rCode
    echo rOut
    return false
  echo "ok: ", path
  return true

var files = toSeq(walkPattern("examples/embedded/*.nim"))
if files.len == 0:
  echo "FAIL: no examples/embedded/*.nim found — run from the repo root"
  quit(1)

var failed = 0
for path in files:
  if not compileAndRun(path):
    inc failed

if failed > 0:
  echo failed, " embedded example(s) failed"
  quit(1)
echo "--- all ", files.len, " embedded examples compiled and ran ---"
