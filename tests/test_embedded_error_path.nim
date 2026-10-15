## Error-path test for embedded elaboration (issue #199).
##
## An elaboration error inside `eponymBlock` must produce a clean compile
## error, not segfault the compiler. The bug: `elabDeclsDirInner` used a
## bare `raise` to re-raise ElabError, which segfaults the Nim VM
## (exit 139, SIGSEGV) instead of propagating the exception. The fix is
## the explicit `raise e`.
##
## Each fixture is compiled with `nim c` and must fail with exit code 1
## and "eponymBlock elaboration error" in the output. A compiler crash
## (signal exit, SIGSEGV in output) fails the test explicitly.
##
## Run from the repo root (like tests/run_embedded_examples.nim):
##   nim c -r --hints:off --path:src --path:src/eponym \
##       tests/test_embedded_error_path.nim
import os
import osproc
import strutils

const pathFlags = "--path:src --path:src/eponym"

let tmpDir = getTempDir() / "eponym-errpath-tests"
createDir(tmpDir)

proc checkFixture(path: string): bool =
  let name = path.splitFile().name
  let bin = tmpDir / name
  let (cOut, cCode) = execCmdEx("nim c --hints:off " & pathFlags &
    " --out:" & quoteShell(bin) & " " & quoteShell(path))
  if "SIGSEGV" in cOut or "Segmentation fault" in cOut:
    echo "FAIL (compiler crashed): ", path
    echo cOut
    return false
  if cCode == 0:
    echo "FAIL (compiled cleanly, expected a type error): ", path
    return false
  if cCode != 1:
    echo "FAIL (expected exit 1, got ", cCode, "): ", path
    echo cOut
    return false
  if "eponymBlock elaboration error" notin cOut:
    echo "FAIL (missing clean error message): ", path
    echo cOut
    return false
  echo "ok (clean compile error): ", path
  return true

var failed = 0
for path in ["tests/fixtures/embedded_err_unbound.nim",
             "tests/fixtures/embedded_err_mismatch.nim",
             "tests/fixtures/embedded_err_singleton_mismatch.nim"]:
  if not checkFixture(path):
    inc failed

if failed > 0:
  echo failed, " error-path fixture(s) misbehaved"
  quit(1)
echo "--- embedded error paths are clean ---"
