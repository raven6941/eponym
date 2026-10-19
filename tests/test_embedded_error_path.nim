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

const pathFlags = "--path:src --path:src/eponym --nimcache:/tmp/eponym-errpath-nimcache"

let tmpDir = getTempDir() / "eponym-errpath-tests"
createDir(tmpDir)

proc checkFixture(path: string,
                  expected = "eponymBlock elaboration error"): bool =
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
  if expected notin cOut:
    echo "FAIL (missing expected error marker '", expected, "'): ", path
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

for (path, expected) in [
    ("tests/fixtures/embedded_err_binding_eponym_type.nim",
     "eponymBlock binding error"),
    ("tests/fixtures/embedded_err_binding_nim_type.nim", "type mismatch"),
    ("tests/fixtures/embedded_err_binding_opaque_nim_type.nim",
     "type mismatch"),
    ("tests/fixtures/embedded_err_unsupported_runtime_type.nim",
     "no runtime codec for Eponym result type 'Thing'"),
    ("tests/fixtures/embedded_err_dependent_sigma_runtime.nim",
     "no runtime codec for Eponym result type 'Sig(n: Nat, Vec[Nat, n])'"),
    ("tests/fixtures/embedded_err_dependent_record_runtime.nim",
     "no runtime codec for Eponym result type 'Point'"),
    ("tests/fixtures/embedded_err_bool_without_prelude.nim",
     "Bool constructor 'true' is not declared; import bool.ep"),
    ("tests/fixtures/embedded_err_generic_runtime_index.nim",
     "values with an explicit runtimeType mapping"),
    ("tests/fixtures/embedded_err_binding_quinary_nim_type.nim",
     "type mismatch"),
    ("tests/fixtures/embedded_err_binding_senary_eponym_type.nim",
     "typed n-ary adapter requires postulate 'sumSix' to have type Int -> Int -> Int -> Int -> Nat -> Int -> Int"),
    ("tests/fixtures/embedded_err_runtime_enum_payload.nim",
     "requires only nullary constructors returning the unindexed family"),
    ("tests/fixtures/embedded_err_runtime_option_shape.nim",
     "runtimeOption requires a Type -> Type family"),
    ("tests/fixtures/embedded_err_runtime_codec_signature.nim", "type mismatch"),
    ("tests/fixtures/embedded_err_dependent_sigma_postulate_binding.nim",
     "structured pair adapter requires postulate 'makeDependentPair'"),
    ("tests/fixtures/embedded_err_pair_binding_nim_type.nim", "type mismatch"),
    ("tests/fixtures/embedded_err_binding_unused.nim",
     "binding for postulate 'hostStepPostulate' is unused"),
    ("tests/fixtures/embedded_err_binding_duplicate.nim",
     "duplicate bindPostulate for 'hostStepPostulate'"),
    ("tests/fixtures/embedded_err_binding_quaternary_type.nim",
     "opaque quaternary adapter requires postulate 'hostFourPostulate'"),
    ("tests/fixtures/embedded_err_unsupported_operator.nim",
     "unsupported pure operator 'div'"),
    ("tests/fixtures/embedded_err_if_missing_else.nim",
     "requires a condition and an else branch"),
    ("tests/fixtures/embedded_err_runtime_dps_quantity.nim",
     "runtimeDps requires every parameter to be marked {.linear.}"),
    ("tests/fixtures/embedded_err_runtime_dps_term.nim",
     "runtimeDps supports only fully applied Int primitives")]:
  if not checkFixture(path, expected):
    inc failed

if failed > 0:
  echo failed, " error-path fixture(s) misbehaved"
  quit(1)
echo "--- embedded error paths are clean ---"
