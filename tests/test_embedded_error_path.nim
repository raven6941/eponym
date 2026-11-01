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

proc checkRuntimeFixture(path, expected: string): bool =
  let name = path.splitFile().name
  let bin = tmpDir / name
  let (cOut, cCode) = execCmdEx("nim c --hints:off -d:eponymRuntimeBridgeTests " & pathFlags &
    " --out:" & quoteShell(bin) & " " & quoteShell(path))
  if cCode != 0:
    echo "FAIL (runtime fixture did not compile): ", path
    echo cOut
    return false
  let (rOut, rCode) = execCmdEx(quoteShell(bin))
  if rCode == 0 or expected notin rOut:
    echo "FAIL (missing named runtime shape error): ", path
    echo rOut
    return false
  echo "ok (named runtime shape error): ", path
  true

var failed = 0
for path in ["tests/fixtures/embedded_err_unbound.nim",
             "tests/fixtures/embedded_err_mismatch.nim",
             "tests/fixtures/embedded_err_singleton_mismatch.nim",
             "tests/fixtures/embedded_err_implicit_nat_to_int.nim",
             "tests/fixtures/embedded_err_scalar_type_mismatch.nim"]:
  if not checkFixture(path):
    inc failed

for (path, expected) in [
    ("tests/fixtures/embedded_err_lambda_call.nim",
     "lambda call forms were removed"),
    ("tests/fixtures/embedded_err_nonlambda_fatarrow.nim",
     "`=>` is only supported after a lam binder group")]:
  if not checkFixture(path, expected):
    inc failed

for (path, expected) in [
    ("tests/fixtures/typed_adapter_err_shape_scalar.nim",
     "bindPostulateValue 'debugEcho' argument 0 shape mismatch: expected Int"),
    ("tests/fixtures/typed_adapter_err_shape_function.nim",
     "bindPostulateValue 'applyCallback' argument 0 shape mismatch: expected function (Pi)")]:
  if not checkRuntimeFixture(path, expected):
    inc failed

for (path, expected) in [
    ("tests/fixtures/embedded_err_q1_if_one_branch.nim",
     "used 0 or 1 time(s)"),
    ("tests/fixtures/embedded_err_q1_if_duplicate_branch.nim",
     "used 1 or 2+ time(s)"),
    ("tests/fixtures/embedded_err_q1_option_one_branch.nim",
     "used 0 or 1 time(s)"),
    ("tests/fixtures/embedded_err_q1_option_duplicate_branch.nim",
     "used 1 or 2+ time(s)")]:
  if not checkFixture(path, expected):
    inc failed

if not checkFixture("tests/fixtures/embedded_err_nat_literal_index.nim",
    "does not match expected type"):
  inc failed

if not checkFixture("tests/fixtures/embedded_err_source_map.nim",
    "embedded_err_source_map.nim(8,"):
  inc failed

for (path, expected) in [
    ("tests/fixtures/embedded_err_binding_eponym_type.nim",
     "eponymBlock binding error"),
    ("tests/fixtures/embedded_err_binding_nim_type.nim",
     "eponymBlock requireCompiled: definition 'checkedRole' has no representation-compiled body"),
    ("tests/fixtures/embedded_err_binding_opaque_nim_type.nim",
     "type mismatch"),
    ("tests/fixtures/embedded_err_unsupported_runtime_type.nim",
     "eponymBlock requireCompiled: definition 'identity' has no representation-compiled body"),
    ("tests/fixtures/embedded_err_unmapped_clause_wrapper.nim",
     "eponymBlock requireCompiled: definition 'tokenIdentity' has no representation-compiled body"),
    ("tests/fixtures/embedded_err_dependent_sigma_runtime.nim",
     "eponymBlock requireCompiled: definition 'dependentSigmaId' has no representation-compiled body"),
    ("tests/fixtures/embedded_err_generic_dependent_record_untrusted.nim",
     "eponymBlock requireCompiled does not emit runtimeValue wrappers"),
    ("tests/fixtures/embedded_err_dependent_record_runtime.nim",
     "eponymBlock requireCompiled: no typed runtime wrapper for 'pointId'"),
    ("tests/fixtures/embedded_err_bool_without_prelude.nim",
     "Bool constructor 'true' is not declared; import bool.ep"),
    ("tests/fixtures/embedded_err_generic_runtime_index.nim",
     "eponymBlock requireCompiled does not emit runtimeValue wrappers"),
    ("tests/fixtures/embedded_err_generic_callback_inference.nim",
     "eponymBlock requireCompiled does not emit runtimeValue wrappers"),
    ("tests/fixtures/embedded_err_generic_callback_vector_inference.nim",
     "eponymBlock requireCompiled does not emit runtimeValue wrappers"),
    ("tests/fixtures/embedded_err_binding_quinary_nim_type.nim",
     "type mismatch"),
    ("tests/fixtures/embedded_err_binding_senary_eponym_type.nim",
     "typed n-ary adapter requires postulate 'sumSix' to have type Int -> Int -> Int -> Int -> Nat -> Int -> Int"),
    ("tests/fixtures/embedded_err_runtime_enum_payload.nim",
     "requires only nullary constructors returning the unindexed family"),
    ("tests/fixtures/embedded_err_runtime_option_shape.nim",
     "runtimeOption requires a Type -> Type family"),
    ("tests/fixtures/embedded_err_runtime_nimcall_result.nim",
     "eponymBlock requireCompiled: definition 'generatedAdder' has no representation-compiled body"),
    ("tests/fixtures/embedded_err_runtime_codec_signature.nim",
     "eponymBlock requireCompiled: definition 'identity' has no representation-compiled body"),
    ("tests/fixtures/embedded_err_dependent_sigma_postulate_binding.nim",
     "structured pair adapter requires postulate 'makeDependentPair'"),
    ("tests/fixtures/embedded_err_pair_binding_nim_type.nim",
     "eponymBlock requireCompiled: definition 'generatedSplitChannel' has no representation-compiled body"),
    ("tests/fixtures/embedded_err_binding_unused.nim",
     "binding for postulate 'hostStepPostulate' is unused"),
    ("tests/fixtures/embedded_err_binding_duplicate.nim",
     "duplicate bindPostulate for 'hostStepPostulate'"),
    ("tests/fixtures/embedded_err_binding_quaternary_type.nim",
     "opaque quaternary adapter requires postulate 'hostFourPostulate'"),
    ("tests/fixtures/embedded_err_require_compiled_unsupported.nim",
     "eponymBlock requireCompiled: definition 'applyQ0' has no representation-compiled body: Phase 2 unavailable: non-atomic binder domain (quantity-0 function domain has no host representation)"),
    ("tests/fixtures/embedded_err_require_compiled_erased_vec_index.nim",
     "eponymBlock requireCompiled: definition 'keepVector' has no representation-compiled body: Phase 2 unavailable: Vec length index mentions an erased binder"),
    ("tests/fixtures/embedded_err_require_compiled_dynamic.nim",
     "eponymBlock requireCompiled does not emit runtimeValue wrappers"),
    ("tests/fixtures/embedded_err_runtime_type_staging.nim",
     "eponymBlock runtimeType staging error"),
    ("tests/fixtures/embedded_err_unsupported_operator.nim",
     "unsupported pure operator 'div'"),
    ("tests/fixtures/embedded_err_unsupported_string_literal.nim",
     "unsupported Nim expression shape 'nnkStrLit'"),
    ("tests/fixtures/embedded_err_if_missing_else.nim",
     "requires a condition and an else branch"),
    ("tests/fixtures/embedded_err_named_argument_unknown.nim",
     "unknown named argument 'other'"),
    ("tests/fixtures/embedded_err_named_argument_duplicate.nim",
     "duplicate argument for 'left'"),
    ("tests/fixtures/embedded_err_named_argument_missing.nim",
     "missing required argument for 'right'"),
    ("tests/fixtures/typed_adapter_err_nonstatic.nim",
     "bindPostulateValue 'debugEcho' applied at a non-static type")]:
  if not checkFixture(path, expected):
    inc failed

if failed > 0:
  echo failed, " error-path fixture(s) misbehaved"
  quit(1)
echo "--- embedded error paths are clean ---"
