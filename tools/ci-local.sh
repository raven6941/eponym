#!/bin/sh
# tools/ci-local.sh — the CI matrix, runnable locally.
#
# This script IS the CI: .github/workflows/ci.yml calls it after setting up
# the toolchain. Run it locally before every merge:
#   sh tools/ci-local.sh
# It exits non-zero on the first failure. Requires: nim (>= 2.0) on PATH,
# node + npm for the VSCode extension smoke test.
#
# Do not reconstruct CI from the YAML — edit this script, and CI follows.

set -e
cd "$(dirname "$0")/.."

P="--path:src --path:src/eponym"
XP="$P --path:src/experimental --path:src/experimental/relational --path:src/experimental/staging"

nim --version

echo "### Dependencies: install falsify (issue: eponym PBT migration)"
# falsify is not in nimble's package index yet, so install it explicitly
# from GitHub. `import falsify` in tests/pbt_*.nim then resolves via
# nimble's package dir on nim's default import path.
nimble install -y https://github.com/raven6941/falsify

echo "### Build: production modules"
# Production module list: keep in sync with eponym.nimble's `buildall` task
# and `installFiles` (the installed set; issue #183). These are the full
# import closure of the public entry points (issue #189): every module a
# user compile pulls in must also build standalone in CI.
for f in abilities codegen eponym_init erasure preterm parse_surf elab elab_prof unify usage_check eponym_mac lsp egraph eponym_embed kernel_check sheds sheds_mac shed_layout mutual_termination; do
  echo "=== build $f ==="
  nim c --hints:off $P "src/eponym/$f.nim"
done
echo "=== build repl (issue #50) ==="
nim c --hints:off $P "src/repl.nim"
echo "=== build experimental (issue #189: kept building, clearly labeled) ==="
for f in eponym mac_surf heap qtt_proto; do
  echo "=== build experimental/$f ==="
  nim c --hints:off $XP "src/experimental/$f.nim"
done

echo "### Test: module suites"
for f in eponym_init preterm parse_surf elab unify eponym_mac egraph eponym_embed kernel_check; do
  echo "=== test $f ==="
  nim c -r --hints:off $P "src/eponym/$f.nim"
done
echo "=== examples ==="
nim c -r --hints:off $P "tests/run_examples.nim"
echo "=== imported source locations ==="
nim c -r --hints:off $P "tests/test_imported_source_locations.nim"
echo "=== error-message snapshots (issue #34) ==="
nim c -r --hints:off $P "tests/error_snapshots.nim"
echo "=== elaboration trace (issue #83) ==="
nim c -r --hints:off $P "tests/test_elab_trace.nim"
echo "=== repl scripted session (issue #50) ==="
sh tests/repl_session.sh
echo "=== kernel audit (issue #62: independent re-check) ==="
nim c -r --hints:off $P "tests/kernel_audit.nim"
echo "=== embedded examples (issue #149) ==="
nim c -r --hints:off $P "tests/run_embedded_examples.nim"
echo "=== package prelude resolution ==="
sh tests/test_package_prelude_install.sh
echo "=== surface-syntax conformance (issue #144) ==="
nim c -r --hints:off $P "tests/surface_conformance.nim"
echo "=== elaboration adequacy properties (issue #38) ==="
nim c -r --hints:off $P "tests/adequacy_props.nim"
echo "=== embedded macro forms (issue #151) ==="
nim c -r --hints:off $P "tests/test_embedded_macro_forms.nim"
echo "=== explicit Eponym parameters in Nim brackets ==="
nim c -r --hints:off $P "tests/test_embedded_explicit_params.nim"
echo "=== legacy explicit-parameter migration diagnostic ==="
nim c -r --hints:off $P "tests/test_embedded_legacy_syntax.nim"
echo "=== chained pure if/elif expressions ==="
nim c -r --hints:off $P "tests/test_embedded_chained_if.nim"
nim c -r --hints:off $P "tests/test_embedded_if_effects.nim"
echo "=== runtime Value bridge properties ==="
nim c -r --hints:off $P "tests/test_runtime_value_bridge.nim"
echo "=== per-block trust boundary report (#374) ==="
sh tests/test_trust_report.sh
echo "=== certified objective runtime properties ==="
nim c -r --hints:off $P "tests/test_convex_opt_runtime.nim"
nim c -r --hints:off $P "tests/test_convex_opt_vec_runtime.nim"
echo "=== checked Paxos loopback properties ==="
nim c -r --hints:off $P "tests/test_paxos_session_runtime.nim"
echo "=== checked borrow adapter properties ==="
nim c -r --hints:off $P "tests/test_borrow_runtime.nim"
echo "=== Nat postulate binding identity ==="
nim c -r --hints:off $P "tests/test_nat_binding_identity.nim"
echo "=== explicit Nat-to-Int conversion ==="
nim c -r --hints:off $P "tests/test_nat_to_int.nim"
echo "=== checked debug echo runtime property ==="
nim c -r --hints:off $P "tests/test_debug_echo.nim"
echo "=== opaque Float/String/Char runtime mappings ==="
nim c -r --hints:off $P "tests/test_scalar_runtime_codecs.nim"
echo "=== checked TCP session loopback integration ==="
nim c -r --hints:off $P "tests/test_session_tcp_bindings.nim"
echo "=== embedded error paths (issue #199) ==="
nim c -r --hints:off $P "tests/test_embedded_error_path.nim"
echo "=== staging soundness fuzz (issue #29, fixed seed; experimental paths) ==="
nim c -r --hints:off $XP "tests/fuzz_soundness.nim" -- --seed 424242 -n 1000
echo "=== egraph property tests (issue #163, fixed seed) ==="
nim c -r --hints:off $P "tests/pbt_egraph.nim"
echo "=== egraph model-based command sequences (falsify runCommands) ==="
nim c -r --hints:off $P "tests/pbt_egraph_commands.nim"
echo "=== minikanren property tests (issue #163, fixed seed; experimental paths) ==="
nim c -r --hints:off $XP "tests/pbt_minikanren.nim"
echo "=== clause-matrix differential tests (issue #163, fixed seed) ==="
nim c -r --hints:off $P "tests/pbt_clause_matrix.nim"
echo "=== clause-matrix negative tests (issue #163, fixed seed) ==="
nim c -r --hints:off $P "tests/pbt_clause_matrix_neg.nim"
echo "=== QTT usage-checker property tests (issue #163, fixed seed) ==="
nim c -r --hints:off $P "tests/pbt_usage.nim"
echo "=== core QTT erasure differential tests (issue #328) ==="
nim c -r --hints:off $P "tests/test_erasure.nim"
echo "=== Phase 1 codegen differential tests (issue #329) ==="
nim c -r --hints:off $P "tests/test_codegen_phase1.nim"
echo "=== Phase 2 codegen differential tests + benchmark (issue #330) ==="
nim c -r --hints:off $P "tests/test_codegen_phase2.nim"
echo "=== Phase 2 Vec codegen differential tests + benchmark (issue #330 v3) ==="
nim c -r --hints:off $P "tests/test_codegen_phase2_vec.nim"
echo "=== Phase 2 List codegen differential tests + benchmark (issue #330 v3) ==="
nim c -r --hints:off $P "tests/test_codegen_phase2_list.nim"
echo "=== Phase 2 Option codegen differential tests + benchmark (issue #330 v3) ==="
nim c -r --hints:off $P "tests/test_codegen_phase2_option.nim"
echo "=== Phase 2 Vec end-to-end wrapper test (issue #330 v3) ==="
nim c -r --hints:off $P "tests/test_codegen_phase2_vec_e2e.nim"
echo "=== interpreter-free static wrapper artifact audit (issue #358) ==="
nim c -r --hints:off $P "tests/test_require_compiled.nim"
echo "=== staged-residual vs relational differential tests (issue #163, fixed seed; experimental paths) ==="
nim c -r --hints:off $XP "tests/pbt_staged_agreement.nim"
echo "=== unifier property tests (issue #163, fixed seed) ==="
nim c -r --hints:off $P "tests/pbt_unify.nim"
# Note: lsp is built but not run — it's a server that blocks on stdin,
# not a test suite. (Was hanging CI since Experiment 7.)
echo "=== lsp hole-session tests (issue #58, headless mock-LSP) ==="
nim c -r --hints:off $P "tests/test_lsp_holes.nim"
nim c -r --hints:off $P "tests/test_lsp_actions.nim"
echo "=== sheds tests (issues #133-135, #137) ==="
nim c -r --hints:off $P "tests/test_sheds.nim"
nim c -r --hints:off $P "tests/test_shed_layout.nim"
nim c -r --hints:off $P "tests/test_shed_loop.nim"
nim c -r --hints:off $P "tests/test_shed_refine_method.nim"
nim c -r --hints:off $P "tests/test_shed_sidecar_reset.nim"
echo "=== mutual termination graph tests (issue #42) ==="
nim c -r --hints:off $P "tests/test_mutual_termination.nim"
echo "=== vscode extension smoke (issue #136 client path, real lsp binary) ==="
# The smoke test self-provisions the shed sidecar: it exercises the
# extension's own generateSidecar path (issue #153) on the demo before
# reading layouts from it. The sidecar is gitignored (*.sheds.json),
# so this also covers the fresh-checkout case (was issue #142's fix).
(cd editors/vscode && npm install --no-audit --no-fund && npm run build)
LSP=src/eponym/lsp DEMO=examples/embedded/sheds_demo.nim node editors/vscode/out/smoke.js
# Note: bench/ contains expensive benchmarks, not run in CI.

echo "### CI PASSED"
