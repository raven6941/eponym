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
#
# Sharding (issue #404): EPONYM_CI_SHARD="INDEX/COUNT" (e.g. "1/3") runs
# only the steps assigned to that shard, round-robin in the order below.
# Every step belongs to exactly one shard, steps keep their relative order
# within a shard, and the unsharded default ("0/1") runs everything — the
# full matrix remains the merge gate; a sharded run is partial by design.
# GitHub CI runs 3 shards on separate runners for parallel drivers.
#
# WARNING: never run two instances concurrently against the same nimcache.
# Nim emits per-compilation unique symbol suffixes, and concurrent nim
# processes overwriting each other's shared-module .c/.o files in one
# nimcache produce link failures with undefined references (diagnosed on
# issue #404). Parallel local shard runs must each set their own
# EPONYM_NIMCACHE (e.g. ~/.cache/eponym-ci-nimcache-shard0).

set -e
cd "$(dirname "$0")/.."

P="--path:src --path:src/eponym"
# One nimcache shared by every suite in this run (and, locally, across
# worktrees and runs): the ~50 test drivers import the same elaborator
# closure, and per-driver caches recompile it from scratch every time.
# Override with EPONYM_NIMCACHE; the default lives outside the checkout.
NC_DIR="${EPONYM_NIMCACHE:-$HOME/.cache/eponym-ci-nimcache}"
mkdir -p "$NC_DIR"
NC="--nimcache:$NC_DIR"
XP="$P --path:src/experimental --path:src/experimental/relational --path:src/experimental/staging"

# --- Shard assignment -------------------------------------------------------
SHARD_INDEX=0
SHARD_COUNT=1
if [ -n "${EPONYM_CI_SHARD:-}" ]; then
  case "$EPONYM_CI_SHARD" in
    */*) ;;
    *) echo "EPONYM_CI_SHARD must be INDEX/COUNT, got: $EPONYM_CI_SHARD" >&2; exit 2 ;;
  esac
  SHARD_INDEX=${EPONYM_CI_SHARD%%/*}
  SHARD_COUNT=${EPONYM_CI_SHARD#*/}
  case "$SHARD_INDEX$SHARD_COUNT" in
    *[!0-9]*|"") echo "EPONYM_CI_SHARD must be numeric INDEX/COUNT, got: $EPONYM_CI_SHARD" >&2; exit 2 ;;
  esac
  if [ "$SHARD_COUNT" -lt 1 ] || [ "$SHARD_INDEX" -ge "$SHARD_COUNT" ]; then
    echo "EPONYM_CI_SHARD out of range: $EPONYM_CI_SHARD" >&2; exit 2
  fi
fi

STEP_N=0
run_step() {
  STEP_N=$((STEP_N + 1))
  if [ $(((STEP_N - 1) % SHARD_COUNT)) -ne $SHARD_INDEX ]; then
    echo "=== skip step $STEP_N (shard $SHARD_INDEX/$SHARD_COUNT): $* ==="
    return 0
  fi
  echo "=== step $STEP_N: $* ==="
  "$@" || { _rc=$?; echo "step $STEP_N FAILED (exit $_rc): $*" >&2; exit $_rc; }
}

echo "shard: $SHARD_INDEX/$SHARD_COUNT"
nim --version

echo "### Dependencies: install falsify (issue: eponym PBT migration)"
# falsify is not in nimble's package index yet, so install it explicitly
# from GitHub. `import falsify` in tests/pbt_*.nim then resolves via
# nimble's package dir on nim's default import path.
if nimble path falsify >/dev/null 2>&1; then
  echo "falsify already installed; skipping reinstall"
else
  nimble install -y https://github.com/raven6941/falsify
fi

echo "### Build: production modules"
# Production module list: keep in sync with eponym.nimble's `buildall` task
# and `installFiles` (the installed set; issue #183). These are the full
# import closure of the public entry points (issue #189): every module a
# user compile pulls in must also build standalone in CI.
for f in abilities codegen eponym_init erasure preterm parse_surf elab elab_prof unify usage_check eponym_mac lsp egraph eponym_embed kernel_check sheds sheds_mac shed_layout mutual_termination; do
  run_step nim c $NC --hints:off $P "src/eponym/$f.nim"
done
# Build repl (issue #50)
run_step nim c $NC --hints:off $P "src/repl.nim"
echo "### Build: experimental (issue #189: kept building, clearly labeled)"
for f in eponym mac_surf heap qtt_proto; do
  run_step nim c $NC --hints:off $XP "src/experimental/$f.nim"
done

echo "### Test: module suites"
for f in eponym_init preterm parse_surf elab unify eponym_mac egraph eponym_embed kernel_check; do
  run_step nim c -r $NC --hints:off $P "src/eponym/$f.nim"
done
run_step nim c -r $NC --hints:off $P "tests/run_examples.nim"
run_step nim c -r $NC --hints:off $P "tests/test_imported_source_locations.nim"
# Error-message snapshots (issue #34)
run_step nim c -r $NC --hints:off $P "tests/error_snapshots.nim"
# Elaboration trace (issue #83)
run_step nim c -r $NC --hints:off $P "tests/test_elab_trace.nim"
# REPL scripted session (issue #50)
run_step sh tests/repl_session.sh
# Kernel audit (issue #62: independent re-check)
run_step nim c -r $NC --hints:off $P "tests/kernel_audit.nim"
# Embedded examples (issue #149)
run_step nim c -r $NC --hints:off $P "tests/run_embedded_examples.nim"
run_step sh tests/test_package_prelude_install.sh
# Surface-syntax conformance (issue #144)
run_step nim c -r $NC --hints:off $P "tests/surface_conformance.nim"
# Elaboration adequacy properties (issue #38)
run_step nim c -r $NC --hints:off $P "tests/adequacy_props.nim"
# Embedded macro forms (issue #151)
run_step nim c -r $NC --hints:off $P "tests/test_embedded_macro_forms.nim"
run_step nim c -r $NC --hints:off $P "tests/test_embedded_explicit_params.nim"
run_step nim c -r $NC --hints:off $P "tests/test_embedded_legacy_syntax.nim"
run_step nim c -r $NC --hints:off $P "tests/test_embedded_chained_if.nim"
run_step nim c -r $NC --hints:off $P "tests/test_embedded_if_effects.nim"
run_step nim c -r $NC --hints:off $P "tests/test_runtime_value_bridge.nim"
# Per-block trust boundary report (#374)
run_step sh tests/test_trust_report.sh
run_step nim c -r $NC --hints:off $P "tests/test_convex_opt_runtime.nim"
run_step nim c -r $NC --hints:off $P "tests/test_convex_opt_vec_runtime.nim"
run_step nim c -r $NC --hints:off $P "tests/test_paxos_session_runtime.nim"
run_step nim c -r $NC --hints:off $P "tests/test_borrow_runtime.nim"
run_step nim c -r $NC --hints:off $P "tests/test_nat_binding_identity.nim"
run_step nim c -r $NC --hints:off $P "tests/test_nat_to_int.nim"
run_step nim c -r $NC --hints:off $P "tests/test_int_to_nat.nim"
run_step nim c -r $NC --hints:off $P "tests/test_debug_echo.nim"
run_step nim c -r $NC --hints:off $P "tests/test_scalar_runtime_codecs.nim"
run_step nim c -r $NC --hints:off $P "tests/test_session_tcp_bindings.nim"
# Embedded error paths (issue #199)
run_step nim c -r $NC --hints:off $P "tests/test_embedded_error_path.nim"
# Staging soundness fuzz (issue #29, fixed seed; experimental paths)
run_step nim c -r $NC --hints:off $XP "tests/fuzz_soundness.nim" -- --seed 424242 -n 1000
# Egraph property tests (issue #163, fixed seed)
run_step nim c -r $NC --hints:off $P "tests/pbt_egraph.nim"
# Egraph model-based command sequences (falsify runCommands)
run_step nim c -r $NC --hints:off $P "tests/pbt_egraph_commands.nim"
# Minikanren property tests (issue #163, fixed seed; experimental paths)
run_step nim c -r $NC --hints:off $XP "tests/pbt_minikanren.nim"
# Clause-matrix differential tests (issue #163, fixed seed)
run_step nim c -r $NC --hints:off $P "tests/pbt_clause_matrix.nim"
# Clause-matrix negative tests (issue #163, fixed seed)
run_step nim c -r $NC --hints:off $P "tests/pbt_clause_matrix_neg.nim"
# QTT usage-checker property tests (issue #163, fixed seed)
run_step nim c -r $NC --hints:off $P "tests/pbt_usage.nim"
# Core QTT erasure differential tests (issue #328)
run_step nim c -r $NC --hints:off $P "tests/test_erasure.nim"
# Phase 1 codegen differential tests (issue #329)
run_step nim c -r $NC --hints:off $P "tests/test_codegen_phase1.nim"
# Phase 2 codegen differential tests + benchmark (issue #330)
run_step nim c -r $NC --hints:off $P "tests/test_codegen_phase2.nim"
# Phase 2 Vec codegen differential tests + benchmark (issue #330 v3)
run_step nim c -r $NC --hints:off $P "tests/test_codegen_phase2_vec.nim"
# Phase 2 List codegen differential tests + benchmark (issue #330 v3)
run_step nim c -r $NC --hints:off $P "tests/test_codegen_phase2_list.nim"
# Phase 2 Option codegen differential tests + benchmark (issue #330 v3)
run_step nim c -r $NC --hints:off $P "tests/test_codegen_phase2_option.nim"
# Phase 2 Vec end-to-end wrapper test (issue #330 v3)
run_step nim c -r $NC --hints:off $P "tests/test_codegen_phase2_vec_e2e.nim"
run_step nim c -r $NC --hints:off $P "tests/test_require_compiled.nim"
# Paxos under requireCompiled: opaque/index-erased families + dependent Sigma (issue #401)
run_step nim c -r $NC --hints:off $P "tests/test_require_compiled_paxos.nim"
# Phase 3 DPS Vec fold tests + benchmark (issue #331)
run_step nim c -r $NC --hints:off $P "tests/test_codegen_phase3_dps_vec.nim"
# Phase 3 DPS List fold tests + benchmark (issue #331)
run_step nim c -r $NC --hints:off $P "tests/test_codegen_phase3_dps_list.nim"
# Staged-residual vs relational differential tests (issue #163, fixed seed; experimental paths)
run_step nim c -r $NC --hints:off $XP "tests/pbt_staged_agreement.nim"
# Unifier property tests (issue #163, fixed seed)
run_step nim c -r $NC --hints:off $P "tests/pbt_unify.nim"
# Note: lsp is built but not run as a module suite — it's a server that
# blocks on stdin, not a test suite. (Was hanging CI since Experiment 7.)
# LSP hole-session tests (issue #58, headless mock-LSP)
run_step nim c -r $NC --hints:off $P "tests/test_lsp_holes.nim"
run_step nim c -r $NC --hints:off $P "tests/test_lsp_actions.nim"
# Sheds tests (issues #133-135, #137)
run_step nim c -r $NC --hints:off $P "tests/test_sheds.nim"
run_step nim c -r $NC --hints:off $P "tests/test_shed_layout.nim"
run_step nim c -r $NC --hints:off $P "tests/test_shed_loop.nim"
run_step nim c -r $NC --hints:off $P "tests/test_shed_refine_method.nim"
run_step nim c -r $NC --hints:off $P "tests/test_shed_sidecar_reset.nim"
run_step nim c -r $NC --hints:off $P "tests/test_shed_refine_roundtrip.nim"
# Mutual termination graph tests (issue #42)
run_step nim c -r $NC --hints:off $P "tests/test_mutual_termination.nim"

# VSCode extension smoke (issue #136 client path, real lsp binary).
# The smoke test self-provisions the shed sidecar: it exercises the
# extension's own generateSidecar path (issue #153) on the demo before
# reading layouts from it. The sidecar is gitignored (*.sheds.json),
# so this also covers the fresh-checkout case (was issue #142's fix).
vscode_smoke() {
  # Depends on the lsp binary from the production-build section; in a
  # sharded run that build may belong to another shard, so build it here
  # too (the nimcache makes the rebuild cheap when it already ran).
  nim c $NC --hints:off $P "src/eponym/lsp.nim" || return $?
  (cd editors/vscode && npm install --no-audit --no-fund && npm run build) || return $?
  LSP=src/eponym/lsp DEMO=examples/embedded/sheds_demo.nim node editors/vscode/out/smoke.js
}
run_step vscode_smoke
# Note: bench/ contains expensive benchmarks, not run in CI.

echo "### CI PASSED (shard $SHARD_INDEX/$SHARD_COUNT, $STEP_N steps total)"
