#!/bin/sh
set -eu
cd "$(dirname "$0")/.."

task_tmp="$(mktemp -d)"
trap 'rm -rf "$task_tmp"' EXIT HUP INT TERM
nim c -d:eponymRuntimeBridgeTests -d:eponymTrustReport --hints:off \
  --nimcache:"$task_tmp/nimcache" \
  --out:"$task_tmp/test_runtime_value_bridge" \
  --path:src --path:src/eponym \
  tests/test_runtime_value_bridge.nim >"$task_tmp/build.log" 2>&1

assert_report_contains() {
  if ! grep -Fq "$1" "$task_tmp/build.log"; then
    cat "$task_tmp/build.log" >&2
    echo "missing expected trust report line: $1" >&2
    exit 1
  fi
}

assert_report_contains "bindPostulateMutable(mutateCell, hostMutateCell)"
assert_report_contains "runtimeType(CellRef, MutableCellRef): Nim/Eponym type correspondence is trusted; host identity, aliasing, and lifetime rules remain with the caller"
assert_report_contains "runtimeCodec(Tree, seq[int]): custom encoder/decoder behavior is trusted"
assert_report_contains "runtimePairTrusted(generatedGenericDependentSigmaValueBinder)"
assert_report_contains "runtimeRecordTrusted(SizedVec)"
assert_report_contains "QTT single-use applies inside checked Eponym terms; Nim aliases"

echo "ok: compile-time trust report lists adapters, custom codecs, dependent opt-ins, and the Nim aliasing boundary"
