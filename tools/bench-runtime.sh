#!/bin/sh
# bench-runtime.sh — run the #432 runtime benchmark suite.
#
# Dev-only measurement instrument (NOT a CI gate): times representative
# eponym programs across the available execution paths (interpreter,
# Value backend, repr backend) and prints per-path wall-clock tables.
#
# This script is DELIBERATELY not wired into tools/ci-local.sh or any
# GitHub Actions workflow (issue #432 constraint). Run it on demand
# during development, debugging, and performance investigations.
#
# Usage: sh tools/bench-runtime.sh        # all drivers
#        sh tools/bench-runtime.sh dps     # subset by name fragment

set -e
cd "$(dirname "$0")/.."

P="--path:src --path:src/eponym"
export PATH="$HOME/.nimble/bin:$PATH"

run_driver() {
  # $1 = driver source under bench/; $2 = extra nim flags for that driver
  name=$(basename "$1" .nim)
  case "$name" in
    *"$FILTER"*)
      echo "### $name"
      nim c -r $P --path:tests --path:bench $2 "$1"
      ;;
  esac
}

FILTER="${1:-}"
run_driver bench/bench_runtime_dps_vec.nim ""
# The List interpreter recurses per element; the depth knob only raises the
# debug-build safety rail (no semantic change).
run_driver bench/bench_runtime_dps_list.nim "-d:nimCallDepthLimit=30000"
run_driver bench/bench_runtime_defheavy.nim ""

echo ""
echo "bench-runtime.sh done. Numbers are wall-clock on this machine; the"
echo "suite reports measurements, never verdicts (see AGENTS.md"
echo "benchmarking discipline: profile a surprising result before recording it)."
