#!/bin/sh
# tools/test-affected.sh — run only the CI steps affected by local changes.
#
# Issue #405. Dev-loop accelerator: the full matrix (tools/ci-local.sh)
# remains the merge gate and is unchanged; this selects the affected subset
# of its steps so most edits re-run in minutes instead of ~24.
#
# Selection is conservative: a step runs if any changed file is in its Nim
# import closure, its macro-time .ep inputs, or its directory-walk inputs;
# anything that cannot be classified selects every step. See
# tools/test-affected.py (the implementation) for the full model.
#
# Usage:
#   sh tools/test-affected.sh [--base REF] [--changed PATH]... [--all]
#                             [--dry-run] [--verbose] [--self-test]
#
#   --base REF      git ref to diff against (default: main)
#   --changed PATH  repeatable; bypass git change detection (debugging aid)
#   --all           run the full matrix (same as tools/ci-local.sh)
#   --dry-run       print the plan without running anything
#   --verbose       also list skipped steps
#   --self-test     validate the mapping model; exits non-zero on failure
#
# Requires: python3, nim (>= 2.0) on PATH
#   (export PATH="$HOME/.nimble/bin:$PATH"; see TOOLS.md: Nim toolchain).
# Never run two instances concurrently against the same nimcache (see the
# WARNING in tools/ci-local.sh); EPONYM_NIMCACHE is honored the same way.

set -eu
cd "$(dirname "$0")/.."
exec python3 tools/test-affected.py "$@"
