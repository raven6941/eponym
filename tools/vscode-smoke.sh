#!/bin/sh
# tools/vscode-smoke.sh — VSCode extension smoke test.
#
# Extracted verbatim from tools/ci-local.sh (issue #136 client path, real
# lsp binary) so the affected-only runner (issue #405) can invoke it as a
# plain step. Behavior is unchanged: same nimcache, same flags, same order.
#
# The smoke test self-provisions the shed sidecar: it exercises the
# extension's own generateSidecar path (issue #153) on the demo before
# reading layouts from it. The sidecar is gitignored (*.sheds.json),
# so this also covers the fresh-checkout case (was issue #142's fix).

set -e
cd "$(dirname "$0")/.."

P="--path:src --path:src/eponym"
NC_DIR="${EPONYM_NIMCACHE:-$HOME/.cache/eponym-ci-nimcache}"
mkdir -p "$NC_DIR"
NC="--nimcache:$NC_DIR"

# Depends on the lsp binary from the production-build section; in a
# sharded run that build may belong to another shard, so build it here
# too (the nimcache makes the rebuild cheap when it already ran).
nim c $NC --hints:off $P "src/eponym/lsp.nim"
(cd editors/vscode && npm install --no-audit --no-fund && npm run build)
LSP=src/eponym/lsp DEMO=examples/embedded/sheds_demo.nim node editors/vscode/out/smoke.js
