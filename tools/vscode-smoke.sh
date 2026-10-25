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
NIMBLE_TEST_DIR=$(mktemp -d "${TMPDIR:-/tmp}/eponym-vscode-nimble.XXXXXX")
trap 'rm -rf "$NIMBLE_TEST_DIR"' EXIT
mkdir -p "$NIMBLE_TEST_DIR/home" "$NIMBLE_TEST_DIR/nimble" \
  "$NIMBLE_TEST_DIR/project" "$NIMBLE_TEST_DIR/storage"
printf '[]\n' > "$NIMBLE_TEST_DIR/nimble/packages_official.json"

# Depends on the lsp binary from the production-build section; in a
# sharded run that build may belong to another shard, so build it here
# too (the nimcache makes the rebuild cheap when it already ran).
nim c $NC --hints:off $P "src/eponym/lsp.nim"
(cd editors/vscode && npm install --no-audit --no-fund && npm run build)
HOME="$NIMBLE_TEST_DIR/home" LSP=src/eponym/lsp \
  DEMO=examples/embedded/sheds_demo.nim node editors/vscode/out/smoke.js

# Exercise the Marketplace-user path from outside the checkout: install the
# current package into an isolated Nimble directory, compile a shed file
# against that flat package, then start the installed-source LSP.
NIMBLE_DIR="$NIMBLE_TEST_DIR/nimble" nimble --offline install --accept
cat > "$NIMBLE_TEST_DIR/project/sheds_user.nim" <<'EOF'
import sheds_mac
import sheds

shedsBlock:
  import "nat.ep"
  proc installedUserGoal(n: Nat): Nat = ![installedBody]
EOF
NIMBLE_DIR="$NIMBLE_TEST_DIR/nimble" \
  HOME="$NIMBLE_TEST_DIR/home" \
  EPONYM_NIMBLE_PROJECT="$NIMBLE_TEST_DIR/project" \
  EPONYM_NIMBLE_STORAGE="$NIMBLE_TEST_DIR/storage" \
  node editors/vscode/out/nimbleSmoke.js
