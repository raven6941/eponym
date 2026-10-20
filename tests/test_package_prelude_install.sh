#!/bin/sh
set -eu

eponymRepoRoot=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
eponymTmpDir=$(mktemp -d "${TMPDIR:-/tmp}/eponym-package.XXXXXX")
trap 'rm -rf "$eponymTmpDir"' EXIT

mkdir -p "$eponymTmpDir/package/src" "$eponymTmpDir/project"
cp -R "$eponymRepoRoot/src/eponym" "$eponymTmpDir/package/src/eponym"
cp -R "$eponymRepoRoot/lib" "$eponymTmpDir/package/lib"
cp "$eponymRepoRoot/tests/test_prelude_resolution.nim" \
  "$eponymTmpDir/project/main.nim"

cd "$eponymTmpDir/project"
nim c -r --path:"$eponymTmpDir/package/src/eponym" \
  --nimcache:"$eponymTmpDir/nimcache" \
  --out:"$eponymTmpDir/test_prelude_resolution" main.nim
