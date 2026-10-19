#!/bin/sh
set -eu

eponymRepoRoot=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
eponymTmpDir=$(mktemp -d "${TMPDIR:-/tmp}/eponym-package.XXXXXX")
trap 'rm -rf "$eponymTmpDir"' EXIT

mkdir -p "$eponymTmpDir/package" "$eponymTmpDir/project"
awk '
  /^installFiles[[:space:]]*=/ { inFiles = 1 }
  inFiles {
    remaining = $0
    while (match(remaining, /"[^"]+\.nim"/)) {
      print substr(remaining, RSTART + 1, RLENGTH - 2)
      remaining = substr(remaining, RSTART + RLENGTH)
    }
    if ($0 ~ /\]/) exit
  }
' "$eponymRepoRoot/eponym.nimble" |
while IFS= read -r moduleFile; do
  cp "$eponymRepoRoot/src/eponym/$moduleFile" \
    "$eponymTmpDir/package/$moduleFile"
done
cp -R "$eponymRepoRoot/lib" "$eponymTmpDir/package/lib"
cp "$eponymRepoRoot/tests/test_prelude_resolution.nim" \
  "$eponymTmpDir/project/main.nim"
cat > "$eponymTmpDir/project/hello.nim" <<'EOF'
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  proc double(x: Int): Int = addInt(x, x)

doAssert double(21) == 42
EOF
cat > "$eponymTmpDir/project/vecs.nim" <<'EOF'
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/vec.ep"
  proc twoNats(x: Nat, y: Nat): Vec[Nat, suc(suc(zero()))] =
    cons[Nat, suc(zero())](x, cons[Nat, zero()](y, vecnil[Nat]()))
  proc myAppend[A: Univ, n: Nat](x: A, xs: Vec[A, n]): Vec[A, suc(n)] =
    cons[A, n](x, xs)
  proc appendTwo(xs: Vec[Nat, suc(zero())],
                 ys: Vec[Nat, suc(zero())]): Vec[Nat, add(suc(zero()), suc(zero()))] =
    vappend[Nat, suc(zero()), suc(zero())](xs, ys)
  proc vlen(A: Univ, n: Nat, v: Vec[A, n]): Nat =
    vecElim[A](lam(i, Nat, lam(w, Vec[A, i], Nat)), zero(),
      lam(i, Nat, lam(x, A, lam(xs, Vec[A, i], lam(ih, Nat, suc(ih))))),
      n, v)
EOF
cat > "$eponymTmpDir/project/lists.nim" <<'EOF'
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/list.ep"
  postulate(Int, Univ)
  runtimeList(List)
  proc keepList(values: List[Int]): List[Int] = values

doAssert keepList(@[2, 3, 5]) == @[2, 3, 5]
EOF
cat > "$eponymTmpDir/project/options.nim" <<'EOF'
import std/options
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/option.ep"
  runtimeOption(Option)
  proc keepOption[A: Univ](value: Option[A]): Option[A] = value

doAssert keepOption[int](some(7)) == some(7)
doAssert keepOption[int](none(int)).isNone
EOF

cd "$eponymTmpDir/project"
nim c -r --path:"$eponymTmpDir/package" \
  --nimcache:"$eponymTmpDir/nimcache" \
  --out:"$eponymTmpDir/test_prelude_resolution" main.nim
nim c -r --path:"$eponymTmpDir/package" \
  --nimcache:"$eponymTmpDir/hello-cache" \
  --out:"$eponymTmpDir/hello" hello.nim
nim c --path:"$eponymTmpDir/package" \
  --nimcache:"$eponymTmpDir/vecs-cache" \
  --out:"$eponymTmpDir/vecs" vecs.nim
nim c -r --path:"$eponymTmpDir/package" \
  --nimcache:"$eponymTmpDir/lists-cache" \
  --out:"$eponymTmpDir/lists" lists.nim
nim c -r --path:"$eponymTmpDir/package" \
  --nimcache:"$eponymTmpDir/options-cache" \
  --out:"$eponymTmpDir/options" options.nim
