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

cd "$eponymTmpDir/project"
nim c -r --path:"$eponymTmpDir/package/src/eponym" \
  --nimcache:"$eponymTmpDir/nimcache" \
  --out:"$eponymTmpDir/test_prelude_resolution" main.nim
nim c -r --path:"$eponymTmpDir/package/src/eponym" \
  --nimcache:"$eponymTmpDir/hello-cache" \
  --out:"$eponymTmpDir/hello" hello.nim
nim c --path:"$eponymTmpDir/package/src/eponym" \
  --nimcache:"$eponymTmpDir/vecs-cache" \
  --out:"$eponymTmpDir/vecs" vecs.nim
nim c -r --path:"$eponymTmpDir/package/src/eponym" \
  --nimcache:"$eponymTmpDir/lists-cache" \
  --out:"$eponymTmpDir/lists" lists.nim
