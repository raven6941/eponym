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

extractTutorialSnippet() {
  snippetName=$1
  outputPath=$2
  awk -v marker="<!-- tutorial-smoke: $snippetName -->" \
    '$0 == marker { marked = 1; next }
     marked && /^```nim$/ { inside = 1; marked = 0; next }
     inside && /^```/ { exit }
     inside { print }' "$eponymRepoRoot/docs/tutorial.md" > "$outputPath"
  if [ ! -s "$outputPath" ]; then
    echo "could not extract tutorial snippet: $snippetName" >&2
    exit 1
  fi
}

extractTutorialSnippet hello "$eponymTmpDir/project/hello.nim"
extractTutorialSnippet vecs "$eponymTmpDir/project/vecs.nim"
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
cat > "$eponymTmpDir/project/nat_to_int.nim" <<'EOF'
import eponym_mac
import eponym_embed

proc addHostOffset(value: int): int = value + 7

eponymBlock:
  import "lib/nat_to_int.ep"
  postulate(addHostOffsetPostulate, Int -> Int)
  bindPostulate(addHostOffsetPostulate, addHostOffset)
  proc convertNatThenCallHost(value: Nat): Int =
    addHostOffsetPostulate(natToInt(value))

doAssert convertNatThenCallHost(5) == 12
cat > "$eponymTmpDir/project/scalars.nim" <<'EOF'
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/float.ep"
  import "lib/text.ep"
  runtimeType(Float, float64)
  runtimeType(String, string)
  runtimeType(Char, char)
  proc keepFloat(value: Float): Float = value
  proc keepString(value: String): String = value
  proc keepChar(value: Char): Char = value

doAssert keepFloat(1.25) == 1.25
doAssert keepString("hello") == "hello"
doAssert keepChar('x') == 'x'
EOF
cat > "$eponymTmpDir/project/debug.nim" <<'EOF'
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  import "lib/debug.ep"
  bindPostulateValue(debugEcho, debugEchoRuntimeValue)
  proc checkedDebugEcho(value: Int): Int = debugEcho[Int](value)

doAssert checkedDebugEcho(42) == 42
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
nim c -r --path:"$eponymTmpDir/package" \
  --nimcache:"$eponymTmpDir/nat-to-int-cache" \
  --out:"$eponymTmpDir/nat_to_int" nat_to_int.nim
nim c -r --path:"$eponymTmpDir/package" \
  --nimcache:"$eponymTmpDir/debug-cache" \
  --out:"$eponymTmpDir/debug" debug.nim
nim c -r --path:"$eponymTmpDir/package" \
  --nimcache:"$eponymTmpDir/scalars-cache" \
  --out:"$eponymTmpDir/scalars" scalars.nim
