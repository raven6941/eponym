#!/bin/sh
set -eu

eponymRepoRoot=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
eponymTmpDir=$(mktemp -d "${TMPDIR:-/tmp}/eponym-package.XXXXXX")
trap 'rm -rf "$eponymTmpDir"' EXIT
cd "$eponymRepoRoot"

# Nimble consults its local package-index cache even for offline local
# installs. An empty cache is enough here because Eponym has no external
# install dependencies; this keeps the smoke test hermetic.
mkdir -p "$eponymTmpDir/nimble"
printf '[]\n' > "$eponymTmpDir/nimble/packages_official.json"

# Confirm the installed package does not pull its property-testing library
# into user projects. Falsify is test-only and installed explicitly by CI.
packageRequirements=$(NIMBLE_DIR="$eponymTmpDir/nimble" nimble --offline dump |
  sed -n 's/^requires: "\([^"]*\)"/\1/p')
case "$packageRequirements" in
  *"nim >= 2.0.0"*) ;;
  *)
    echo "Nim compiler requirement missing from package metadata: $packageRequirements" >&2
    exit 1
    ;;
esac
case ",$packageRequirements," in
  *,falsify*)
    echo "test-only dependency falsify leaked into package requirements: $packageRequirements" >&2
    exit 1
    ;;
esac

# Exercise a real Nimble install with an empty, isolated package directory.
NIMBLE_DIR="$eponymTmpDir/nimble" nimble --offline install --accept

eponymPackageDir=
for candidate in "$eponymTmpDir"/nimble/pkgs2/eponym-*; do
  if [ -d "$candidate" ]; then
    eponymPackageDir=$candidate
    break
  fi
done
if [ -z "$eponymPackageDir" ]; then
  echo "nimble install did not create an Eponym package directory" >&2
  exit 1
fi

mkdir -p "$eponymTmpDir/project"
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
extractTutorialSnippet dynamic-vec "$eponymTmpDir/project/dynamic_vec.nim"
cat > "$eponymTmpDir/project/lists.nim" <<'EOF'
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/list.ep"
  postulate(Int, Univ)
  runtimeList(List)
  proc keepList(values: List[Int]): List[Int] = values
  proc emptyList(): List[Int] = (nil)

doAssert keepList(@[2, 3, 5]) == @[2, 3, 5]
doAssert emptyList() == @[]
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
EOF
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
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/nimcache" \
  --out:"$eponymTmpDir/test_prelude_resolution" main.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/hello-cache" \
  --out:"$eponymTmpDir/hello" hello.nim
nim c --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/vecs-cache" \
  --out:"$eponymTmpDir/vecs" vecs.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/dynamic-vec-cache" \
  --out:"$eponymTmpDir/dynamic_vec" dynamic_vec.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/lists-cache" \
  --out:"$eponymTmpDir/lists" lists.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/options-cache" \
  --out:"$eponymTmpDir/options" options.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/nat-to-int-cache" \
  --out:"$eponymTmpDir/nat_to_int" nat_to_int.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/debug-cache" \
  --out:"$eponymTmpDir/debug" debug.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/scalars-cache" \
  --out:"$eponymTmpDir/scalars" scalars.nim
