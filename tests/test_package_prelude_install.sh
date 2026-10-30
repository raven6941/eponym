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
extractTutorialSnippet runtime-vec "$eponymTmpDir/project/runtime_vec.nim"
cat > "$eponymTmpDir/project/lists.nim" <<'EOF'
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/list.ep"
  postulate(Int, Univ)
  runtimeType(Int, int)
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
  postulate(Int, Univ)
  runtimeType(Int, int)
  proc keepOption(value: Option[Int]): Option[Int] = value

doAssert keepOption(some(7)) == some(7)
doAssert keepOption(none(int)).isNone
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
  --nimcache:"$eponymTmpDir/runtime-vec-cache" \
  --out:"$eponymTmpDir/runtime_vec" runtime_vec.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/lists-cache" \
  --out:"$eponymTmpDir/lists" lists.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/options-cache" \
  --out:"$eponymTmpDir/options" options.nim
nim c -r --path:"$eponymPackageDir" \
  --nimcache:"$eponymTmpDir/scalars-cache" \
  --out:"$eponymTmpDir/scalars" scalars.nim
