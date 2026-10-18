#!/usr/bin/env bash
# Build the same static site tree as .github/workflows/pages.yml for local review.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output_dir="${1:-$repo_root/_site}"

cd "$repo_root"
command -v pandoc >/dev/null || { echo "pandoc is required (GitHub Actions uses 3.6)" >&2; exit 1; }
command -v python3 >/dev/null || { echo "python3 is required" >&2; exit 1; }

rm -rf "$output_dir"
mkdir -p "$output_dir"
cp site.css "$output_dir/site.css"

while IFS= read -r -d '' source; do
  case "$source" in
    ./README.md) source="README.md" ;;
    ./*) source="${source#./}" ;;
  esac
  target="${source%.md}.html"
  fragment="${target}.fragment"
  pandoc --from=gfm --to=html5 \
    --metadata title="$(basename "${source%.md}")" \
    -o "$fragment" "$source"
  if grep -Eq '^<p>```|^<h[1-6]>[^<]*</h[1-6]>$' "$fragment" || grep -Fq '```' "$fragment"; then
    rm -f "$fragment"
    echo "Pandoc left Markdown syntax unconverted in $source" >&2
    exit 1
  fi
  python3 tools/wrap_markdown_page.py "$source" "$fragment" "$target" "$output_dir"
  rm "$fragment"
done < <(find . -type f -name '*.md' -not -path './.git/*' -not -path '*/node_modules/*' -print0)

cp robots.txt sitemap.xml "$output_dir/"
printf 'Built local Pages site in %s\n' "$output_dir"
printf 'Open %s/index.html to inspect the home page.\n' "$output_dir"
