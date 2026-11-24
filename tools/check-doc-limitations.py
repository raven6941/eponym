#!/usr/bin/env python3
"""Docs consistency check (issue #573).

A doc that phrases something as a *current* limitation ("... yet, see
issue #NNN") must cite an issue that is still open. Once the issue
closes, the doc is stale: reword the claim as historical or remove it.

Scans examples/README.md, docs/*.md, and examples/embedded/*.nim for
lines carrying both "yet" and an "issue #NNN" reference, then checks
each cited issue's state against the public GitHub API (no auth needed;
this is a public repo). If the API is unreachable, warns and passes so
a network blip never fails CI.
"""
import json
import re
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCOPES = [ROOT / "examples" / "README.md", *sorted((ROOT / "docs").glob("*.md")),
          *sorted((ROOT / "examples" / "embedded").glob("*.nim"))]
PATTERN = re.compile(r"yet\b.*issue #(\d+)|issue #(\d+).*yet\b", re.IGNORECASE)
API = "https://api.github.com/repos/raven6941/eponym/issues/{}"


def cited_issues():
    found = {}
    for path in SCOPES:
        if not path.exists():
            continue
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            m = PATTERN.search(line)
            if m:
                num = int(m.group(1) or m.group(2))
                found.setdefault(num, []).append(f"{path.relative_to(ROOT)}:{lineno}")
    return found


def issue_state(num):
    req = urllib.request.Request(API.format(num), headers={"User-Agent": "eponym-doc-check"})
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.load(resp).get("state")


def main():
    found = cited_issues()
    if not found:
        print("check-doc-limitations: no current-limitation issue references found")
        return 0
    stale = []
    for num, locs in sorted(found.items()):
        try:
            state = issue_state(num)
        except Exception as e:  # noqa: BLE001 - network failure must not fail CI
            print(f"check-doc-limitations: WARNING: could not check issue #{num} ({e}); skipping")
            continue
        print(f"check-doc-limitations: issue #{num} is {state} (cited at {', '.join(locs)})")
        if state == "closed":
            stale.append(num)
    if stale:
        print("check-doc-limitations: FAIL: current-limitation claims cite closed "
              f"issue(s): {', '.join('#' + str(n) for n in stale)}. "
              "Reword as historical or remove the claim.", file=sys.stderr)
        return 1
    print("check-doc-limitations: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
