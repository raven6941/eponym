## Runs all .ep examples through the elaborator.
import os
import strutils
import elab

var failed = 0
for kind, path in walkDir("examples"):
  if kind == pcFile and path.endsWith(".ep"):
    let prog = readFile(path)
    # Strip # comments (example headers)
    var lines: seq[string] = @[]
    for line in prog.splitLines():
      if not line.strip().startsWith("#"):
        lines.add(line)
    let src = lines.join("\n")
    try:
      discard elabCheck(src)
      echo "ok: ", path
    except ElabError as e:
      echo "FAIL: ", path, " — ", e.msg
      inc failed

if failed > 0:
  echo failed, " example(s) failed"
  quit(1)
echo "--- all examples elaborated ---"
