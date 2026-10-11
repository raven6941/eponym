## Runs all .ep examples through the elaborator.
##
## Issue #49: each file is elaborated with `elabCheckFile`, so real `import`
## declarations are exercised — imports resolve relative to the importing
## file and merge into one environment per driver. (The Oct 9 reorg moved
## .ep files into examples/ep/; this runner walks all three directories so
## the suite is not vacuous.) Files named `*-neg.ep` are *negative* tests:
## they must raise ElabError.
import os
import strutils
import elab

proc runFile(path: string): bool =
  ## Returns true if the file behaves as expected.
  let neg = path.endsWith("-neg.ep")
  try:
    discard elabCheckFile(path)
    if neg:
      echo "FAIL: ", path, " — expected ElabError, elaborated cleanly"
      return false
    echo "ok: ", path
  except ElabError as e:
    if neg:
      echo "ok (rejected as expected): ", path, " — ", e.msg.splitLines()[0]
    else:
      echo "FAIL: ", path, " — ", e.msg
      return false
  return true

var failed = 0
for dir in ["lib", "examples", "examples/ep"]:
  for kind, path in walkDir(dir):
    if kind == pcFile and path.endsWith(".ep"):
      if not runFile(path):
        inc failed

if failed > 0:
  echo failed, " example(s) failed"
  quit(1)
echo "--- all examples elaborated ---"
