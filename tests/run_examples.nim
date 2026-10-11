## Runs all .ep examples through the elaborator.
##
## Directories: lib/, examples/ and examples/ep/ (the Oct 9 reorg moved .ep
## files into examples/ep/; this runner walks all three so the suite is not
## vacuous). Files named `*-neg.ep` are *negative* tests: they must raise
## ElabError.
##
## Issue #114: example files may carry `# import <mod>` header directives.
## Each directive prepends `lib/<mod>.ep` before elaboration, so library
## definitions (e.g. Nat) are shared instead of redefined per file. The
## concatenated source is still one standalone elaboration unit.
import os
import strutils
import elab

proc expandImports(path: string, prog: string): string =
  ## Collect `# import <mod>` directives (in order, deduplicated, transitive)
  ## and return the concatenated `lib/<mod>.ep` sources to prepend.
  var seen: seq[string] = @[]
  proc loadModule(name: string): string =
    ## Source of lib/<name>.ep with its own `# import` directives expanded.
    if name in seen: return ""
    seen.add(name)
    let libFile = "lib" / name & ".ep"
    if not fileExists(libFile):
      echo "FAIL: ", path, " — import '", name, "': ", libFile, " not found"
      quit(1)
    let libSrc = readFile(libFile)
    for line in libSrc.splitLines():
      let s = line.strip()
      if s.startsWith("# import "):
        result.add(loadModule(s[len("# import ")..^1].strip()))
    result.add(libSrc & "\n")
  for line in prog.splitLines():
    let s = line.strip()
    if s.startsWith("# import "):
      result.add(loadModule(s[len("# import ")..^1].strip()))

proc runFile(path: string): bool =
  ## Returns true if the file behaves as expected.
  let prog = readFile(path)
  # Strip # comments (example headers, incl. `# import` directives —
  # those are expanded separately above and never reach the elaborator)
  var lines: seq[string] = @[]
  for line in prog.splitLines():
    if not line.strip().startsWith("#"):
      lines.add(line)
  let src = expandImports(path, prog) & lines.join("\n")
  let neg = path.endsWith("-neg.ep")
  try:
    discard elabCheck(src)
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
