import os
import strutils
import elab

let dir = getTempDir() / "eponym-imported-source-locations"
if dirExists(dir): removeDir(dir)
createDir(dir)
let imported = dir / "bad.ep"
let client = dir / "client.ep"
writeFile(imported, "postulate(Nat, Univ)\nproc bad : Nat = missingName\n")
writeFile(client, "import \"bad.ep\"\nproc client : Nat = zero\n")

try:
  discard elabCheckFile(client)
  doAssert false, "expected the imported definition to fail"
except ElabError as e:
  doAssert e.msg.startsWith(e.loc.source & ":line 2, col 18: "), e.msg
  doAssert e.loc.source.endsWith("/bad.ep"), e.loc.source
  doAssert "unbound variable 'missingName'" in e.msg, e.msg

writeFile(imported, "postulate(Nat, Univ)\nproc bad : Nat =\n")
try:
  discard elabCheckFile(client)
  doAssert false, "expected the imported syntax to fail"
except ElabError as e:
  doAssert e.msg.startsWith(e.loc.source & ":line 3, col 1: "), e.msg
  doAssert e.loc.source.endsWith("/bad.ep"), e.loc.source

removeDir(dir)
echo "ok: imported diagnostics retain source file and position"
