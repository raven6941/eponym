## Issue #429: structured, checked shed actions with explicit undo/replay.
import json
import os
import strutils
import tables
import lsp
import sheds

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

proc opened(server: var LspServer, uri, text: string) =
  discard server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didOpen",
    "params": {"textDocument": {"uri": uri, "text": text}}})

proc changed(server: var LspServer, uri, text: string) =
  discard server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didChange",
    "params": {"textDocument": {"uri": uri},
               "contentChanges": [{"text": text}]}})

proc macroSidecar(nimFile, generatedSource, name: string,
                  goal, context: string): ShedInfo =
  let lines = generatedSource.splitLines()
  var holeLine = 0
  var holeCol = 0
  for i, line in lines:
    let col = line.find('_')
    if col >= 0:
      holeLine = i + 1
      holeCol = col + 1
      break
  result = ShedInfo(name: name, draft: "", nimLine: 3, nimCol: 33,
    holeLine: holeLine, holeCol: holeCol, holeIdx: 0,
    status: ssYellow, goal: goal, ctx: @[context], genSrc: generatedSource)

proc actionRequest(server: var LspServer, uri, kind, shedName: string,
                   args: JsonNode, id: int): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "eponym/performShedAction",
    "params": {"textDocument": {"uri": uri},
               "action": {"kind": kind, "target": shedName,
                          "arguments": args}}})

proc commitRequest(server: var LspServer, uri: string, transitionId, id: int): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "eponym/commitShedAction",
    "params": {"textDocument": {"uri": uri}, "transitionId": transitionId}})

proc fixtureDir(name: string): string =
  result = getTempDir() / ("eponym_shed_history_" & name)
  if dirExists(result): removeDir(result)
  createDir(result)

let dir = fixtureDir("refine")
let nimFile = dir / "demo.nim"
let uri = "file://" & nimFile
let source0 = "import eponym_mac\neponymBlock:\n  proc identity(n: Int): Int = ![identityBody]\n"
let generated0 = "postulate(Int, Univ)\nproc identity (n : Int) : Int = _\n"
writeFile(nimFile, source0)
writeShedSidecar(nimFile, @[macroSidecar(nimFile, generated0,
  "identityBody", "Int", "n : Int")])
var server = LspServer(documents: initTable[string, string]())
opened(server, uri, source0)

let action = actionRequest(server, uri, "refine", "identityBody",
  %*{"term": "n"}, 1)
check("error" notin action and
      action["result"]["action"]["kind"].getStr() == "refine" and
      action["result"]["action"]["arguments"]["term"].getStr() == "n" and
      action["result"]["validation"]["accepted"].getBool(),
  "Refine returns a structured checker-accepted transition")
let first = action["result"]
let transitionId = first["id"].getInt()
let source1 = source0.replace("![identityBody]", first["edit"]["term"].getStr())
writeFile(nimFile, source1)
changed(server, uri, source1)
let committed = commitRequest(server, uri, transitionId, 2)
check("error" notin committed and
      committed["result"]["validation"]["accepted"].getBool(),
  "transition commits after the edited source and checked sidecar agree")

let historyReq = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 3, "method": "eponym/shedActionHistory",
  "params": {"textDocument": {"uri": uri}}})
check(historyReq["result"]["cursor"].getInt() == 1 and
      historyReq["result"]["canUndo"].getBool() and
      not historyReq["result"]["canRedo"].getBool() and
      historyReq["result"]["transitions"].len == 1 and
      historyReq["result"]["transitions"][0]["applied"].getBool(),
  "history exposes the committed transition and cursor")

let undo = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 4, "method": "eponym/undoShedAction",
  "params": {"textDocument": {"uri": uri}}})
check("error" notin undo and
      undo["result"]["transitionId"].getInt() == transitionId and
      undo["result"]["transition"]["action"]["kind"].getStr() == "refine",
  "undo returns a guarded semantic transition without projecting source")
writeFile(nimFile, source0)
changed(server, uri, source0)
let beforeAgain = macroSidecar(nimFile, generated0,
  "identityBody", "Int", "n : Int")
writeShedSidecar(nimFile, @[beforeAgain])
let commitUndo = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 5, "method": "eponym/commitShedHistoryMove",
  "params": {"textDocument": {"uri": uri}, "transitionId": transitionId,
              "direction": "undo"}})
check("error" notin commitUndo and commitUndo["result"]["cursor"].getInt() == 0,
  "undo commits only after recompiling the restored proof state")
check(commitUndo["result"]["canRedo"].getBool(),
  "history reports redo available after a validated undo")

let redo = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 6, "method": "eponym/redoShedAction",
  "params": {"textDocument": {"uri": uri}}})
check("error" notin redo and
      redo["result"]["id"].getInt() == transitionId and
      redo["result"]["edit"]["term"].getStr() == "n",
  "redo replays the recorded action through the checker")
let source2 = source0.replace("![identityBody]", redo["result"]["edit"]["term"].getStr())
writeFile(nimFile, source2)
changed(server, uri, source2)
let commitRedo = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 7, "method": "eponym/commitShedHistoryMove",
  "params": {"textDocument": {"uri": uri}, "transitionId": transitionId,
              "direction": "redo"}})
check("error" notin commitRedo and commitRedo["result"]["cursor"].getInt() == 1,
  "redo advances history only after the replayed source recompiles")
check(commitRedo["result"]["canUndo"].getBool() and
      not commitRedo["result"]["canRedo"].getBool(),
  "history reports the cursor after a validated redo")

let changedText = source2 & "# user edit\n"
writeFile(nimFile, changedText)
changed(server, uri, changedText)
let staleUndo = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 9, "method": "eponym/undoShedAction",
  "params": {"textDocument": {"uri": uri}}})
check("error" in staleUndo and "changed since" in staleUndo["error"]["message"].getStr(),
  "undo rejects a stale document instead of overwriting user edits")
let staleHistory = server.inspectShedActionHistory(uri)
check(not staleHistory["canUndo"].getBool(),
  "history marks stale transitions as unavailable for undo")

# Give shares the same action envelope and uses complete-proof validation.
let giveDir = fixtureDir("give")
let giveFile = giveDir / "demo.nim"
let giveUri = "file://" & giveFile
let giveSource = "import eponym_mac\neponymBlock:\n  proc identity(n: Int): Int = ![giveBody]\n"
let giveGenerated = "postulate(Int, Univ)\nproc identity (n : Int) : Int = _\n"
writeFile(giveFile, giveSource)
writeShedSidecar(giveFile, @[macroSidecar(giveFile, giveGenerated,
  "giveBody", "Int", "n : Int")])
opened(server, giveUri, giveSource)
let give = actionRequest(server, giveUri, "give", "giveBody",
  %*{"term": "n"}, 10)
check("error" notin give and
      give["result"]["action"]["kind"].getStr() == "give" and
      give["result"]["validation"]["status"].getStr() == "white",
  "Give uses the shared transition envelope and complete checking")

# Case-split returns the same transition shape, with its variable as arguments.
let splitDir = fixtureDir("case_split")
let splitFile = splitDir / "demo.nim"
let splitUri = "file://" & splitFile
let natPath = (getCurrentDir() / "lib/nat.ep").replace("\\", "/")
let boolPath = (getCurrentDir() / "lib/bool.ep").replace("\\", "/")
let splitSource = "import eponym_mac\neponymBlock:\n  proc isZero(n: Nat): Bool = ![isZeroBody]\n"
let splitGenerated = "import \"" & natPath & "\"\nimport \"" & boolPath &
  "\"\nproc isZero (n : Nat) : Bool = _\n"
writeFile(splitFile, splitSource)
writeShedSidecar(splitFile, @[macroSidecar(splitFile, splitGenerated,
  "isZeroBody", "Bool", "n : Nat")])
opened(server, splitUri, splitSource)
let split = actionRequest(server, splitUri, "caseSplit", "isZeroBody",
  %*{"variable": "n"}, 11)
check("error" notin split and
      split["result"]["action"]["kind"].getStr() == "caseSplit" and
      split["result"]["action"]["arguments"]["variable"].getStr() == "n" and
      split["result"]["subSheds"].len == 2 and
      split["result"]["after"]["goals"].len == 2 and
      "n : Nat" in $split["result"]["after"]["goals"][0]["context"] and
      split["result"]["validation"]["accepted"].getBool(),
  "Case-split uses the shared transition envelope with typed subgoals")

removeDir(dir)
removeDir(giveDir)
removeDir(splitDir)
if failures > 0:
  echo failures, " FAILURES"
  quit(1)
echo "all semantic shed action history tests passed"
