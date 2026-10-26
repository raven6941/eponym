## Issue #430: proof-state action discovery and version-checked submission.
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

proc macroSidecar(generatedSource, name, goal: string,
                  context: seq[string]): ShedInfo =
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
    status: ssYellow, goal: goal, ctx: context, genSrc: generatedSource)

proc openDoc(server: var LspServer, uri, source: string) =
  discard server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didOpen",
    "params": {"textDocument": {"uri": uri, "text": source}}})

proc changeDoc(server: var LspServer, uri, source: string) =
  discard server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didChange",
    "params": {"textDocument": {"uri": uri},
               "contentChanges": [{"text": source}]}})

proc discover(server: var LspServer, uri, shedName: string, id: int): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id,
    "method": "eponym/availableShedActions",
    "params": {"textDocument": {"uri": uri}, "shedName": shedName}})

proc submit(server: var LspServer, uri, shedName: string, version: int,
            actionId: string, arguments: JsonNode, id: int): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id,
    "method": "eponym/submitShedAction",
    "params": {"textDocument": {"uri": uri}, "shedName": shedName,
                "stateVersion": version,
                "action": {"id": actionId, "arguments": arguments}}})

proc action(actions: JsonNode, id: string): JsonNode =
  for item in actions:
    if item["id"].getStr() == id: return item

proc choices(descriptor: JsonNode, argumentName: string): seq[string] =
  for argument in descriptor["arguments"]:
    if argument["name"].getStr() == argumentName:
      for choice in argument["choices"]: result.add(choice.getStr())

proc tempDir(name: string): string =
  result = getTempDir() / ("eponym_shed_discovery_" & name)
  if dirExists(result): removeDir(result)
  createDir(result)

let dir = tempDir("apply")
let file = dir / "demo.nim"
let uri = "file://" & file
let source = "import sheds_mac\nshedsBlock:\n" &
  "  proc identity(n: Int): Int = ![identityBody]\n"
let generated = "postulate(Int, Univ)\n" &
  "proc identity (n : Int) : Int = _\n"
writeFile(file, source)
writeShedSidecar(file, @[macroSidecar(generated, "identityBody", "Int",
                                      @["n : Int"])])
var server = LspServer(documents: initTable[string, string]())
openDoc(server, uri, source)
let sidecarBefore = readFile(sidecarPath(file))
let available = discover(server, uri, "identityBody", 1)
check("error" notin available and
      available["result"]["goal"].getStr() == "Int" and
      "n : Int" in $available["result"]["context"],
  "query returns the current typed goal and context")
let actionList = available["result"]["actions"]
check(not action(actionList, "refine").isNil and
      not action(actionList, "give").isNil and
      not action(actionList, "apply").isNil,
  "freeform actions and a feasible local application are discovered")
check(action(actionList, "construct").isNil and
      action(actionList, "caseSplit").isNil and
      action(actionList, "rewrite").isNil and
      action(actionList, "intro").isNil,
  "inapplicable actions are omitted")
check(choices(action(actionList, "apply"), "candidate") == @["n"],
  "Apply exposes the checked local candidate, not a client-computed guess")
check(readFile(sidecarPath(file)) == sidecarBefore,
  "discovering actions does not mutate the proof sidecar")

# Intro choices report the actual binder and residual goal for each count.
let introDir = tempDir("intro")
let introFile = introDir / "intro.nim"
let introUri = "file://" & introFile
let introSource = "import sheds_mac\nshedsBlock:\n" &
  "  proc mapper(f: Int): Int = ![mapperBody]\n"
let introGenerated = "postulate(Int, Univ)\n" &
  "proc mapper (f : Int) : Pi(x: Int, Int) = _\n"
writeFile(introFile, introSource)
writeShedSidecar(introFile, @[macroSidecar(introGenerated,
  "mapperBody", "Pi(x: Int, Int)", @[])])
var introServer = LspServer(documents: initTable[string, string]())
openDoc(introServer, introUri, introSource)
let introQuery = discover(introServer, introUri, "mapperBody", 7)
let introAction = action(introQuery["result"]["actions"], "intro")
check(not introAction.isNil and
      introAction["expectedSubgoals"]["choices"]["1"]["binders"][0]["name"].getStr() == "x" and
      introAction["expectedSubgoals"]["choices"]["1"]["goal"].getStr() == "Int",
  "Intro discovery returns the chosen binder type and residual goal")

let version = available["result"]["stateVersion"].getInt()
let extraArgument = submit(server, uri, "identityBody", version, "apply",
                           %*{"candidate": "n", "ignored": true}, 8)
check("error" in extraArgument,
  "submission rejects arguments outside the queried schema")
let applied = submit(server, uri, "identityBody", version, "apply",
                     %*{"candidate": "n"}, 2)
check("error" notin applied and
      applied["result"]["action"]["id"].getStr() == "apply" and
      applied["result"]["edit"]["term"].getStr() == "n" and
      applied["result"]["validation"]["accepted"].getBool(),
  "submission rechecks the discovered candidate through the semantic layer")
let replay = submit(server, uri, "identityBody", version, "apply",
                    %*{"candidate": "n"}, 3)
check("error" in replay,
  "a proof-state version cannot be replayed after an accepted action")

# An edit between query and submission must invalidate the exact version.
let staleDir = tempDir("stale")
let staleFile = staleDir / "demo.nim"
let staleUri = "file://" & staleFile
writeFile(staleFile, source)
writeShedSidecar(staleFile, @[macroSidecar(generated, "identityBody", "Int",
                                           @["n : Int"])])
var staleServer = LspServer(documents: initTable[string, string]())
openDoc(staleServer, staleUri, source)
let staleQuery = discover(staleServer, staleUri, "identityBody", 4)
changeDoc(staleServer, staleUri, source & "# edit\n")
let staleSubmit = submit(staleServer, staleUri, "identityBody",
  staleQuery["result"]["stateVersion"].getInt(), "refine",
  %*{"term": "n"}, 5)
check("error" in staleSubmit and
      "changed since" in staleSubmit["error"]["message"].getStr(),
  "submission rejects a proof state edited after discovery")

# The indexed constructor picker must retain elaborator feasibility checks.
let natPath = (getCurrentDir() / "lib/nat.ep").replace("\\", "/")
let vecPath = (getCurrentDir() / "lib/vec.ep").replace("\\", "/")
let vecDir = tempDir("indexed")
let vecFile = vecDir / "vec.nim"
let vecUri = "file://" & vecFile
let vecSource = "import sheds_mac\nshedsBlock:\n" &
  "  proc makeVec(n: Nat): Vec[Nat, suc(n)] = ![makeVecBody]\n"
let vecGenerated = "import \"" & natPath & "\"\nimport \"" & vecPath &
  "\"\nproc earlier (n : Nat) : Nat = _\n" &
  "proc makeVec (n : Nat) : Vec Nat (suc n) = _\n"
writeFile(vecFile, vecSource)
var vecShed = macroSidecar(vecGenerated, "makeVecBody",
  "Vec Nat (suc n)", @["n : Nat"])
var generatedLine = 0
for line in vecGenerated.splitLines():
  if line.startsWith("proc makeVec"):
    vecShed.holeLine = generatedLine + 1
    vecShed.holeCol = line.find('_') + 1
  inc generatedLine
writeShedSidecar(vecFile, @[vecShed])
var vecServer = LspServer(documents: initTable[string, string]())
openDoc(vecServer, vecUri, vecSource)
let vecSidecarBefore = readFile(sidecarPath(vecFile))
let vecQuery = discover(vecServer, vecUri, "makeVecBody", 6)
check(readFile(sidecarPath(vecFile)) == vecSidecarBefore,
  "indexed action discovery leaves the sidecar unchanged")
check("error" notin vecQuery and
      choices(action(vecQuery["result"]["actions"], "construct"),
              "constructor") == @["cons"],
  "constructor discovery omits nil because its index cannot fit Vec[Nat, suc(n)]")
let constructAction = action(vecQuery["result"]["actions"], "construct")
if not constructAction.isNil:
  let fields = constructAction["expectedSubgoals"]["choices"]["cons"]
  check(fields.len == 4 and fields[0]["goal"].getStr().len > 0,
    "constructor discovery includes checked typed field-goal shapes")
let splitChoices = choices(action(vecQuery["result"]["actions"], "caseSplit"),
                           "variable")
check("n" in splitChoices,
  "case-split choices come from the typed context")
let splitShape = action(vecQuery["result"]["actions"], "caseSplit")
if not splitShape.isNil:
  let byChoice = splitShape["expectedSubgoals"]["byChoice"]["n"]
  check(byChoice.len == 2 and
        byChoice[0]["name"].getStr().startsWith("makeVecBody"),
    "case-split subgoal metadata describes only the selected shed's branches")
check(action(vecQuery["result"]["actions"], "rewrite").isNil,
  "rewrite is omitted when no equality proof can apply")

removeDir(dir)
removeDir(staleDir)
removeDir(vecDir)
if failures > 0:
  echo failures, " FAILURES"
  quit(1)
echo "all semantic shed action discovery tests passed"
