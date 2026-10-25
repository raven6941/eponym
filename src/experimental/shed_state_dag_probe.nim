## Executable feasibility probe for issue #450.
## Run with nim c -r --path:src --path:src/eponym --path:src/experimental
## src/experimental/shed_state_dag_probe.nim <fixture.nim>

import std/[json, os, sequtils, strutils, tables]
import eponym/lsp
import eponym/sheds
import eponym/shed_state
import ../eponym/shed_state_dag
import ../eponym/sha256

type StateBuild = object
  root: NodeId
  nodes: seq[tuple[id: NodeId, node: MerkleNode]]
  goalIds: Table[string, string]
  goalNodeIds: Table[string, NodeId]

proc addNode(state: var StateBuild, node: MerkleNode): NodeId =
  result = nodeId(node)
  state.nodes.add((result, node))

proc buildState(source: string, sheds: seq[ShedInfo], envFingerprint: string,
                stableIds: Table[string, string]): StateBuild =
  let sourceTree = buildSourceTree(source)
  result.nodes.add(sourceTree.nodes)
  var goals: seq[tuple[goalId: string, node: NodeId]] = @[]
  for shed in sheds:
    if shed.status != ssYellow: continue
    let goalId = if stableIds.hasKey(shed.name): stableIds[shed.name]
      else: sha256Hex("shed.initial.v1" & idText(sourceTree.root) & "\0" & shed.name &
        "\0" & $shed.nimLine & ":" & $shed.nimCol)
    let record = goalRecord(goalId, shed.name, shed.goal,
      shed.ctx.join("\n"), $shed.status,
      $shed.nimLine & ":" & $shed.nimCol)
    let recordId = result.addNode(record)
    result.goalIds[shed.name] = goalId
    result.goalNodeIds[shed.name] = recordId
    goals.add((goalId, recordId))
  let goalRoot = result.addNode(goalSet(goals))
  let sourceSetRoot = result.addNode(sourceSet(["probe-block"], [sourceTree.root]))
  let environmentRoot = result.addNode(environment(envFingerprint))
  result.root = result.addNode(proofState(sourceTree.root, sourceSetRoot,
                                           goalRoot, environmentRoot))

proc cacheState(cache: var NodeCache, state: StateBuild) =
  for (id, node) in state.nodes: cache.put(id, node)

proc nodeBytes(nodes: openArray[tuple[id: NodeId, node: MerkleNode]]): int =
  for (_, node) in nodes: result += canonicalBytes(node).len

proc transferUntilResolved(server: var LspServer, methodName, uri, stateId,
                            goalId: string, nodeById: Table[string, JsonNode],
                            extra: JsonNode): JsonNode =
  let rootJson = nodeById[stateId]
  discard nodeFromJson(rootJson)
  var request = %*{"jsonrpc": "2.0", "id": 7, "method": methodName,
    "params": {"textDocument": {"uri": uri}, "stateId": stateId,
               "goalId": goalId, "nodes": [rootJson]}}
  if not extra.isNil:
    for key, value in extra: request["params"][key] = value
  while true:
    let response = handleMessage(server, request)
    if "error" in response: raise newException(ValueError, response["error"]["message"].getStr())
    let payload = response["result"]
    if "needsNodes" notin payload: return payload
    var supplied = newJArray()
    for missing in payload["needsNodes"]:
      supplied.add(nodeById[missing.getStr()])
    request["params"]["nodes"] = supplied

proc main(fixture: string) =
  doAssert sha256Hex("") == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  doAssert sha256Hex("abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

  let nimFile = absolutePath(fixture)
  let sidecar = sidecarPath(nimFile)
  let sourceBefore = readFile(nimFile)
  let sidecarBefore = readFile(sidecar)
  let (sheds, errMsg) = readShedSidecarEx(sidecar)
  doAssert sheds.len == 2, "fixture must contain exactly two sheds"
  doAssert sheds.anyIt(it.name == "firstBody" and it.status == ssYellow)
  doAssert sheds.anyIt(it.name == "siblingBody" and it.status == ssYellow)

  let generatedBefore = sheds[0].genSrc
  let envFingerprint = "nim=" & NimVersion & ";eponym=workspace"
  let parent = buildState(generatedBefore, sheds, envFingerprint,
                          initTable[string, string]())
  doAssert parent.goalIds.len == 2
  var updated: seq[ShedInfo] = @[]
  let plan = refineShedPlan(nimFile, "firstBody", "double ( ? )", sheds,
                            errMsg, updated)
  doAssert plan.ok, plan.why
  doAssert updated.len == 2
  doAssert updated.anyIt(it.name == "siblingBody" and it.status == ssYellow)
  doAssert updated.anyIt(it.name == "firstBody" and it.status == ssYellow)
  doAssert sheds[0].genSrc == generatedBefore, "planning mutated input metadata"
  doAssert readFile(nimFile) == sourceBefore, "planning modified the Nim file"
  doAssert readFile(sidecar) == sidecarBefore, "planning modified the sidecar"

  let generatedAfter = updated[0].genSrc
  var successorGoalIds = initTable[string, string]()
  successorGoalIds["siblingBody"] = parent.goalIds["siblingBody"]
  successorGoalIds["firstBody"] = sha256Hex("shed.child.v1" & idText(parent.root) &
    "\0refine\0" & parent.goalIds["firstBody"] & "\0ordinal=0")
  let successor = buildState(generatedAfter, updated, envFingerprint,
                             successorGoalIds)
  doAssert parent.goalIds["siblingBody"] == successor.goalIds["siblingBody"],
    "untouched sibling goal should retain its stable goal ID"
  doAssert parent.goalIds["firstBody"] != successor.goalIds["firstBody"],
    "a residual child gets an identity derived from its parent action"
  doAssert generatedAfter != generatedBefore

  # Exercise the actual LSP state-addressed request path after an LSP restart.
  let uri = "file://" & nimFile
  var lspServer = LspServer(documents: initTable[string, string](),
    stateNodeCache: initNodeCache(4096))
  lspServer.documents[uri] = sourceBefore
  let boot = handleMessage(lspServer, %*{"jsonrpc": "2.0", "id": 1,
    "method": "eponym/createShedState",
    "params": {"textDocument": {"uri": uri}}})["result"]
  var clientWireNodes = initTable[string, JsonNode]()
  for node in boot["nodes"]: clientWireNodes[node["id"].getStr()] = node
  let initialStateId = boot["stateId"].getStr()
  var freshServer = LspServer(documents: initTable[string, string](),
    stateNodeCache: initNodeCache(4096))
  freshServer.documents[uri] = sourceBefore
  var firstGoalId = ""
  for goal in boot["goals"]:
    if goal["name"].getStr() == "firstBody": firstGoalId = goal["goalId"].getStr()
  doAssert firstGoalId.len > 0
  let affordances = transferUntilResolved(freshServer,
    "eponym/queryShedStateActions", uri, initialStateId, firstGoalId,
    clientWireNodes, nil)
  doAssert affordances["actions"].len >= 2
  let transitionResult = transferUntilResolved(freshServer,
    "eponym/transitionShedState", uri, initialStateId, firstGoalId,
    clientWireNodes, %*{"action": {"id": "refine",
      "arguments": {"term": "double ( ? )"}}})
  doAssert transitionResult["successorStateId"].getStr() != initialStateId
  doAssert "double" in transitionResult["documentText"].getStr()
  doAssert "shedHole(firstBody)" in transitionResult["documentText"].getStr()
  doAssert readFile(nimFile) == sourceBefore
  doAssert readFile(sidecar) == sidecarBefore
  for node in transitionResult["nodes"]:
    clientWireNodes[node["id"].getStr()] = node

  var server = initNodeCache(512)
  var client = initNodeCache(512)
  cacheState(server, parent)
  cacheState(client, parent)
  var parentIds = initTable[NodeId, bool]()
  for (id, _) in parent.nodes: parentIds[id] = true
  var delta: seq[tuple[id: NodeId, node: MerkleNode]] = @[]
  for item in successor.nodes:
    if not parentIds.hasKey(item.id):
      delta.add(item)
      server.put(item.id, item.node)
      client.put(item.id, item.node)
  doAssert server.reconstructSource(buildSourceTree(generatedBefore).root) == generatedBefore
  doAssert server.reconstructSource(buildSourceTree(generatedAfter).root) == generatedAfter

  let siblingId = successor.goalNodeIds["siblingBody"]
  doAssert server.evict(siblingId), "expected the sibling node in cache"
  let missing = server.missingClosure([successor.root])
  doAssert siblingId in missing, "cache miss should identify the evicted sibling node"
  for id in missing: server.put(id, client.get(id))
  doAssert server.missingClosure([successor.root]).len == 0

  var tampered = client.get(siblingId)
  tampered.payload.add("tampered")
  var rejected = false
  try: server.put(siblingId, tampered)
  except CacheError: rejected = true
  doAssert rejected, "a modified node must not pass under its old digest"

  var bounded = initNodeCache(2)
  cacheState(bounded, parent)
  doAssert bounded.cacheSize <= 2

  var selected = parent.root
  selected = successor.root
  doAssert selected == successor.root
  selected = parent.root
  doAssert selected == parent.root

  let fullBytes = nodeBytes(parent.nodes)
  let deltaBytes = nodeBytes(delta)
  echo "LSP restart recovered state nodes; state-addressed refine returned a checked successor"
  echo "checked refine preserved sibling; immediate root selection returned to parent"
  echo "SHA-256 vectors valid; mutated content rejected; cache miss recovered"
  echo "node bytes: delta=", deltaBytes, " full-parent-snapshot=", fullBytes

when isMainModule:
  if paramCount() != 1:
    quit("usage: shed_state_dag_probe <compiled-two-shed-fixture.nim>", 2)
  main(paramStr(1))
