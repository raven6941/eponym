## Integration probe for all state-addressed shed actions (#451).
## Compile its fixture first, then run this probe with that fixture path.
import std/[json, os, tables]
import eponym/lsp
import eponym/sheds
import ../eponym/shed_state_dag

type ClientNodes = Table[string, JsonNode]

proc stateRequest(server: var LspServer, nodes: var ClientNodes, methodName,
                  uri, stateId, goalId: string, extra: JsonNode): JsonNode =
  var request = %*{"jsonrpc": "2.0", "id": 9, "method": methodName,
    "params": {"textDocument": {"uri": uri}, "stateId": stateId,
               "goalId": goalId, "nodes": [nodes[stateId]]}}
  if not extra.isNil:
    for key, value in extra: request["params"][key] = value
  while true:
    let response = handleMessage(server, request)
    if "error" in response:
      raise newException(ValueError, response["error"]["message"].getStr())
    let body = response["result"]
    if "needsNodes" notin body:
      if "nodes" in body:
        for node in body["nodes"]: nodes[node["id"].getStr()] = node
      return body
    var supplied = newJArray()
    for id in body["needsNodes"]:
      let key = id.getStr()
      if key notin nodes: raise newException(ValueError, "client lacks node " & key)
      supplied.add(nodes[key])
    request["params"]["nodes"] = supplied

proc main(fixture: string) =
  let nimFile = absolutePath(fixture)
  let sidecar = sidecarPath(nimFile)
  let sourceBefore = readFile(nimFile)
  let sidecarBefore = readFile(sidecar)
  let uri = "file://" & nimFile
  var server = LspServer(documents: initTable[string, string](),
    stateNodeCache: initNodeCache(4096))
  server.documents[uri] = sourceBefore
  let bootResponse = handleMessage(server, %*{"jsonrpc": "2.0", "id": 1,
    "method": "eponym/createShedState",
    "params": {"textDocument": {"uri": uri}}})
  if "error" in bootResponse: raise newException(ValueError, bootResponse["error"]["message"].getStr())
  let boot = bootResponse["result"]
  let root = boot["stateId"].getStr()
  var nodes = initTable[string, JsonNode]()
  var goalIds = initTable[string, string]()
  for node in boot["nodes"]: nodes[node["id"].getStr()] = node
  for goal in boot["goals"]: goalIds[goal["name"].getStr()] = goal["goalId"].getStr()

  let initialGoal = goalIds["refineGoal"]
  let initialLayout = stateRequest(server, nodes, "eponym/shedStateLayout",
    uri, root, initialGoal, nil)
  doAssert initialLayout["box"]["holeIds"].len > 0,
    "restored yellow state should render its checked hole"

  let cases = [
    ("refine", "refineGoal", %*{"term": "add ( ? ) ( ? )"}),
    ("give", "giveGoal", %*{"term": "x"}),
    ("intro", "introGoal", %*{"count": 1}),
    ("construct", "constructGoal", newJObject()),
    ("apply", "applyGoal", newJObject()),
    ("caseSplit", "caseGoal", %*{"variable": "n"}),
    ("rewrite", "rewriteGoal", newJObject()),
  ]
  for (actionId, goalName, requestedArgs) in cases:
    if goalName notin goalIds: raise newException(ValueError, "missing fixture goal " & goalName)
    let goalId = goalIds[goalName]
    let queried = stateRequest(server, nodes, "eponym/queryShedStateActions",
      uri, root, goalId, nil)
    var descriptor: JsonNode
    for action in queried["actions"]:
      if action["id"].getStr() == actionId: descriptor = action
    if descriptor.isNil: raise newException(ValueError, "action unavailable: " & actionId)
    var args = requestedArgs
    if actionId in ["construct", "apply", "rewrite"]:
      let choices = descriptor["arguments"][0]["choices"]
      if choices.len == 0: raise newException(ValueError, "action has no choices: " & actionId)
      let argumentName = descriptor["arguments"][0]["name"].getStr()
      args[argumentName] = choices[0]
    let transitioned = stateRequest(server, nodes, "eponym/transitionShedState",
      uri, root, goalId, %*{"action": {"id": actionId, "arguments": args}})
    let successorRoot = transitioned["successorStateId"].getStr()
    if successorRoot == root:
      raise newException(ValueError, "action returned its parent root: " & actionId)
    if actionId == "refine":
      echo "refine document: ", transitioned["documentText"].getStr()
      # A goal is actionable through any immutable state that contains it.
      # Completing it removes it from the successor's open-goal set, while
      # the parent still supports a separate hypothetical branch.
      let parentStillOpen = stateRequest(server, nodes,
        "eponym/queryShedStateActions", uri, root, goalId, nil)
      doAssert parentStillOpen["goalId"].getStr() == goalId
      let alternate = stateRequest(server, nodes,
        "eponym/transitionShedState", uri, root, goalId,
        %*{"action": {"id": "refine", "arguments": {"term": "x"}}})
      let alternateRoot = alternate["successorStateId"].getStr()
      doAssert alternateRoot != root and alternateRoot != successorRoot,
        "same parent should support an independent alternate successor"
      var targetStillOpen = false
      for goal in alternate["goals"]:
        if goal["goalId"].getStr() == goalId: targetStillOpen = true
      doAssert not targetStillOpen,
        "a completed goal must leave the successor's open-goal set"
      var closedGoalRejected = false
      try:
        discard stateRequest(server, nodes, "eponym/queryShedStateActions",
          uri, successorRoot, goalId, nil)
      except ValueError as e:
        closedGoalRejected = e.msg == "unknown goal ID in this proof state"
      doAssert closedGoalRejected,
        "a closed goal ID must not be actionable in its completed successor"

      var residualGoalId = ""
      for goal in transitioned["goals"]:
        residualGoalId = goal["goalId"].getStr()
        break
      if residualGoalId.len == 0:
        raise newException(ValueError, "refine did not preserve residual goals")
      let childLayout = stateRequest(server, nodes, "eponym/shedStateLayout",
        uri, successorRoot, residualGoalId, nil)
      doAssert childLayout["box"]["holeIds"].len > 0,
        "restored residual shedHole should render as an open goal"
      let childActions = stateRequest(server, nodes,
        "eponym/queryShedStateActions", uri, successorRoot, residualGoalId, nil)
      var hasGive = false
      for action in childActions["actions"]:
        if action["id"].getStr() == "give": hasGive = true
      if not hasGive: raise newException(ValueError, "successor root was not queryable")
      let childTransition = stateRequest(server, nodes,
        "eponym/transitionShedState", uri, successorRoot, residualGoalId,
        %*{"action": {"id": "give", "arguments": {"term": "x"}}})
      if childTransition["successorStateId"].getStr() == successorRoot:
        raise newException(ValueError, "successor state could not be advanced")
      echo "continued from the refine successor while retaining its parent root"
    echo actionId, " checked -> ", successorRoot

  doAssert readFile(nimFile) == sourceBefore, "state transitions modified the fixture"
  doAssert readFile(sidecar) == sidecarBefore, "state transitions modified the sidecar"
  echo "all seven actions returned checked successor states without disk writes"

when isMainModule:
  if paramCount() != 1: quit("usage: shed_state_actions_probe <fixture.nim>", 2)
  main(paramStr(1))
