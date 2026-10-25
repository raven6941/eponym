## Content-addressed shed proof-state construction and wire transfer.
## This production-facing layer is built on the #450 experimental encoding.

import std/[algorithm, base64, json, strutils, tables]
import sheds
import shed_state_dag
import sha256

type
  ShedProofState* = object
    id*: NodeId
    document*: string
    generatedSources*: Table[string, string]
    sheds*: seq[ShedInfo]
    goalIds*: Table[string, string]
    environment*: string
    nodes*: seq[tuple[id: NodeId, node: MerkleNode]]

proc appendU64(dst: var string, n: uint64) =
  for i in countdown(7, 0): dst.add(char((n shr (i * 8)) and 0xff'u64))

proc appendField(dst: var string, value: string) =
  appendU64(dst, uint64(value.len))
  dst.add(value)

proc decodeFields(payload: string): seq[string] =
  var i = 0
  while i < payload.len:
    if i + 8 > payload.len: raise newException(ValueError, "truncated state field")
    var length = 0'u64
    for j in 0 ..< 8:
      length = (length shl 8) or uint64(byte(payload[i + j]))
    i += 8
    if length > uint64(payload.len - i):
      raise newException(ValueError, "state field exceeds node payload")
    let n = int(length)
    result.add(payload[i ..< i + n])
    i += n

proc addNode(state: var ShedProofState, node: MerkleNode): NodeId =
  result = nodeId(node)
  state.nodes.add((result, node))

proc recordPayload(goalId, blockId: string, shed: ShedInfo): string =
  result = ""
  for field in [goalId, blockId, shed.name, shed.draft,
      $shed.nimLine, $shed.nimCol, $shed.holeLine, $shed.holeCol,
      shed.goal, $shed.status]:
    appendField(result, field)
  appendField(result, $shed.ctx.len)
  for item in shed.ctx: appendField(result, item)
  appendField(result, $shed.goalPi.len)
  for item in shed.goalPi: appendField(result, item)

proc rawGoalRecord(payload: string): MerkleNode =
  MerkleNode(kind: nkGoalRecord, payload: payload)

proc buildShedProofState*(document: string, sheds: seq[ShedInfo],
                          environment, documentUri: string,
                          previousGoalIds: Table[string, string],
                          parentId = "", action = "", targetGoalId = ""):
                          ShedProofState =
  result.document = document
  result.environment = environment & "\0document-uri=" & documentUri
  result.sheds = @[]
  for shed in sheds:
    if shed.status == ssYellow and shed.genSrc.len > 0: result.sheds.add(shed)
  result.generatedSources = initTable[string, string]()
  result.goalIds = initTable[string, string]()

  let documentTree = buildSourceTree(document)
  result.nodes.add(documentTree.nodes)

  var blockLines = initTable[string, int]()
  for shed in sheds:
    if shed.genSrc.len == 0: continue
    if shed.genSrc notin blockLines or shed.nimLine < blockLines[shed.genSrc]:
      blockLines[shed.genSrc] = shed.nimLine
  var blockIds: seq[string] = @[]
  var blockRoots: seq[NodeId] = @[]
  var blockMap = initTable[string, string]()
  for genSrc, firstLine in blockLines:
    let blockId = "block@" & $firstLine
    blockMap[genSrc] = blockId
    result.generatedSources[blockId] = genSrc
    let tree = buildSourceTree(genSrc)
    result.nodes.add(tree.nodes)
    blockIds.add(blockId)
    blockRoots.add(tree.root)
  # Sort source blocks by their stable block identity and keep roots paired.
  var blockPairs: seq[tuple[id: string, root: NodeId]] = @[]
  for i in 0 ..< blockIds.len: blockPairs.add((blockIds[i], blockRoots[i]))
  blockPairs.sort(proc(a, b: tuple[id: string, root: NodeId]): int = cmp(a.id, b.id))
  blockIds.setLen(0); blockRoots.setLen(0)
  for item in blockPairs:
    blockIds.add(item.id); blockRoots.add(item.root)
  let documentRoot = documentTree.root
  let sourceSetRoot = result.addNode(sourceSet(blockIds, blockRoots))

  var records: seq[tuple[goalId: string, node: NodeId]] = @[]
  var childOrdinals = initTable[string, int]()
  var targetName = ""
  for name, id in previousGoalIds:
    if id == targetGoalId: targetName = name
  for shed in sheds:
    if shed.status != ssYellow or shed.genSrc.len == 0: continue
    let blockId = blockMap[shed.genSrc]
    var goalId: string
    if previousGoalIds.hasKey(shed.name) and
       not (targetGoalId.len > 0 and previousGoalIds[shed.name] == targetGoalId):
      goalId = previousGoalIds[shed.name]
    elif parentId.len > 0 and targetGoalId.len > 0 and targetName.len > 0 and
         (shed.name == targetName or shed.name.startsWith(targetName & "_")):
      let ordinal = childOrdinals.getOrDefault(targetGoalId)
      childOrdinals[targetGoalId] = ordinal + 1
      goalId = sha256Hex("eponym.shed.goal-child\0v1\0" & parentId & "\0" &
        action & "\0" & targetGoalId & "\0" & $ordinal)
    else:
      goalId = sha256Hex("eponym.shed.goal-initial\0v1\0" &
        idText(documentTree.root) & "\0" & blockId & "\0" &
        shed.name & "\0" & $shed.nimLine & ":" & $shed.nimCol)
    result.goalIds[shed.name] = goalId
    let record = rawGoalRecord(recordPayload(goalId, blockId, shed))
    records.add((goalId, result.addNode(record)))
  let goalsRoot = result.addNode(goalSet(records))
  let environmentRoot = result.addNode(environment(result.environment))
  result.id = result.addNode(proofState(documentRoot, sourceSetRoot,
                                         goalsRoot, environmentRoot))

proc nodeToJson*(id: NodeId, node: MerkleNode): JsonNode =
  var children = newJArray()
  for child in node.children: children.add(%idText(child))
  %*{"id": idText(id), "kind": $node.kind,
     "payload": encode(node.payload), "children": children,
     "byteLength": node.byteLength}

proc nodeFromJson*(j: JsonNode): tuple[id: NodeId, node: MerkleNode] =
  let id = NodeId(j["id"].getStr())
  let kind = parseEnum[NodeKind](j["kind"].getStr())
  var children: seq[NodeId] = @[]
  for child in j["children"]: children.add(NodeId(child.getStr()))
  let node = MerkleNode(kind: kind, payload: decode(j["payload"].getStr()),
    children: children, byteLength: j["byteLength"].getInt())
  if not verified(id, node):
    raise newException(ValueError, "node hash does not match canonical content")
  (id, node)

proc nodesToJson*(nodes: openArray[tuple[id: NodeId, node: MerkleNode]]): JsonNode =
  result = newJArray()
  for (id, node) in nodes: result.add(nodeToJson(id, node))

proc restoreShedProofState*(cache: var NodeCache, root: NodeId): ShedProofState =
  let rootNode = cache.get(root)
  if rootNode.kind != nkProofState or rootNode.children.len != 4:
    raise newException(ValueError, "invalid shed proof-state root node")
  result.id = root
  result.document = cache.reconstructSource(rootNode.children[0])
  result.generatedSources = initTable[string, string]()
  result.goalIds = initTable[string, string]()
  let sourceIndex = cache.get(rootNode.children[1])
  if sourceIndex.kind != nkSourceSet:
    raise newException(ValueError, "proof state source index is malformed")
  let sourceFields = decodeFields(sourceIndex.payload)
  if sourceFields.len == 0: raise newException(ValueError, "source index has no count")
  let sourceCount = parseInt(sourceFields[0])
  if sourceFields.len != sourceCount + 1 or sourceIndex.children.len != sourceCount:
    raise newException(ValueError, "source index count mismatch")
  for i in 0 ..< sourceCount:
    result.generatedSources[sourceFields[i + 1]] =
      cache.reconstructSource(sourceIndex.children[i])

  let goalIndex = cache.get(rootNode.children[2])
  if goalIndex.kind != nkGoalSet:
    raise newException(ValueError, "proof state goal index is malformed")
  for recordId in goalIndex.children:
    let record = cache.get(recordId)
    if record.kind != nkGoalRecord:
      raise newException(ValueError, "goal index references a non-goal node")
    let fields = decodeFields(record.payload)
    if fields.len < 12: raise newException(ValueError, "goal record is truncated")
    var item = ShedInfo(name: fields[2], draft: fields[3],
      nimLine: parseInt(fields[4]), nimCol: parseInt(fields[5]),
      holeLine: parseInt(fields[6]), holeCol: parseInt(fields[7]),
      goal: fields[8], status: parseEnum[ShedStatus](fields[9]), holeIdx: -1)
    let contextCount = parseInt(fields[10])
    if fields.len < 12 + contextCount:
      raise newException(ValueError, "goal context is truncated")
    for i in 0 ..< contextCount: item.ctx.add(fields[11 + i])
    let goalPiIndex = 11 + contextCount
    let goalPiCount = parseInt(fields[goalPiIndex])
    if fields.len != goalPiIndex + goalPiCount + 1:
      raise newException(ValueError, "goal Pi spine count mismatch")
    for i in 0 ..< goalPiCount: item.goalPi.add(fields[goalPiIndex + 1 + i])
    if fields[1] notin result.generatedSources:
      raise newException(ValueError, "goal references an unknown source block")
    item.genSrc = result.generatedSources[fields[1]]
    result.goalIds[item.name] = fields[0]
    result.sheds.add(item)
  let env = cache.get(rootNode.children[3])
  if env.kind != nkEnvironment:
    raise newException(ValueError, "proof state environment node is malformed")
  result.environment = env.payload

proc stateNodes*(cache: var NodeCache, root: NodeId): seq[tuple[id: NodeId, node: MerkleNode]] =
  var seen = initTable[NodeId, bool]()
  var collected: seq[tuple[id: NodeId, node: MerkleNode]] = @[]
  proc visit(id: NodeId) =
    if seen.hasKey(id): return
    seen[id] = true
    let node = cache.get(id)
    collected.add((id, node))
    for child in node.children: visit(child)
  visit(root)
  result = collected
