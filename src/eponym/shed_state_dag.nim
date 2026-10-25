## Prototype canonical Merkle DAG and bounded node cache for shed proof states.
## This module is intentionally experimental until #450 establishes the format.

import std/[algorithm, hashes, tables]
import sha256

type
  NodeId* = distinct string
  NodeKind* = enum
    nkSourceLeaf, nkSourceBranch, nkSourceSet, nkGoalRecord, nkGoalSet,
    nkEnvironment, nkProofState, nkTransition
  MerkleNode* = object
    kind*: NodeKind
    payload*: string
    children*: seq[NodeId]
    byteLength*: int
  NodeCache* = object
    nodes: Table[NodeId, MerkleNode]
    lru: seq[NodeId]
    maxNodes*: int
  CacheError* = object of CatchableError

const
  NodeDomain = "eponym.shed.node\0v1\0"
  SourceChunkBytes* = 64

proc idText*(id: NodeId): string = string(id)
proc `==`*(a, b: NodeId): bool {.borrow.}
proc hash*(id: NodeId): Hash {.borrow.}

proc appendU64(dst: var string, n: uint64) =
  for i in countdown(7, 0):
    dst.add(char((n shr (i * 8)) and 0xff'u64))

proc appendField(dst: var string, value: string) =
  dst.appendU64(uint64(value.len))
  dst.add(value)

proc canonicalBytes*(node: MerkleNode): string =
  result = NodeDomain
  result.add(char(ord(node.kind)))
  appendField(result, node.payload)
  appendU64(result, uint64(node.byteLength))
  appendU64(result, uint64(node.children.len))
  for child in node.children:
    appendField(result, idText(child))

proc nodeId*(node: MerkleNode): NodeId =
  NodeId(sha256Hex(canonicalBytes(node)))

proc verified*(id: NodeId, node: MerkleNode): bool = nodeId(node) == id

proc leaf*(bytes: string): MerkleNode =
  MerkleNode(kind: nkSourceLeaf, payload: bytes, byteLength: bytes.len)

proc branch*(left, right: NodeId, leftBytes, rightBytes: int): MerkleNode =
  MerkleNode(kind: nkSourceBranch, children: @[left, right],
    byteLength: leftBytes + rightBytes)

proc goalRecord*(goalId, displayName, goal, context, status, sourceAnchor: string): MerkleNode =
  var payload = ""
  for field in [goalId, displayName, goal, context, status, sourceAnchor]:
    appendField(payload, field)
  MerkleNode(kind: nkGoalRecord, payload: payload)

proc goalSet*(records: openArray[tuple[goalId: string, node: NodeId]]): MerkleNode =
  var ordered = @records
  ordered.sort(proc(a, b: tuple[goalId: string, node: NodeId]): int =
    cmp(a.goalId, b.goalId))
  var payload = ""
  var children: seq[NodeId] = @[]
  for item in ordered:
    appendField(payload, item.goalId)
    children.add(item.node)
  MerkleNode(kind: nkGoalSet, payload: payload, children: children)

proc sourceSet*(blockIds: openArray[string], sourceRoots: openArray[NodeId]): MerkleNode =
  var payload = ""
  appendField(payload, $blockIds.len)
  for blockId in blockIds: appendField(payload, blockId)
  MerkleNode(kind: nkSourceSet, payload: payload, children: @sourceRoots)

proc environment*(fingerprint: string): MerkleNode =
  MerkleNode(kind: nkEnvironment, payload: fingerprint)

proc proofState*(documentRoot, sourcesRoot, goalsRoot, environmentRoot: NodeId): MerkleNode =
  MerkleNode(kind: nkProofState,
    children: @[documentRoot, sourcesRoot, goalsRoot, environmentRoot])

proc transition*(parent: NodeId, actionKind, goalId, arguments: string,
                 successor: NodeId, checkerVersion: string): MerkleNode =
  var payload = ""
  for field in [actionKind, goalId, arguments, checkerVersion]:
    appendField(payload, field)
  MerkleNode(kind: nkTransition, payload: payload,
    children: @[parent, successor])

proc buildSourceTree*(source: string): tuple[root: NodeId, nodes: seq[tuple[id: NodeId, node: MerkleNode]]] =
  var allNodes: seq[tuple[id: NodeId, node: MerkleNode]] = @[]
  var leaves: seq[tuple[id: NodeId, node: MerkleNode, bytes: int]] = @[]
  if source.len == 0:
    let node = leaf("")
    allNodes.add((nodeId(node), node))
    result.root = nodeId(node)
    result.nodes = allNodes
    return
  var offset = 0
  while offset < source.len:
    let stop = min(offset + SourceChunkBytes, source.len)
    let node = leaf(source[offset ..< stop])
    let id = nodeId(node)
    allNodes.add((id, node))
    leaves.add((id, node, stop - offset))
    offset = stop
  proc build(lo, hi: int): tuple[id: NodeId, bytes: int] =
    if hi - lo == 1:
      return (leaves[lo].id, leaves[lo].bytes)
    let mid = lo + (hi - lo) div 2
    let left = build(lo, mid)
    let right = build(mid, hi)
    let node = branch(left.id, right.id, left.bytes, right.bytes)
    let id = nodeId(node)
    allNodes.add((id, node))
    (id, node.byteLength)
  result.root = build(0, leaves.len).id
  result.nodes = allNodes

proc initNodeCache*(maxNodes = 256): NodeCache =
  NodeCache(nodes: initTable[NodeId, MerkleNode](),
            lru: @[], maxNodes: max(1, maxNodes))

proc touch(cache: var NodeCache, id: NodeId) =
  let i = cache.lru.find(id)
  if i >= 0: cache.lru.delete(i)
  cache.lru.add(id)

proc put*(cache: var NodeCache, id: NodeId, node: MerkleNode) =
  if not verified(id, node):
    raise newException(CacheError, "node hash does not match canonical content")
  cache.nodes[id] = node
  cache.touch(id)
  while cache.nodes.len > cache.maxNodes:
    let victim = cache.lru[0]
    cache.lru.delete(0)
    cache.nodes.del(victim)

proc contains*(cache: NodeCache, id: NodeId): bool = cache.nodes.hasKey(id)

proc evict*(cache: var NodeCache, id: NodeId): bool =
  if not cache.nodes.hasKey(id): return false
  cache.nodes.del(id)
  let i = cache.lru.find(id)
  if i >= 0: cache.lru.delete(i)
  true

proc get*(cache: var NodeCache, id: NodeId): MerkleNode =
  if not cache.nodes.hasKey(id):
    raise newException(CacheError, "unknown node " & idText(id))
  cache.touch(id)
  cache.nodes[id]

proc missingClosure*(cache: NodeCache, requested: openArray[NodeId]): seq[NodeId] =
  var missing: seq[NodeId] = @[]
  var visited = initTable[NodeId, bool]()
  proc visit(id: NodeId) =
    if visited.hasKey(id): return
    visited[id] = true
    if not cache.nodes.hasKey(id):
      missing.add(id)
      return
    for child in cache.nodes[id].children: visit(child)
  for id in requested: visit(id)
  result = missing

proc reconstructSource*(cache: var NodeCache, id: NodeId): string =
  let node = cache.get(id)
  case node.kind
  of nkSourceLeaf: node.payload
  of nkSourceBranch:
    if node.children.len != 2:
      raise newException(CacheError, "source branch must have two children")
    reconstructSource(cache, node.children[0]) &
      reconstructSource(cache, node.children[1])
  else:
    raise newException(CacheError, "requested node is not a source node")

proc cacheSize*(cache: NodeCache): int = cache.nodes.len
