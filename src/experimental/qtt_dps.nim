## A narrow QTT-inspired destination-passing prototype.
##
## This is intentionally separate from Eponym elaboration and wrapper
## generation. It models first-order Int expressions, proves the expression
## graph is a tree (no shared mutable ownership), and then writes each result
## into a caller-provided stack slot. Graphs with shared nodes use the
## allocation-heavy immutable evaluator.

import std/[sets, tables]

type
  IntExprKind* = enum
    ieLiteral, ieAdd

  IntExpr* = ref object
    case kind*: IntExprKind
    of ieLiteral:
      literal*: int
    of ieAdd:
      left*, right*: IntExpr

  IntCell = ref object
    value: int

  EvalStats* = object
    allocatedCells*: int
    usedDestinationPassing*: bool

proc intLiteral*(value: int): IntExpr =
  IntExpr(kind: ieLiteral, literal: value)

proc intAdd*(left, right: IntExpr): IntExpr =
  IntExpr(kind: ieAdd, left: left, right: right)

proc analyzeOwnership(root: IntExpr): tuple[exclusiveTree, cyclic: bool] =
  if root.isNil: return
  var incoming = initTable[pointer, int]()
  var expanded = initHashSet[pointer]()
  var active = initHashSet[pointer]()
  var cyclic = false
  proc visit(node: IntExpr) =
    if node.isNil: return
    let key = cast[pointer](node)
    incoming[key] = incoming.getOrDefault(key) + 1
    if key in active:
      cyclic = true
      return
    if key in expanded: return
    expanded.incl(key)
    active.incl(key)
    if node.kind == ieAdd:
      visit(node.left)
      visit(node.right)
    active.excl(key)
  visit(root)
  result.cyclic = cyclic
  result.exclusiveTree = not cyclic
  for count in incoming.values:
    if count != 1: result.exclusiveTree = false

proc isExclusivelyOwnedTree*(root: IntExpr): bool =
  ## Each node must have one incoming edge. Shared graphs cannot reuse slots.
  analyzeOwnership(root).exclusiveTree

proc evalImmutable(node: IntExpr, stats: var EvalStats): IntCell =
  case node.kind
  of ieLiteral:
    inc stats.allocatedCells
    new(result)
    result.value = node.literal
  of ieAdd:
    let left = evalImmutable(node.left, stats)
    let right = evalImmutable(node.right, stats)
    inc stats.allocatedCells
    new(result)
    result.value = left.value + right.value

proc evalInto(node: IntExpr, destination: var int) =
  ## Destination-passing evaluation uses only stack locals and mutates the
  ## final result slot. It is selected only after the ownership-tree check.
  case node.kind
  of ieLiteral:
    destination = node.literal
  of ieAdd:
    var leftValue, rightValue: int
    evalInto(node.left, leftValue)
    evalInto(node.right, rightValue)
    destination = leftValue + rightValue

proc evaluateImmutable*(root: IntExpr): tuple[value: int, stats: EvalStats] =
  if root.isNil:
    raise newException(ValueError, "cannot evaluate a nil Int expression")
  if analyzeOwnership(root).cyclic:
    raise newException(ValueError, "cannot evaluate a cyclic Int expression")
  let value = evalImmutable(root, result.stats)
  result.value = value.value

proc evaluate*(root: IntExpr): tuple[value: int, stats: EvalStats] =
  if root.isNil:
    raise newException(ValueError, "cannot evaluate a nil Int expression")
  let ownership = analyzeOwnership(root)
  if ownership.cyclic:
    raise newException(ValueError, "cannot evaluate a cyclic Int expression")
  if ownership.exclusiveTree:
    result.stats.usedDestinationPassing = true
    evalInto(root, result.value)
  else:
    result = evaluateImmutable(root)
