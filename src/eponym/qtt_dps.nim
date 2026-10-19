## A narrow QTT-inspired destination-passing prototype.
##
## This module models first-order Int expressions, proves the expression
## graph is a tree (no shared mutable ownership), and writes each result into
## a caller-provided stack slot. It also lowers a checked linear Int term to
## this IR and emits an allocation-free Nim wrapper for that restricted form.

import macros
import std/[sets, tables]
import eponym_init

type
  IntExprKind* = enum
    ieLiteral, ieVariable, ieAdd, ieSub, ieMul

  IntExpr* = ref object
    case kind*: IntExprKind
    of ieLiteral:
      literal*: int
    of ieVariable:
      variableIndex*: int
    of ieAdd, ieSub, ieMul:
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

proc intVariable*(index: int): IntExpr =
  IntExpr(kind: ieVariable, variableIndex: index)

proc intSub*(left, right: IntExpr): IntExpr =
  IntExpr(kind: ieSub, left: left, right: right)

proc intMul*(left, right: IntExpr): IntExpr =
  IntExpr(kind: ieMul, left: left, right: right)

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
    if node.kind in {ieAdd, ieSub, ieMul}:
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

proc evalImmutable(node: IntExpr, stats: var EvalStats,
                   args: openArray[int]): IntCell =
  case node.kind
  of ieLiteral:
    inc stats.allocatedCells
    new(result)
    result.value = node.literal
  of ieVariable:
    if node.variableIndex < 0 or node.variableIndex >= args.len:
      raise newException(ValueError, "Int expression argument index out of range")
    inc stats.allocatedCells
    new(result)
    result.value = args[node.variableIndex]
  of ieAdd, ieSub, ieMul:
    let left = evalImmutable(node.left, stats, args)
    let right = evalImmutable(node.right, stats, args)
    inc stats.allocatedCells
    new(result)
    result.value = case node.kind
      of ieAdd: left.value + right.value
      of ieSub: left.value - right.value
      of ieMul: left.value * right.value
      else: 0

proc evalInto(node: IntExpr, destination: var int, args: openArray[int]) =
  ## Destination-passing evaluation uses only stack locals and mutates the
  ## final result slot. It is selected only after the ownership-tree check.
  case node.kind
  of ieLiteral:
    destination = node.literal
  of ieVariable:
    if node.variableIndex < 0 or node.variableIndex >= args.len:
      raise newException(ValueError, "Int expression argument index out of range")
    destination = args[node.variableIndex]
  of ieAdd, ieSub, ieMul:
    var leftValue, rightValue: int
    evalInto(node.left, leftValue, args)
    evalInto(node.right, rightValue, args)
    destination = case node.kind
      of ieAdd: leftValue + rightValue
      of ieSub: leftValue - rightValue
      of ieMul: leftValue * rightValue
      else: 0

proc evaluateImmutable*(root: IntExpr,
                        args: openArray[int] = []):
    tuple[value: int, stats: EvalStats] =
  if root.isNil:
    raise newException(ValueError, "cannot evaluate a nil Int expression")
  if analyzeOwnership(root).cyclic:
    raise newException(ValueError, "cannot evaluate a cyclic Int expression")
  let value = evalImmutable(root, result.stats, args)
  result.value = value.value

proc evaluate*(root: IntExpr, args: openArray[int] = []):
    tuple[value: int, stats: EvalStats] =
  if root.isNil:
    raise newException(ValueError, "cannot evaluate a nil Int expression")
  let ownership = analyzeOwnership(root)
  if ownership.cyclic:
    raise newException(ValueError, "cannot evaluate a cyclic Int expression")
  if ownership.exclusiveTree:
    result.stats.usedDestinationPassing = true
    evalInto(root, result.value, args)
  else:
    result = evaluateImmutable(root, args)

proc markCheckedNode(term: Term, seen, active: var seq[Term],
                     diagnostic: var string): bool =
  if term.isNil:
    diagnostic = "runtimeDps cannot compile a nil term"
    return false
  for checked in active:
    if checked == term:
      diagnostic = "runtimeDps cannot compile cyclic terms"
      return false
  for checked in seen:
    if checked == term:
      diagnostic = "runtimeDps requires an exclusively owned checked term tree"
      return false
  seen.add(term)
  active.add(term)
  true

proc lowerCheckedInt(term: Term, arity: int, seen, active: var seq[Term],
                     useCounts: var seq[int],
                     diagnostic: var string): IntExpr =
  if not markCheckedNode(term, seen, active, diagnostic):
    return intLiteral(0)
  defer: active.setLen(active.len - 1)
  case term.kind
  of tInt:
    result = intLiteral(term.intVal)
  of tV:
    if term.idx < 0 or term.idx >= arity:
      diagnostic = "runtimeDps supports only references to its Int parameters"
      return intLiteral(0)
    let paramIndex = arity - term.idx - 1
    inc useCounts[paramIndex]
    result = intVariable(paramIndex)
  of tApp:
    if term.fn.isNil or term.fn.kind != tApp or term.fn.fn.isNil or
        term.fn.fn.kind != tPrim:
      diagnostic = "runtimeDps supports only fully applied Int primitives"
      return intLiteral(0)
    if not markCheckedNode(term.fn, seen, active, diagnostic):
      return intLiteral(0)
    active.setLen(active.len - 1)
    if not markCheckedNode(term.fn.fn, seen, active, diagnostic):
      return intLiteral(0)
    active.setLen(active.len - 1)
    let left = lowerCheckedInt(term.fn.arg, arity, seen, active, useCounts,
                               diagnostic)
    if diagnostic.len > 0: return intLiteral(0)
    let right = lowerCheckedInt(term.arg, arity, seen, active, useCounts,
                                diagnostic)
    if diagnostic.len > 0: return intLiteral(0)
    case term.fn.fn.primOp
    of opAdd: result = intAdd(left, right)
    of opSub: result = intSub(left, right)
    of opMul: result = intMul(left, right)
  else:
    diagnostic =
      "runtimeDps supports only Int literals, linear parameters, and +, -, *"
    return intLiteral(0)

proc tryLowerCheckedLinearInt*(term: Term, arity: int):
    tuple[expression: IntExpr, error: string] =
  ## Lower a checked term body, rejecting sharing, cycles, and repeated or
  ## unused source arguments independently of the elaborator's QTT check.
  var seen, active: seq[Term] = @[]
  var useCounts = newSeq[int](arity)
  result.expression = lowerCheckedInt(term, arity, seen, active, useCounts,
                                      result.error)
  if result.error.len > 0: return
  for i, count in useCounts:
    if count != 1:
      result.error = "runtimeDps requires parameter " & $i &
        " to be used exactly once"
      return

proc lowerCheckedLinearInt*(term: Term, arity: int): IntExpr =
  ## Raising convenience form for ordinary Nim callers; macros should use
  ## tryLowerCheckedLinearInt to keep diagnostics inside the Nim VM.
  let lowered = tryLowerCheckedLinearInt(term, arity)
  if lowered.error.len > 0:
    raise newException(ValueError, lowered.error)
  lowered.expression

proc emitInto(node: IntExpr, args: openArray[NimNode], statements: NimNode,
              slots: var int): NimNode =
  result = genSym(nskVar, "dpsSlot")
  statements.add(newVarStmt(result, newLit(0)))
  inc slots
  case node.kind
  of ieLiteral:
    statements.add(newAssignment(copyNimTree(result), newLit(node.literal)))
  of ieVariable:
    if node.variableIndex < 0 or node.variableIndex >= args.len:
      error("runtimeDps variable index is out of range")
    statements.add(newAssignment(copyNimTree(result),
      copyNimTree(args[node.variableIndex])))
  of ieAdd, ieSub, ieMul:
    let left = emitInto(node.left, args, statements, slots)
    let right = emitInto(node.right, args, statements, slots)
    let op = case node.kind
      of ieAdd: ident"+"
      of ieSub: ident"-"
      of ieMul: ident"*"
      else: ident"+"
    statements.add(newAssignment(copyNimTree(result),
      newTree(nnkInfix, op, left, right)))

proc generateLinearIntDpsProc*(name: string, parameterNames: seq[string],
                               expression: IntExpr): NimNode =
  ## Emit a typed Nim proc with mutable local result slots and no heap cells.
  ## The Eponym term lowering has already verified exclusive ownership before
  ## constructing this fresh tree; avoid pointer-based IR checks in the Nim VM.
  if parameterNames.len == 0 or expression.isNil:
    error("runtimeDps requires parameters and an Int expression")
  var formal = newNimNode(nnkFormalParams)
  formal.add(parseExpr("tuple[value: int, stackSlots: int, heapCells: int]"))
  var args: seq[NimNode] = @[]
  for parameterName in parameterNames:
    let arg = genSym(nskParam, parameterName)
    args.add(arg)
    formal.add(newIdentDefs(arg, ident"int", newEmptyNode()))
  var body = newStmtList()
  var slots = 0
  let valueSlot = emitInto(expression, args, body, slots)
  body.add(newAssignment(newTree(nnkDotExpr, ident"result", ident"value"),
                         valueSlot))
  body.add(newAssignment(newTree(nnkDotExpr, ident"result", ident"stackSlots"),
                         newLit(slots)))
  body.add(newAssignment(newTree(nnkDotExpr, ident"result", ident"heapCells"),
                         newLit(0)))
  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident"*", ident(name)))
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(body)
