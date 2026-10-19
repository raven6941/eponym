## Differential properties for the isolated destination-passing prototype.

import falsify
import experimental/qtt_dps
import eponym_mac
import eponym_embed
import std/strutils

proc referenceValue(expression: IntExpr, args: openArray[int] = []): int =
  case expression.kind
  of ieLiteral: expression.literal
  of ieVariable: args[expression.variableIndex]
  of ieAdd, ieSub, ieMul:
    let left = referenceValue(expression.left, args)
    let right = referenceValue(expression.right, args)
    case expression.kind
    of ieAdd: left + right
    of ieSub: left - right
    of ieMul: left * right
    else: 0

proc `$`(expression: IntExpr): string =
  case expression.kind
  of ieLiteral: $expression.literal
  of ieVariable: "arg" & $expression.variableIndex
  of ieAdd, ieSub, ieMul:
    let op = case expression.kind
      of ieAdd: "+"
      of ieSub: "-"
      of ieMul: "*"
      else: "?"
    "(" & $expression.left & " " & op & " " & $expression.right & ")"

proc genExpression(r: var Rng, depth: int): IntExpr =
  if depth == 0 or r.genInt(0, 3) == 0:
    intLiteral(r.genInt(-20, 20))
  else:
    intAdd(genExpression(r, depth - 1), genExpression(r, depth - 1))

eponymBlock:
  postulate(Int, Univ)
  proc checkedLinearPlusSeven(x {.linear.}: Int): Int = addInt(x, 7)
  proc checkedLinearArithmetic(left {.linear.}, right {.linear.}: Int): Int =
    subInt(mulInt(left, 2), right)
  proc checkedLinearRightSkew(a {.linear.}, b {.linear.}, c {.linear.},
      d {.linear.}: Int): Int = addInt(a, addInt(b, addInt(c, d)))
  proc checkedLinearNestedSubtraction(a {.linear.}, b {.linear.},
      c {.linear.}, d {.linear.}: Int): Int =
    subInt(a, subInt(b, subInt(c, d)))
  proc checkedLinearBalanced(a {.linear.}, b {.linear.}, c {.linear.},
      d {.linear.}: Int): Int = addInt(addInt(a, b), addInt(c, d))
  proc checkedLinearBalanced8(a {.linear.}, b {.linear.}, c {.linear.},
      d {.linear.}, e {.linear.}, f {.linear.}, g {.linear.},
      h {.linear.}: Int): Int =
    addInt(addInt(addInt(a, b), addInt(c, d)),
      addInt(addInt(e, f), addInt(g, h)))
  runtimeDps(checkedLinearPlusSeven)
  runtimeDps(checkedLinearArithmetic)
  runtimeDps(checkedLinearRightSkew)
  runtimeDps(checkedLinearNestedSubtraction)
  runtimeDps(checkedLinearBalanced)
  runtimeDps(checkedLinearBalanced8)

var rng = initRng(0xD05)
let cases = forAll(
  "destination-passing expressions match immutable evaluation", rng, 200,
  proc(r: var Rng): IntExpr = genExpression(r, 5),
  proc(expression: IntExpr): bool =
    let evaluated = evaluate(expression)
    evaluated.value == referenceValue(expression) and
      isExclusivelyOwnedTree(expression) and
      evaluated.stats.usedDestinationPassing and
      evaluated.stats.allocatedCells == 0)
if not cases:
  quit(1)

let variableExpression = intAdd(intVariable(0), intLiteral(7))
let variableCases = forAll(
  "destination-passing IR evaluates linear Int inputs", rng, 200,
  proc(r: var Rng): int = r.genInt(-1000, 1000),
  proc(value: int): bool =
    let evaluated = evaluate(variableExpression, @[value])
    evaluated.value == referenceValue(variableExpression, @[value]) and
      evaluated.stats.usedDestinationPassing and
      evaluated.stats.allocatedCells == 0,
  shrinkInt)
if not variableCases:
  quit(1)

let shared = intAdd(intLiteral(2), intLiteral(3))
let sharedGraph = intAdd(shared, shared)
let fallback = evaluate(sharedGraph)
doAssert fallback.value == 10
doAssert not isExclusivelyOwnedTree(sharedGraph)
doAssert not fallback.stats.usedDestinationPassing
doAssert fallback.stats.allocatedCells == 7

var cyclic = IntExpr(kind: ieAdd, left: nil, right: intLiteral(1))
cyclic.left = cyclic
doAssert not isExclusivelyOwnedTree(cyclic)
var cyclicRejected = false
try:
  discard evaluate(cyclic)
except ValueError as error:
  cyclicRejected = "cyclic Int expression" in error.msg
cyclic.left = intLiteral(0) # break the test cycle for reference-counted GC
doAssert cyclicRejected

var longChain = intLiteral(0)
for _ in 0 ..< 500:
  longChain = intAdd(longChain, intLiteral(1))
let optimized = evaluate(longChain)
let immutable = evaluateImmutable(longChain)
let reference = referenceValue(longChain)
doAssert optimized.value == reference
doAssert immutable.value == reference
doAssert optimized.value == 500
doAssert optimized.stats.usedDestinationPassing
doAssert optimized.stats.allocatedCells == 0
doAssert immutable.stats.allocatedCells == 1_001
echo "immutable workload cells: ", immutable.stats.allocatedCells
echo "destination-passing workload cells: ", optimized.stats.allocatedCells
let generatedCases = forAll(
  "generated destination-passing Int code matches checked evaluation", rng, 200,
  proc(r: var Rng): int = r.genInt(-1_000_000, 1_000_000),
  proc(value: int): bool =
    let generated = checkedLinearPlusSevenDps(value)
    generated.value == checkedLinearPlusSeven(value) and
      generated.value == value + 7 and generated.stackSlots == 1 and
      generated.heapCells == 0,
  shrinkInt)
if not generatedCases:
  quit(1)

let arithmeticCases = forAll(
  "generated DPS maps multiple QTT parameters and primitive operators", rng, 200,
  proc(r: var Rng): int = r.genInt(-100, 100),
  proc(left: int): bool =
    let right = left + 1
    let generated = checkedLinearArithmeticDps(left, right)
    generated.value == checkedLinearArithmetic(left, right) and
      generated.value == left - 1 and generated.stackSlots == 1 and
      generated.heapCells == 0,
  shrinkInt)
if not arithmeticCases:
  quit(1)

let rightSkewCases = forAll(
  "right-skewed QTT expressions reuse one generated slot", rng, 200,
  proc(r: var Rng): array[4, int] =
    [r.genInt(-100, 100), r.genInt(-100, 100), r.genInt(-100, 100),
      r.genInt(-100, 100)],
  proc(values: array[4, int]): bool =
    let (a, b, c, d) = (values[0], values[1], values[2], values[3])
    let sum = checkedLinearRightSkew(a, b, c, d)
    let sumDps = checkedLinearRightSkewDps(a, b, c, d)
    let difference = checkedLinearNestedSubtraction(a, b, c, d)
    let differenceDps = checkedLinearNestedSubtractionDps(a, b, c, d)
    sumDps.value == sum and sumDps.value == a + b + c + d and
      differenceDps.value == difference and
      differenceDps.value == a - (b - (c - d)) and
      sumDps.stackSlots == 1 and differenceDps.stackSlots == 1 and
      sumDps.heapCells == 0 and differenceDps.heapCells == 0)
if not rightSkewCases:
  quit(1)

let balancedCases = forAll(
  "balanced QTT expressions allocate only the live temporary", rng, 200,
  proc(r: var Rng): array[4, int] =
    [r.genInt(-100, 100), r.genInt(-100, 100), r.genInt(-100, 100),
      r.genInt(-100, 100)],
  proc(values: array[4, int]): bool =
    let (a, b, c, d) = (values[0], values[1], values[2], values[3])
    let ordinary = checkedLinearBalanced(a, b, c, d)
    let optimized = checkedLinearBalancedDps(a, b, c, d)
    optimized.value == ordinary and optimized.value == a + b + c + d and
      optimized.stackSlots == 2 and optimized.heapCells == 0)
if not balancedCases:
  quit(1)

let deeperBalancedCases = forAll(
  "nested balanced QTT expressions reuse a logarithmic slot pool", rng, 200,
  proc(r: var Rng): array[8, int] =
    [r.genInt(-100, 100), r.genInt(-100, 100), r.genInt(-100, 100),
      r.genInt(-100, 100), r.genInt(-100, 100), r.genInt(-100, 100),
      r.genInt(-100, 100), r.genInt(-100, 100)],
  proc(values: array[8, int]): bool =
    let ordinary = checkedLinearBalanced8(values[0], values[1], values[2],
      values[3], values[4], values[5], values[6], values[7])
    let optimized = checkedLinearBalanced8Dps(values[0], values[1],
      values[2], values[3], values[4], values[5], values[6], values[7])
    optimized.value == ordinary and optimized.value == values[0] + values[1] +
      values[2] + values[3] + values[4] + values[5] + values[6] + values[7] and
      optimized.stackSlots == 3 and optimized.heapCells == 0)
if not deeperBalancedCases:
  quit(1)

echo "test_qtt_dps: differential properties and ownership fallback passed"
echo "test_qtt_dps: checked Nim code generation property passed"
