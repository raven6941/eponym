## Differential properties for the isolated destination-passing prototype.

import falsify
import experimental/qtt_dps
import std/strutils

proc referenceValue(expression: IntExpr): int =
  case expression.kind
  of ieLiteral: expression.literal
  of ieAdd:
    referenceValue(expression.left) + referenceValue(expression.right)

proc `$`(expression: IntExpr): string =
  case expression.kind
  of ieLiteral: $expression.literal
  of ieAdd: "(" & $expression.left & " + " & $expression.right & ")"

proc genExpression(r: var Rng, depth: int): IntExpr =
  if depth == 0 or r.genInt(0, 3) == 0:
    intLiteral(r.genInt(-20, 20))
  else:
    intAdd(genExpression(r, depth - 1), genExpression(r, depth - 1))

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
echo "test_qtt_dps: differential properties and ownership fallback passed"
