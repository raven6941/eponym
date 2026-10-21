## Differential and effect-count checks for the core QTT erasure pass (#328).

import std/tables
import falsify
import eponym_init
import erasure
import preterm

proc expect(ok: bool, message: string) =
  if not ok:
    quit("FAIL: " & message, 1)
  echo "ok: ", message

const Seed = 328'u64
const Cases = 200

type ErasureCase = object
  effects: int

proc genErasureCase(r: var Rng): ErasureCase =
  ErasureCase(effects: r.genInt(0, 50))

proc shrinkErasureCase(c: ErasureCase): seq[ErasureCase] =
  result = @[ErasureCase(effects: 0)]
  if c.effects != 0:
    result.add(ErasureCase(effects: c.effects div 2))

var supply = Supply()
let unitType = eval(tmC(cOne), @[])
let unitValue = eval(tmC(cVoid), @[])
let ordinaryFnTy = runtimeArrowType(unitType, unitType)
let effectRef = newPostulateRef(supply, ordinaryFnTy)
let erasedFn = tmLam(tmC(cOne), "proof", tmC(cVoid), qty = q0)
let effectfulArg = tmApp(effectRef, tmC(cVoid))
let source = tmApp(erasedFn, effectfulArg)
let erased = eraseQ0Arguments(source)

expect(erased.kind == tApp and erased.arg.kind == tC and
       erased.arg.c == cVoid,
       "q0 application argument is replaced by the canonical erased witness")

var originalCalls = 0
var originalBindings = initTable[int, Value]()
originalBindings[effectRef.refId] = vHostFunc(
  proc(_: Value): Value =
    inc originalCalls
    unitValue)
let interpreted = evalWithBindings(source, @[], originalBindings)
expect(originalCalls == 1, "interpreter evaluates the original q0 argument")

var erasedCalls = 0
var erasedBindings = initTable[int, Value]()
erasedBindings[effectRef.refId] = vHostFunc(
  proc(_: Value): Value =
    inc erasedCalls
    unitValue)
let compiled = evalWithBindings(erased, @[], erasedBindings)
expect(erasedCalls == 0, "erased term does not evaluate the q0 argument")
expect(interpreted.whnf.kind == wConst and interpreted.whnf.c == cVoid and
       compiled.whnf.kind == wConst and compiled.whnf.c == cVoid,
       "erased and interpreted terms return the same observable value")

var ordinaryCalls = 0
var ordinaryBindings = initTable[int, Value]()
ordinaryBindings[effectRef.refId] = vHostFunc(
  proc(_: Value): Value =
    inc ordinaryCalls
    unitValue)
let ordinaryCall = tmApp(effectRef, tmC(cVoid))
let ordinaryErased = eraseQ0Arguments(ordinaryCall)
discard evalWithBindings(ordinaryErased, @[], ordinaryBindings)
expect(ordinaryCalls == 1,
       "unrestricted postulate calls remain executable after erasure")

let nested = tmApp(
  tmLam(tmC(cOne), "ordinary", tmApp(erasedFn, effectfulArg)), tmC(cVoid))
let nestedErased = eraseQ0Arguments(nested)
expect(nestedErased.kind == tApp and nestedErased.fn.kind == tLam and
       nestedErased.fn.scope.bdy.kind == tApp and
       nestedErased.fn.scope.bdy.arg.kind == tC,
       "erasure finds q0 applications under ordinary binders")

proc erasurePreservesResultAndSkipsEffects(input: ErasureCase): bool =
  var expensiveArg = tmC(cVoid)
  for i in 0 ..< input.effects:
    expensiveArg = tmLet(tmApp(effectRef, tmC(cVoid)), tmC(cOne),
                         "ignored" & $i, expensiveArg)
  let candidate = tmApp(erasedFn, expensiveArg)
  let candidateErased = eraseQ0Arguments(candidate)
  var sourceCalls = 0
  var sourceBindings = initTable[int, Value]()
  sourceBindings[effectRef.refId] = vHostFunc(
    proc(_: Value): Value =
      inc sourceCalls
      unitValue)
  let sourceValue = evalWithBindings(candidate, @[], sourceBindings)
  var erasedCallCount = 0
  var erasedRunBindings = initTable[int, Value]()
  erasedRunBindings[effectRef.refId] = vHostFunc(
    proc(_: Value): Value =
      inc erasedCallCount
      unitValue)
  let erasedValue = evalWithBindings(candidateErased, @[], erasedRunBindings)
  sourceCalls == input.effects and erasedCallCount == 0 and
    sourceValue.whnf.kind == wConst and sourceValue.whnf.c == cVoid and
    erasedValue.whnf.kind == wConst and erasedValue.whnf.c == cVoid

var rng = initRng(Seed)
let propertyPassed = forAll("q0-erasure-differential", rng, Cases,
  genErasureCase, erasurePreservesResultAndSkipsEffects, shrinkErasureCase)
expect(propertyPassed,
  "200 generated cases preserve results and skip erased work")

echo "all core erasure checks passed"
