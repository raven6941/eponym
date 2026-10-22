## Differential and effect-count checks for the core QTT erasure pass (#328).

import std/[tables, os, strutils]
import falsify
import eponym_init
import erasure
import preterm
import elab
import parse_surf

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

let repoRoot = parentDir(parentDir(currentSourcePath()))
let vecProgram = "import \"lib/vec.ep\"\n"
let vecChecked = elabCheckDirStateAll(vecProgram, repoRoot)
var foundVappend = false
for definition in vecChecked.allDefs:
  if definition.name == "vappend":
    foundVappend = true
    discard eraseQ0Arguments(definition.tmTm)
expect(foundVappend, "length-indexed vector append erases without refId collisions")

var branchDrv = initModuleDriver()
discard branchDrv.elabFile(repoRoot / "lib/bool.ep")
let branchDefs = branchDrv.elabDeclsDir(parseProgram("""
postulate Int : Type 0
proc branchLinear (flag : Bool) (1 value : Int) : Int =
  ifThenElse flag (lam (u : 1). value) (lam (u : 1). value) <>
"""), repoRoot, "<q1-branch-erasure>")
var branchLinearDef: ElabDef
for defn in branchDefs:
  if defn.name == "branchLinear": branchLinearDef = defn
expect(not branchLinearDef.tmTm.isNil,
  "branch-linear definition elaborates")
discard eraseQ0Arguments(branchLinearDef.tmTm)
expect(true,
  "q1 branch profiles are rechecked consistently by codegen erasure")

var multiBranchDrv = initModuleDriver()
let multiBranchDefs = multiBranchDrv.elabDeclsDir(parseProgram("""
postulate Int : Type 0
data Tri : Type 0 where
| first : Tri
| second : Tri
| third : Tri
proc triLinear (tag : Tri) (1 value : Int) : Int =
  triElim (lam (u : Tri). Pi(unit : 1). Int)
          (lam (unit : 1). value)
          (lam (unit : 1). value)
          (lam (unit : 1). value)
          tag
          <>
"""), repoRoot, "<three-way-q1-branch>")
var triLinearDef: ElabDef
for defn in multiBranchDefs:
  if defn.name == "triLinear": triLinearDef = defn
expect(not triLinearDef.tmTm.isNil,
  "q1 usage accepts balanced alternatives in a three-case eliminator")
discard eraseQ0Arguments(triLinearDef.tmTm)
expect(true, "three-case q1 branch profiles pass codegen erasure")

var triDuplicateRejected = false
var badTriDrv = initModuleDriver()
try:
  discard badTriDrv.elabDeclsDir(parseProgram("""
postulate Int : Type 0
postulate duplicateInt : Int -> Int -> Int
data Tri : Type 0 where
| first : Tri
| second : Tri
| third : Tri
proc triDuplicate (tag : Tri) (1 value : Int) : Int =
  triElim (lam (u : Tri). Pi(unit : 1). Int)
          (lam (unit : 1). value)
          (lam (unit : 1). value)
          (lam (unit : 1). duplicateInt value value)
          tag
          <>
"""), repoRoot, "<three-way-q1-duplicate>")
except ElabError as e:
  triDuplicateRejected = "linear variable 'value' used 1 or 2+ time(s)" in e.msg
expect(triDuplicateRejected,
  "three-case q1 analysis rejects a duplicate on one branch")

# Constructor identities in an eliminator's cached rule table do not appear as
# ordinary tR nodes. Make the first fresh inference parameter collide with one
# of those identities: without reserving rule keys, evaluating this dependent
# codomain mistakes the parameter for the constructor and opens an invalid
# reduction template.
var collisionIds = Supply()
let collisionUnitType = eval(tmC(cOne), @[])
# Reserve IDs 1 and 2 as unrelated globals, then give the eliminator and
# postulate IDs 3 and 4. Constructor IDs 2 and 6 are present only in the
# eliminator's cached rules; 6 also collides with the second neutral opened by
# a ref-only reservation walk (which starts fresh IDs at 5).
discard newPostulateRef(collisionIds, collisionUnitType) # ID 1
discard newPostulateRef(collisionIds, collisionUnitType) # ID 2
let collisionElim = newRedRef(collisionIds,
  runtimeArrowType(collisionUnitType, collisionUnitType), 1)
attachRedCase(collisionElim, 2, vv(0))
attachRedCase(collisionElim, 6, vv(0))
let collisionBody = tmLet(
  tmApp(collisionElim, vv(0)), tmC(cStar), "reduce-unused",
  tmPi(tmC(cOne), "y", tmC(cOne)))
let collisionFnType = eval(tmPi(tmC(cOne), "x", collisionBody), @[])
let collisionFn = newPostulateRef(collisionIds, collisionFnType)
let collisionCall = tmLam(tmC(cOne), "outer",
  tmLam(tmC(cOne), "input",
    tmApp(tmApp(collisionFn, vv(0)), tmC(cVoid))))
discard eraseQ0Arguments(collisionCall)
expect(true,
  "erasure reserves constructor IDs embedded in cached eliminator rules")

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
