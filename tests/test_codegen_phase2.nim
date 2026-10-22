## Differential tests + benchmark for the Phase 2 representation backend
## (Issue #330: v1 Int fragment, v2 Nat/Bool-as-int with match-compiled
## eliminators).
##
## A `differentialBlockRepr` macro elaborates a surface program at compile
## time with `Int`/`Nat`/`Bool -> int` runtime mappings and emits both the
## Phase-1 Value procs and the Phase-2 repr procs (`eponymCompiledRepr_<name>`).
## The test body checks each repr proc against the interpreter
## (`callValueFuncDir`) and against its Phase-1 compiled twin, then
## benchmarks interpreter vs Phase-1 vs Phase-2 on the same workload (per
## #19's framing, Phase 2 is measured against Phase 1's compiled output).

import std/[tables, macros, sequtils, strutils, times]
import falsify
import eponym_init
import eponym_embed
import eponym_mac
import elab
import codegen

proc expect(ok: bool, message: string) =
  if not ok:
    quit("FAIL: " & message, 1)
  echo "ok: ", message

macro differentialBlockRepr(src: static string, srcFile: static string): untyped =
  ## Elaborate `src` at compile time with `Int`/`Nat`/`Bool -> int`
  ## runtimeType mappings and emit Phase-1 + Phase-2 procs via the real
  ## compiler. Also emits `reprCompiledNames()` (which defs got a repr
  ## proc) and `testPostulateBindings()` (neutral bindings for the
  ## differential harness, as in the Phase-1 suite).
  let checked = elabCheckDirStateAll(src, "")
  var userLines = initTable[string, int]()
  for d in checked.defs:
    userLines[d.name] = 1
  proc intMappingFor(eponymName: string): HostRuntimeType =
    HostRuntimeType(eponymName: eponymName, nimType: ident"int",
      isRuntimeVector: false, isRuntimeList: false, isRuntimeOption: false,
      isRuntimeVariant: false, isRuntimeCodec: false,
      isGenericTypeWitnessable: true, encoder: nil, decoder: nil)
  let mappings = @[intMappingFor("Int"), intMappingFor("Nat"),
                   intMappingFor("Bool")]
  let cgBlock = compileBlockProcs(checked.defs, checked.globals, "", src,
    srcFile, userLines, mappings)
  if cgBlock.report["fortyTwo"].tier != cgtRepr or
      cgBlock.report["higher"].tier != cgtValue or
      not cgBlock.report["higher"].reason.contains("non-atomic binder domain"):
    error("codegen report should distinguish Phase 2 and Phase 1 fallback")
  result = newStmtList()
  for p in cgBlock.procs:
    result.add(p)
    # Repr procs carry user source positions, like the Phase-1 procs.
    if p.kind == nnkProcDef and p[0].kind == nnkPostfix and
        ($p[0][1]).startsWith("eponymCompiledRepr_"):
      let li = lineInfoObj(p)
      if not li.filename.endsWith("test_codegen_phase2.nim"):
        error("repr proc " & $p[0][1] &
          " missing user source position (got " & li.filename & ")")
  var names = newNimNode(nnkBracket)
  for name in cgBlock.compiledRepr.keys:
    names.add(newLit(name))
  result.add quote do:
    proc reprCompiledNames*(): seq[string] = @`names`
  var bindStmts = newStmtList()
  let bndSym = genSym(nskVar, "testBnd")
  bindStmts.add(newVarStmt(bndSym, newCall(bindSym"initRuntimeBindings")))
  for name, e in checked.globals.pairs:
    if e.tm != nil and e.tm.kind == tR and not e.tm.refIsDefn and
        not e.isElim and not e.isDataConstructor:
      let refIdLit = newLit(e.tm.refId)
      bindStmts.add(newTree(nnkAsgn,
        newTree(nnkBracketExpr, bndSym, refIdLit),
        newCall(bindSym"postulateValue", refIdLit,
          newCall(bindSym"initRuntimeBindings"))))
    elif e.isDataConstructor:
      let refIdLit = newLit(e.tm.refId)
      bindStmts.add(newTree(nnkAsgn,
        newTree(nnkBracketExpr, bndSym, refIdLit),
        newCall(bindSym"postulateValue", refIdLit,
          newCall(bindSym"initRuntimeBindings"))))
  bindStmts.add(bndSym)
  result.add quote do:
    proc testPostulateBindings*(): RuntimeBindings =
      `bindStmts`

const prog = """postulate Int : Type 0
proc fortyTwo : Int = 42
proc add (x : Int) (y : Int) : Int = addInt x y
proc mulAdd (x : Int) (y : Int) (z : Int) : Int = addInt (mulInt x y) z
proc nestedLet (x : Int) : Int =
  let y : Int = addInt x x in addInt y (mulInt x 3)
proc double (x : Int) : Int = addInt x x
proc quad (x : Int) : Int = double (double x)
proc betaRed (x : Int) : Int = (lam (y : Int). addInt y y) x
proc subThenMul (x : Int) (y : Int) : Int = mulInt (subInt x y) (subInt y x)

postulate tick : Int -> Int
proc tickTwice (x : Int) : Int = addInt (tick x) (tick x)
proc higher (f : Int -> Int) (x : Int) : Int = f x

data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
data Bool : Type 0 where
| true : Bool
| false : Bool
proc natZero : Nat = zero
proc natSeven : Nat = 7
proc natSucc (n : Nat) : Nat = suc n
proc natAdd (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) n (lam (p : Nat). lam (ih : Nat). suc ih) m
proc natMul (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) zero (lam (p : Nat). lam (ih : Nat). natAdd m ih) n
proc natDouble (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) zero (lam (p : Nat). lam (ih : Nat). suc (suc ih)) n
proc isZero (n : Nat) : Bool =
  natElim (lam (u : Nat). Bool) true (lam (p : Nat). lam (ih : Bool). false) n
proc notb (b : Bool) : Bool =
  boolElim (lam (u : Bool). Bool) false true b
proc andb (a : Bool) (b : Bool) : Bool =
  boolElim (lam (u : Bool). Bool) b false a
proc stepFn (p : Nat) (ih : Nat) : Nat = suc ih
proc stepFn2 (p : Nat) (ih : Nat) : Nat = natAdd p (suc ih)
proc addViaFn (m : Nat) (n : Nat) : Nat =
  natElim (lam (u : Nat). Nat) n stepFn2 m
proc q0Prefix (0 proof : Nat) (x : Int) : Int = x
proc q0Call (x : Int) : Int = q0Prefix 0 x
proc q0Middle (x : Int) (0 proof : Nat) (y : Int) : Int = addInt x y
proc q0MiddleCall (x : Int) (y : Int) : Int = q0Middle x 0 y
postulate inspectQ0 : Pi (f : Pi (0 proof : Nat). Int). Int
proc q0Capture (x : Int) : Int =
  inspectQ0 (lam (0 proof : Nat). x)
postulate tickNat : Nat -> Nat
proc q0EffectCall (n : Nat) : Nat =
  (lam (0 proof : Nat). tickNat 7) (tickNat n)
"""

differentialBlockRepr(prog, currentSourcePath())

proc checkRepr2(name: string, args: seq[int], expected: int) =
  ## Compare the repr proc against the literal expectation, the
  ## interpreter, and the Phase-1 compiled proc.
  let got = case name
    of "fortyTwo": eponymCompiledRepr_fortyTwo()
    of "add": eponymCompiledRepr_add(args[0], args[1])
    of "mulAdd": eponymCompiledRepr_mulAdd(args[0], args[1], args[2])
    of "nestedLet": eponymCompiledRepr_nestedLet(args[0])
    of "double": eponymCompiledRepr_double(args[0])
    of "quad": eponymCompiledRepr_quad(args[0])
    of "betaRed": eponymCompiledRepr_betaRed(args[0])
    of "subThenMul": eponymCompiledRepr_subThenMul(args[0], args[1])
    else: raise newException(ValueError, "unknown repr def " & name)
  expect(got == expected,
    name & " repr computes " & $expected & " on " & $args)
  let argVals = args.mapIt(vInt(it))
  let want = callValueFuncDir("", prog, name, argVals,
    testPostulateBindings())
  expect(want.whnfKind == wInt and want.whnfIntVal == expected,
    name & " interpreter agrees")
  let got1 = case name
    of "fortyTwo": eponymCompiled_fortyTwo(@[], testPostulateBindings())
    of "add": eponymCompiled_add(argVals, testPostulateBindings())
    of "mulAdd": eponymCompiled_mulAdd(argVals, testPostulateBindings())
    of "nestedLet": eponymCompiled_nestedLet(argVals, testPostulateBindings())
    of "double": eponymCompiled_double(argVals, testPostulateBindings())
    of "quad": eponymCompiled_quad(argVals, testPostulateBindings())
    of "betaRed": eponymCompiled_betaRed(argVals, testPostulateBindings())
    of "subThenMul": eponymCompiled_subThenMul(argVals, testPostulateBindings())
    else: raise newException(ValueError, "unknown phase-1 def " & name)
  expect(got1.whnfKind == wInt and got1.whnfIntVal == expected,
    name & " phase-1 agrees")

checkRepr2("fortyTwo", @[], 42)
for (x, y) in [(3, 4), (0, 0), (-5, 8)]:
  checkRepr2("add", @[x, y], x + y)
for (x, y, z) in [(2, 3, 4), (0, 7, 1), (5, 5, 5)]:
  checkRepr2("mulAdd", @[x, y, z], x * y + z)
for x in [0, 1, 5, 21]:
  checkRepr2("nestedLet", @[x], x + x + x * 3)
  checkRepr2("double", @[x], x + x)
  checkRepr2("quad", @[x], 4 * x)
  checkRepr2("betaRed", @[x], x + x)
for (x, y) in [(10, 3), (3, 10), (0, 0)]:
  checkRepr2("subThenMul", @[x, y], (x - y) * (y - x))

# --- v2: Nat/Bool as int, with match-compiled eliminators ---
# The interpreter's natElim/boolElim only fire on constructor-headed
# scrutinees (a wNatLit scrutinee stays stuck), so Nat arguments are built
# as suc-chains via natToValue and Bool arguments via boolToValue; results
# are decoded with valueToNat/valueToBool.
let natGlobals = getGlobals(prog)

var negativeNatRejected = false
try:
  discard eponymCompiledRepr_natSucc(-1)
except ValueError as error:
  negativeNatRejected = error.msg == "runtime Nat cannot be negative"
expect(negativeNatRejected,
  "Phase 2 Nat successor rejects negative host integers")

var natBoundaryRng = initRng(0x380'u64)
let natBoundaryCases = forAll(
  "interpreter, Phase 1, and Phase 2 agree at the host-int Nat boundary",
  natBoundaryRng, 200,
  proc(r: var Rng): int = high(int) - r.genInt(0, 2),
  proc(n: int): bool =
    let fits = n < high(int)
    let expected = if fits: n + 1 else: 0
    let input = natToValue(n)
    let bindings = testPostulateBindings()
    let interpreted = callValueFuncDir("", prog, "natSucc", @[input],
      bindings)
    let phase1 = eponymCompiled_natSucc(@[input], bindings)
    var interpretedMatches = false
    var phase1Matches = false
    try:
      let value = valueToNat(interpreted, natGlobals)
      interpretedMatches = fits and value == expected
    except ValueError as error:
      interpretedMatches = not fits and
        error.msg == "runtime Nat does not fit Nim int"
    try:
      let value = valueToNat(phase1, natGlobals)
      phase1Matches = fits and value == expected
    except ValueError as error:
      phase1Matches = not fits and
        error.msg == "runtime Nat does not fit Nim int"
    var phase2Matches = false
    try:
      let value = eponymCompiledRepr_natSucc(n)
      phase2Matches = fits and value == expected
    except ValueError as error:
      phase2Matches = not fits and
        error.msg == "runtime Nat does not fit Nim int"
    interpretedMatches and phase1Matches and phase2Matches,
  shrinkInt)
expect(natBoundaryCases,
  "runtime Nat values above high(int) fail consistently without wraparound")

proc checkReprNat(name: string, args: seq[int], expected: int) =
  ## Compare the repr proc against the literal expectation, the
  ## interpreter, and the Phase-1 compiled proc (Nat results decoded).
  let got = case name
    of "natZero": eponymCompiledRepr_natZero()
    of "natSeven": eponymCompiledRepr_natSeven()
    of "natAdd": eponymCompiledRepr_natAdd(args[0], args[1])
    of "natMul": eponymCompiledRepr_natMul(args[0], args[1])
    of "natDouble": eponymCompiledRepr_natDouble(args[0])
    of "stepFn2": eponymCompiledRepr_stepFn2(args[0], args[1])
    else: raise newException(ValueError, "unknown repr def " & name)
  expect(got == expected,
    name & " repr computes " & $expected & " on " & $args)
  let argVals = args.mapIt(natToValue(it, natGlobals))
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, argVals, bnd)
  expect(valueToNat(want, natGlobals) == expected,
    name & " interpreter agrees")
  let got1 = case name
    of "natZero": eponymCompiled_natZero(@[], bnd)
    of "natSeven": eponymCompiled_natSeven(@[], bnd)
    of "natAdd": eponymCompiled_natAdd(argVals, bnd)
    of "natMul": eponymCompiled_natMul(argVals, bnd)
    of "natDouble": eponymCompiled_natDouble(argVals, bnd)
    of "stepFn2": eponymCompiled_stepFn2(argVals, bnd)
    else: raise newException(ValueError, "unknown phase-1 def " & name)
  expect(valueToNat(got1, natGlobals) == expected,
    name & " phase-1 agrees")

proc checkReprBool(name: string, args: seq[int], expected: int) =
  ## Bool-typed defs: args/expectations as ints (1 = true, 0 = false).
  ## `isZero` takes a Nat argument; the rest take Bool arguments.
  let got = case name
    of "notb": eponymCompiledRepr_notb(args[0])
    of "andb": eponymCompiledRepr_andb(args[0], args[1])
    of "isZero": eponymCompiledRepr_isZero(args[0])
    else: raise newException(ValueError, "unknown repr def " & name)
  expect(got == expected,
    name & " repr computes " & $expected & " on " & $args)
  let argVals =
    if name == "isZero": @[natToValue(args[0], natGlobals)]
    else: args.mapIt(boolToValue(it != 0, natGlobals))
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", prog, name, argVals, bnd)
  expect(valueToBool(want, natGlobals) == (expected != 0),
    name & " interpreter agrees")
  let got1 = case name
    of "notb": eponymCompiled_notb(argVals, bnd)
    of "andb": eponymCompiled_andb(argVals, bnd)
    of "isZero": eponymCompiled_isZero(argVals, bnd)
    else: raise newException(ValueError, "unknown phase-1 def " & name)
  expect(valueToBool(got1, natGlobals) == (expected != 0),
    name & " phase-1 agrees")

checkReprNat("natZero", @[], 0)
checkReprNat("natSeven", @[], 7)
for (x, y) in [(3, 4), (0, 5), (10, 0)]:
  checkReprNat("natAdd", @[x, y], x + y)
for (x, y) in [(3, 4), (0, 7), (5, 5)]:
  checkReprNat("natMul", @[x, y], x * y)
for x in [0, 1, 21]:
  checkReprNat("natDouble", @[x], 2 * x)
for (x, y) in [(3, 4), (0, 0)]:
  checkReprNat("stepFn2", @[x, y], x + y + 1)
for x in [1, 0]:
  checkReprBool("notb", @[x], 1 - x)
for (x, y) in [(1, 1), (1, 0), (0, 1), (0, 0)]:
  checkReprBool("andb", @[x, y], x * y)
for x in [0, 1, 42]:
  checkReprBool("isZero", @[x], if x == 0: 1 else: 0)
for name in ["natZero", "natSeven", "natAdd", "natMul", "natDouble",
    "isZero", "notb", "andb", "stepFn2"]:
  expect(name in reprCompiledNames(), name & " has a repr proc")
for name in ["stepFn", "q0Prefix", "q0Call", "q0Middle",
    "q0MiddleCall"]:
  expect(name in reprCompiledNames(), name & " erases q0 binder slots")
for x in [0, 1, 19]:
  expect(eponymCompiledRepr_stepFn(x) == x + 1,
    "unused first Nat binder omitted from stepFn ABI")
  expect(eponymCompiledRepr_q0Prefix(x) == x,
    "explicit q0 prefix omitted from q0Prefix ABI")
  expect(eponymCompiledRepr_q0Call(x) == x,
    "q0 argument omitted from compiled local call")
for (x, y) in [(-17, 4), (0, 0), (18, -9)]:
  expect(eponymCompiledRepr_q0Middle(x, y) == x + y,
    "interleaved q0 binder omitted from generated signature")
  expect(eponymCompiledRepr_q0MiddleCall(x, y) == x + y,
    "interleaved q0 argument omitted from compiled local call")

block:
  let bnd = testPostulateBindings()
  let runtimeArg = vInt(23)
  let compiled = eponymCompiled_q0Prefix(@[runtimeArg], bnd)
  let interpreted = callValueFuncDir("", prog, "q0Prefix",
    @[natToValue(17, natGlobals), runtimeArg], bnd)
  expect(compiled.whnfKind == wInt and compiled.whnfIntVal == 23 and
    interpreted.whnfKind == wInt and interpreted.whnfIntVal == 23,
    "phase-1 Value ABI omits q0 prefix and preserves runtime arg order")
  let middleArgs = @[vInt(8), vInt(-3)]
  let middleCompiled = eponymCompiled_q0Middle(middleArgs, bnd)
  let middleInterpreted = callValueFuncDir("", prog, "q0Middle",
    @[vInt(8), natToValue(2, natGlobals), vInt(-3)], bnd)
  expect(middleCompiled.whnfKind == wInt and
    middleCompiled.whnfIntVal == 5 and middleInterpreted.whnfKind == wInt and
    middleInterpreted.whnfIntVal == 5,
    "phase-1 Value ABI omits an interleaved q0 binder")

block:
  let inspectId = getGlobals(prog)["inspectQ0"].tm.refId
  var generatedKind = wConst
  var generatedBindings = testPostulateBindings()
  generatedBindings[inspectId] = vHostFunc(proc(f: Value): Value =
    generatedKind = f.whnfKind
    vAppWithBindings(f, natToValue(9, natGlobals), generatedBindings))
  let generated = eponymCompiled_q0Capture(@[vInt(42)], generatedBindings)

  var interpretedKind = wConst
  var interpretedBindings = testPostulateBindings()
  interpretedBindings[inspectId] = vHostFunc(proc(f: Value): Value =
    interpretedKind = f.whnfKind
    vAppWithBindings(f, natToValue(9, natGlobals), interpretedBindings))
  let interpreted = callValueFuncDir("", prog, "q0Capture", @[vInt(42)],
    interpretedBindings)
  expect(generatedKind == wLam0 and interpretedKind == wLam and
    generated.whnfKind == wInt and generated.whnfIntVal == 42 and
    interpreted.whnfKind == wInt and interpreted.whnfIntVal == 42,
    "generated higher-order q0 closures are nullary, capture outer values, and agree with the unary interpreter")

var q0EffectRng = initRng(0x368'u64)
let q0EffectCases = forAll(
  "compiled and Value runtime paths erase effects in q0 arguments",
  q0EffectRng, 200,
  proc(r: var Rng): int = r.genInt(0, 100),
  proc(n: int): bool =
    let rtGlobals = getGlobals(prog)
    let tickId = rtGlobals["tickNat"].tm.refId
    var generatedCalls = 0
    var generatedBindings = testPostulateBindings()
    generatedBindings[tickId] = vHostFunc(proc(x: Value): Value =
      inc generatedCalls
      x)
    let generated = eponymCompiled_q0EffectCall(
      @[natToValue(n, natGlobals)], generatedBindings)
    var interpretedCalls = 0
    var interpretedBindings = testPostulateBindings()
    interpretedBindings[tickId] = vHostFunc(proc(x: Value): Value =
      inc interpretedCalls
      x)
    let interpreted = callValueFuncDir("", prog, "q0EffectCall",
      @[natToValue(n, natGlobals)], interpretedBindings)
    valueToNat(generated, natGlobals) == 7 and
      valueToNat(interpreted, natGlobals) == 7 and
      generatedCalls == 1 and interpretedCalls == 1)
expect(q0EffectCases,
  "runtime interpreter and generated q0 closures each run only the retained body effect")

# --- fragment boundaries: these get Phase-1 procs but no repr procs ---
expect("tickTwice" notin reprCompiledNames(),
  "postulate-calling def has no repr proc")
expect("higher" notin reprCompiledNames(),
  "higher-order def has no repr proc")
expect("addViaFn" notin reprCompiledNames(),
  "non-lambda natElim step case has no repr proc")
for name in ["fortyTwo", "add", "mulAdd", "nestedLet", "double", "quad",
    "betaRed", "subThenMul"]:
  expect(name in reprCompiledNames(), name & " has a repr proc")

# The fallback defs still work through the Phase-1 backend.
block:
  let rtGlobals = getGlobals(prog)
  let tickId = rtGlobals["tick"].tm.refId
  var bnd = testPostulateBindings()
  bnd[tickId] = vHostFunc(proc(x: Value): Value = vInt(x.whnfIntVal + 1))
  let got = eponymCompiled_tickTwice(@[vInt(10)], bnd)
  let want = callValueFuncDir("", prog, "tickTwice", @[vInt(10)], bnd)
  expect(got.whnfKind == wInt and got.whnfIntVal == 22, "tickTwice via phase-1")
  expect(got.whnfIntVal == want.whnfIntVal, "tickTwice phase-1 agrees")

# addViaFn (non-lambda step case) falls back to Phase-1 but still computes.
# Note: addViaFn is *not* addition — addViaFn m n recurses on m with
# stepFn2 p ih = natAdd p (suc ih), so addViaFn 3 4 = 10.
block:
  let bnd = testPostulateBindings()
  let args = @[natToValue(3, natGlobals), natToValue(4, natGlobals)]
  let got = eponymCompiled_addViaFn(args, bnd)
  let want = callValueFuncDir("", prog, "addViaFn", args, bnd)
  expect(valueToNat(got, natGlobals) == 10, "addViaFn via phase-1")
  expect(valueToNat(want, natGlobals) == 10, "addViaFn interpreter agrees")

# --- benchmark: interpreter vs Phase-1 compiled vs Phase-2 repr ---
# Per #19's framing, the comparison that matters is Phase 2 against
# Phase 1's compiled output; the interpreter is context. First
# measurement is a draft — printed, not asserted.
block:
  const iters = 200_000
  let bnd = testPostulateBindings()
  var t0 = cpuTime()
  var accI = 0
  for i in 0 ..< iters:
    let v = callValueFuncDir("", prog, "mulAdd",
      @[vInt(i), vInt(i + 1), vInt(i + 2)], bnd)
    accI += v.whnfIntVal
  let tInterp = cpuTime() - t0
  t0 = cpuTime()
  var acc1 = 0
  for i in 0 ..< iters:
    let v = eponymCompiled_mulAdd(@[vInt(i), vInt(i + 1), vInt(i + 2)], bnd)
    acc1 += v.whnfIntVal
  let tPhase1 = cpuTime() - t0
  t0 = cpuTime()
  var acc2 = 0
  for i in 0 ..< iters:
    acc2 += eponymCompiledRepr_mulAdd(i, i + 1, i + 2)
  let tPhase2 = cpuTime() - t0
  expect(accI == acc1 and acc1 == acc2, "benchmark accumulators agree")
  echo "bench mulAdd x", iters, ": interpreter ", tInterp.formatFloat(ffDecimal, 3),
    "s | phase-1 ", tPhase1.formatFloat(ffDecimal, 3),
    "s | phase-2 ", tPhase2.formatFloat(ffDecimal, 3), "s"
  echo "bench speedup vs interpreter: phase-1 ",
    (tInterp / tPhase1).formatFloat(ffDecimal, 1), "x, phase-2 ",
    (tInterp / tPhase2).formatFloat(ffDecimal, 1), "x; phase-2 vs phase-1 ",
    (tPhase1 / tPhase2).formatFloat(ffDecimal, 1), "x"

# --- benchmark: natElim fold (natDouble) ---
# The suc-chain argument is built once: natElim only fires on
# constructor-headed scrutinees, on all three sides. Result decoding
# (valueToNat walks the chain) is included in every side's time.
# n is small (100): the interpreter and the Phase-1 eliminator proc both
# evaluate Nat folds recursively, so deep folds hit the debug build's
# call-depth limit (a known runtime limitation, cf. test_nat_to_int).
block:
  const iters = 1000
  const n = 100
  let bnd = testPostulateBindings()
  let argV = natToValue(n, natGlobals)
  var t0 = cpuTime()
  var accI = 0
  for i in 0 ..< iters:
    let v = callValueFuncDir("", prog, "natDouble", @[argV], bnd)
    accI += valueToNat(v, natGlobals)
  let tInterp = cpuTime() - t0
  t0 = cpuTime()
  var acc1 = 0
  for i in 0 ..< iters:
    let v = eponymCompiled_natDouble(@[argV], bnd)
    acc1 += valueToNat(v, natGlobals)
  let tPhase1 = cpuTime() - t0
  t0 = cpuTime()
  var acc2 = 0
  for i in 0 ..< iters:
    acc2 += eponymCompiledRepr_natDouble(n)
  let tPhase2 = cpuTime() - t0
  expect(accI == acc1 and acc1 == acc2, "natDouble accumulators agree")
  echo "bench natDouble x", iters, " (n=", n, "): interpreter ",
    tInterp.formatFloat(ffDecimal, 3), "s | phase-1 ",
    tPhase1.formatFloat(ffDecimal, 3), "s | phase-2 ",
    tPhase2.formatFloat(ffDecimal, 3), "s"
  echo "bench natDouble speedup vs interpreter: phase-1 ",
    (tInterp / tPhase1).formatFloat(ffDecimal, 1), "x, phase-2 ",
    (tInterp / tPhase2).formatFloat(ffDecimal, 1), "x; phase-2 vs phase-1 ",
    (tPhase1 / tPhase2).formatFloat(ffDecimal, 1), "x"

echo "all Phase 2 codegen differential checks passed"

# --- end-to-end: typed wrappers reroute through the repr procs ---
# (Int fragment only: eponymBlock's runtimeType validation only accepts
# plain mappings for postulated types and nullary-constructor variants,
# so data-declared Nat/Bool with runtimeType(..., int) is rejected there
# — see the daily log 2026-10-21. The Nat/Bool repr tier is covered by
# differentialBlockRepr above, which drives compileBlockProcs directly.)
proc q0HostBump(value: int): int = value + 1
proc q0HostCombine(x, y: int): int = x + y

eponymBlock:
  postulate(Int, Univ)
  postulate(Opaque, Univ)
  runtimeType(Int, int)
  runtimeType(Opaque, int)
  postulate(q0HostBumpPostulate, Opaque -> Opaque)
  postulate(q0HostCombinePostulate, Opaque -> Opaque -> Opaque)
  bindPostulate(q0HostBumpPostulate, q0HostBump, Opaque, Opaque)
  bindPostulate(q0HostCombinePostulate, q0HostCombine,
    Opaque, Opaque, Opaque)
  proc wAdd(x: Int, y: Int): Int = addInt(x, y)
  proc wMulAdd(x: Int, y: Int, z: Int): Int = addInt(mulInt(x, y), z)
  proc wErased(proof {.erased.}: Int, x: Int): Int = x
  proc wErasedMiddle(x: Int, proof {.erased.}: Int, y: Int): Int =
    addInt(x, y)
  proc wErasedValueBacked(proof {.erased.}: Opaque, x: Opaque): Opaque =
    q0HostBumpPostulate(x)
  proc wErasedMiddleValueBacked(x: Opaque, proof {.erased.}: Opaque,
      y: Opaque): Opaque = q0HostCombinePostulate(x, y)
  proc wDouble(x: Int): Int = addInt(x, x)
  proc wQuad(x: Int): Int = wDouble(wDouble(x))

static:
  doAssert not compiles(wAdd("not an int"))
  doAssert not compiles(wQuad(1, 2))

when isMainModule:
  expect(wAdd(3, 4) == 7, "e2e wrapper wAdd")
  expect(wMulAdd(2, 3, 4) == 10, "e2e wrapper wMulAdd")
  var erasedWrapperResults = true
  var interleavedWrapperResults = true
  var erasedValueBackedResults = true
  var interleavedValueBackedResults = true
  for x in -100 .. 99:
    erasedWrapperResults = erasedWrapperResults and
      wErased(x * 17, x) == x
    interleavedWrapperResults = interleavedWrapperResults and
      wErasedMiddle(x, x * 17, x + 1) == 2 * x + 1
    erasedValueBackedResults = erasedValueBackedResults and
      wErasedValueBacked(x * 17, x) == x + 1
    interleavedValueBackedResults = interleavedValueBackedResults and
      wErasedMiddleValueBacked(x, x * 17, x + 1) == 2 * x + 1
  expect(erasedWrapperResults,
    "typed wrapper omits q0 arguments (200 values)")
  expect(interleavedWrapperResults,
    "typed wrapper omits interleaved q0 arguments (200 values)")
  expect(erasedValueBackedResults,
    "Phase-1 typed wrapper omits leading q0 argument (200 values)")
  expect(interleavedValueBackedResults,
    "Phase-1 typed wrapper omits interleaved q0 argument (200 values)")
  expect(wQuad(21) == 84, "e2e wrapper wQuad")
  for x in [-10, 0, 7]:
    for y in [-3, 0, 9]:
      expect(wAdd(x, y) == x + y, "e2e wAdd agrees with (+)")
  echo "all Phase 2 end-to-end wrapper checks passed"
