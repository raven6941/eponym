## Differential tests + benchmark for the Phase 2 representation backend
## (Issue #330, v1 Int fragment).
##
## A `differentialBlockRepr` macro elaborates a surface program at compile
## time with an `Int -> int` runtime mapping and emits both the Phase-1
## Value procs and the Phase-2 repr procs (`eponymCompiledRepr_<name>`).
## The test body checks each repr proc against the interpreter
## (`callValueFuncDir`) and against its Phase-1 compiled twin, then
## benchmarks interpreter vs Phase-1 vs Phase-2 on the same workload (per
## #19's framing, Phase 2 is measured against Phase 1's compiled output).

import std/[tables, macros, sequtils, strutils, times]
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
  ## Elaborate `src` at compile time with an `Int -> int` runtimeType
  ## mapping and emit Phase-1 + Phase-2 procs via the real compiler.
  ## Also emits `reprCompiledNames()` (which defs got a repr proc) and
  ## `testPostulateBindings()` (neutral bindings for the differential
  ## harness, as in the Phase-1 suite).
  let checked = elabCheckDirStateAll(src, "")
  var userLines = initTable[string, int]()
  for d in checked.defs:
    userLines[d.name] = 1
  let intMapping = HostRuntimeType(eponymName: "Int", nimType: ident"int",
    isRuntimeVector: false, isRuntimeList: false, isRuntimeOption: false,
    isRuntimeVariant: false, isRuntimeCodec: false,
    isGenericTypeWitnessable: true, encoder: nil, decoder: nil)
  let cgBlock = compileBlockProcs(checked.defs, checked.globals, "", src,
    srcFile, userLines, @[intMapping])
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

# --- fragment boundaries: these get Phase-1 procs but no repr procs ---
expect("tickTwice" notin reprCompiledNames(),
  "postulate-calling def has no repr proc")
expect("higher" notin reprCompiledNames(),
  "higher-order def has no repr proc")
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

echo "all Phase 2 codegen differential checks passed"

# --- end-to-end: typed wrappers reroute through the repr procs ---
eponymBlock:
  postulate(Int, Univ)
  runtimeType(Int, int)
  proc wAdd(x: Int, y: Int): Int = addInt(x, y)
  proc wMulAdd(x: Int, y: Int, z: Int): Int = addInt(mulInt(x, y), z)
  proc wDouble(x: Int): Int = addInt(x, x)
  proc wQuad(x: Int): Int = wDouble(wDouble(x))

static:
  doAssert not compiles(wAdd("not an int"))
  doAssert not compiles(wQuad(1, 2))

when isMainModule:
  expect(wAdd(3, 4) == 7, "e2e wrapper wAdd")
  expect(wMulAdd(2, 3, 4) == 10, "e2e wrapper wMulAdd")
  expect(wQuad(21) == 84, "e2e wrapper wQuad")
  for x in [-10, 0, 7]:
    for y in [-3, 0, 9]:
      expect(wAdd(x, y) == x + y, "e2e wAdd agrees with (+)")
  echo "all Phase 2 end-to-end wrapper checks passed"
