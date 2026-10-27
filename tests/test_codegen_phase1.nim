## Differential tests for the Phase 1 codegen backend (Issue #329).
##
## A `differentialBlock` macro elaborates a surface program at compile time
## and emits the real Phase-1 compiled procs; the test body then compares
## each compiled proc against the interpreter (`callValueFunc` /
## `callDefValueWithBindings`) on the same arguments, structurally over
## `whnf` (compiled `syn` is approximate by design — semantics live in
## `whnf`). Effectful postulates are counted on both sides to catch
## duplicated or dropped effects.

import std/[tables, macros, sequtils, strutils]
import eponym_init
import eponym_embed
import elab
import codegen

proc expect(ok: bool, message: string) =
  if not ok:
    quit("FAIL: " & message, 1)
  echo "ok: ", message

macro differentialBlock(src: static string, srcFile: static string): untyped =
  ## Elaborate `src` at compile time and emit one `eponymCompiled_<name>`
  ## proc per eligible definition, using the real Phase-1 compiler.
  ## `srcFile` is the calling file (for generated source positions).
  ## Also emits `testPostulateBindings()` which binds every postulate-like
  ## global to a neutral value, so the interpreter and compiled code agree
  ## on unbound postulates (both see neutrals instead of the interpreter
  ## raising).
  let checked = elabCheckDirStateAll(src, "")
  var userLines = initTable[string, int]()
  for d in checked.defs:
    userLines[d.name] = 1
  let cgBlock = compileBlockProcs(checked.defs, checked.globals, "", src,
    srcFile, userLines)
  if cgBlock.report["add42"].tier != cgtValue or
      not cgBlock.report["add42"].reason.contains("Phase 2 unavailable"):
    error("codegen report should identify add42 as Phase 1 Value code")
  if cgBlock.report["natElimPartial"].tier != cgtValue or
      not cgBlock.report["natElimPartial"].reason.contains("Phase 2 unavailable"):
    error("codegen report should identify natElimPartial as Phase 1 Value code (eta-expanded, issue #407)")
  var isolatedDefs: seq[ElabDef] = @[]
  for d in checked.defs:
    if d.name == "add42": isolatedDefs.add(d)
  let isolated = compileBlockProcs(isolatedDefs, checked.globals, "", src,
    srcFile, userLines)
  if "fortyTwo" notin isolated.report["add42"].slowPaths:
    error("codegen report should expose a cross-block runtime slow path")
  result = newStmtList()
  for p in cgBlock.procs:
    result.add(p)
    # Issue #329 acceptance: generated definition procs carry user source
    # positions (eliminator procs and forward declarations keep the macro
    # call-site info, which still names the user's file).
    if p.kind == nnkProcDef and p[0].kind == nnkPostfix and
        ($p[0][1]).startsWith("eponymCompiled_"):
      let li = lineInfoObj(p)
      if not li.filename.endsWith("test_codegen_phase1.nim"):
        error("compiled proc " & $p[0][1] &
          " missing user source position (got " & li.filename & ")")
  # Bind postulates to neutrals for the differential harness.
  var bindStmts = newStmtList()
  let bndSym = genSym(nskVar, "testBnd")
  bindStmts.add(newVarStmt(bndSym, newCall(bindSym"initRuntimeBindings")))
  for name, e in checked.globals.pairs:
    if e.tm != nil and e.tm.kind == tR and not e.tm.refIsDefn and
        not e.isElim and not e.isDataConstructor:
      # postulate or type former: bind to a neutral
      let refIdLit = newLit(e.tm.refId)
      bindStmts.add(newTree(nnkAsgn,
        newTree(nnkBracketExpr, bndSym, refIdLit),
        newCall(bindSym"postulateValue", refIdLit,
          newCall(bindSym"initRuntimeBindings"))))
    elif e.isDataConstructor:
      # data constructors: also bind to neutrals (they're postulates too)
      let refIdLit = newLit(e.tm.refId)
      bindStmts.add(newTree(nnkAsgn,
        newTree(nnkBracketExpr, bndSym, refIdLit),
        newCall(bindSym"postulateValue", refIdLit,
          newCall(bindSym"initRuntimeBindings"))))
  bindStmts.add(bndSym)
  let bindingsProc = quote do:
    proc testPostulateBindings*(): RuntimeBindings =
      `bindStmts`
  result.add(bindingsProc)

proc whnfEq(a, b: Value): bool  # forward

proc spineEq(a, b: Value): bool =
  if a.whnfSpineLen != b.whnfSpineLen: return false
  for i in 0 ..< a.whnfSpineLen:
    if a.whnfSpineKind(i) != b.whnfSpineKind(i): return false
    if a.whnfSpineKind(i) == eApp and
        not whnfEq(a.whnfSpineArg(i), b.whnfSpineArg(i)):
      return false
  true

proc whnfEq(a, b: Value): bool =
  ## Structural equality on weak-head normal forms, ignoring `syn`.
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.whnfKind != b.whnfKind: return false
  case a.whnfKind
  of wInt: a.whnfIntVal == b.whnfIntVal
  of wNatLit: a.whnfNatLitVal == b.whnfNatLitVal
  of wNatSing: a.whnfNatSingVal == b.whnfNatSingVal
  of wConst: a.whnf.c == b.whnf.c
  of wType: a.whnf.lvl == b.whnf.lvl
  of wPair:
    whnfEq(fstValue(a), fstValue(b)) and
      whnfEq(sndValue(a), sndValue(b))
  of wRef: a.whnfRefId == b.whnfRefId and spineEq(a, b)
  else: false

proc whnfEqExt(a, b: Value, bnd: RuntimeBindings, depth: int = 3): bool =
  ## Structural equality like `whnfEq`, but closures (`wLam`) are compared
  ## by a bounded extensionality probe: apply both to the same fresh neutral
  ## and compare the results. Needed for stuck-eliminator spines, which
  ## carry the motive/step closures — semantically equal across the
  ## compiled/interpreter boundary but representationally different (host
  ## closure vs `ScoVal`), so plain structural comparison gives up on them.
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.whnfKind != b.whnfKind: return false
  case a.whnfKind
  of wLam:
    if depth <= 0: return false
    let probe = neutralVar(7)
    whnfEqExt(vAppWithBindings(a, probe, bnd),
              vAppWithBindings(b, probe, bnd), bnd, depth - 1)
  of wRef:
    if a.whnfRefId != b.whnfRefId: return false
    if a.whnfSpineLen != b.whnfSpineLen: return false
    for i in 0 ..< a.whnfSpineLen:
      if a.whnfSpineKind(i) != b.whnfSpineKind(i): return false
      if a.whnfSpineKind(i) == eApp and
          not whnfEqExt(a.whnfSpineArg(i), b.whnfSpineArg(i), bnd, depth):
        return false
    true
  else:
    whnfEq(a, b)

const prog = """postulate(Int, Univ)
proc fortyTwo : Int = 42
proc add42 (n : Int) : Int = addInt n fortyTwo
proc twice (x : Int) : Int = addInt x x
proc nestedLet (x : Int) : Int =
  let y : Int = addInt x x in addInt y x
proc higher (f : Int -> Int) (x : Int) : Int = f (f x)
proc twiceVal : Int -> Int = twice
proc pairMk (a : Int) (b : Int) : Sig(u: Int, Int) = (a, b)
proc pairFst (p : Sig(u: Int, Int)) : Int = fst p
proc const42 (x : Int) : Int = subInt (addInt x fortyTwo) x
proc addTwice (x : Int) : Int = add42 (twice x)

postulate(Nat, Univ)
postulate(zero, Nat)
postulate(suc, Nat -> Nat)
elim(natElim, Pi(C: Nat -> Univ, C zero -> Pi(n: Nat, C n -> C (suc n)) -> Pi(m: Nat, C m)))
red(natElim C z s zero   , z)
red(natElim C z s (suc n), s n (natElim C z s n))
proc two : Nat = suc (suc zero)
proc add3 (n : Nat) : Nat =
  natElim (lam(u: Nat) => Nat) (suc (suc (suc zero))) (lam(p: Nat) => lam(ih: Nat) => suc ih) n
proc isZero (n : Nat) : Nat =
  natElim (lam(u: Nat) => Nat) zero (lam(p: Nat) => lam(ih: Nat) => p) n
proc natElimPartial (C : Nat -> Univ) (z : C zero)
    (s : Pi(n: Nat, C n -> C (suc n))) : Pi(m: Nat, C m) =
  natElim C z s
proc motiveNatLam : Nat -> Univ = lam(u: Nat) => Nat
proc sucStepFn : Pi(p: Nat, Nat -> Nat) =
  lam(p: Nat) => lam(ih: Nat) => suc ih
proc applyToTwo (f : Pi(m: Nat, Nat)) : Nat = f two
proc natElimBare : Pi(C: Nat -> Univ, C zero -> Pi(n: Nat, C n -> C (suc n)) -> Pi(m: Nat, C m)) =
  natElim

data(Vec, [A : Univ], Nat -> Univ) where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc cloneVec {A : Univ} {n : Nat} (xs : Vec A n) : Vec A n =
  vecElim A (lam(i: Nat) => lam(v: Vec A i) => Vec A i)
    (nil A)
    (lam(i: Nat) => lam(x: A) => lam(xs2: Vec A i) => lam(ih: Vec A i) => cons A i x ih)
    n xs
proc nilIntVec : Vec Int zero = nil Int
proc oneIntVec (x : Int) : Vec Int (suc zero) =
  cons Int zero x (nil Int)

postulate(BoolD, Univ)
postulate(trueD, BoolD)
postulate(falseD, BoolD)
elim(boolElimD, Pi(C: BoolD -> Univ, C trueD -> C falseD -> Pi(b: BoolD, C b)))
red(boolElimD C t f trueD , t)
red(boolElimD C t f falseD, f)
proc notFn (b : BoolD) : BoolD =
  boolElimD (lam(u: BoolD) => BoolD) falseD trueD b

postulate(tick, Int -> Int)
proc twiceTicked (n : Int) : Int = addInt (tick n) (tick n)
postulate(mystery, Nat)
proc stuckAdd (n : Nat) : Nat =
  natElim (lam(u: Nat) => Nat) n (lam(p: Nat) => lam(ih: Nat) => suc ih) mystery
postulate(boom, Int -> Int)
proc boomCaller (x : Int) : Int = addInt (boom x) (boom x)
"""

differentialBlock(prog, currentSourcePath())

# A generated integer refId must still resolve to the same global name in the
# current elaboration. Simulate a stale baked table and ensure codegen fails
# before emitting any proc that could silently dispatch to another definition.
block:
  let checked = elabCheckDirStateAll(prog, "")
  let originalId = checked.globals["two"].tm.refId
  var changedGlobals = checked.globals
  var changed = changedGlobals["two"]
  changed.tm.refId = originalId + 1_000_000
  changedGlobals["two"] = changed
  var bakedIds = initTable[int, string]()
  bakedIds[originalId] = "two"
  var rejected = false
  try:
    validateBakedRefIds(changedGlobals, bakedIds)
  except CgUnsupported as e:
    rejected = "expected global 'two'" in e.msg
  expect(rejected, "stale baked refId is rejected by name")

macro checkElimTranslation(src: static string): untyped =
  ## Exercise translation validation during macro expansion, at the same
  ## stage that generated procedures are finalized.
  let checked = elabCheckDirStateAll(src, "")
  var userLines = initTable[string, int]()
  for d in checked.defs:
    userLines[d.name] = 1
  let generated = compileBlockProcs(checked.defs, checked.globals, "", src,
    currentSourcePath(), userLines)
  if "natElimPartial" notin generated.compiled:
    error("partially applied natElim should compile via eta-expansion (issue #407)")
  let ctx = buildCodegenCtx(checked.globals, "", src)
  let elimId = checked.globals["natElim"].tm.refId
  let elim = ctx.refs[elimId]
  var emitted: NimNode
  for p in generated.procs:
    if p.kind == nnkProcDef and p[0].kind == nnkPostfix and
        $p[0][1] == elimProcName("natElim") and p[6].kind != nnkEmpty:
      emitted = p
      break
  if emitted.isNil:
    error("natElim compiled body is missing")
  validateElimDispatchCoverage(elim, emitted)

  proc findCtorDispatch(node: NimNode): NimNode =
    if node.isNil: return nil
    if node.kind == nnkCaseStmt and node.len > 0 and
        node[0].kind == nnkCall and node[0].len > 0 and
        $node[0][0] == "whnfRefId":
      return node
    for child in node:
      result = findCtorDispatch(child)
      if not result.isNil: return

  var corrupted = copyNimTree(emitted)
  let dispatch = findCtorDispatch(corrupted)
  if dispatch.isNil or dispatch.len <= 2:
    error("natElim dispatch is missing constructor branches")
  dispatch.del(1)  # Remove one registered constructor branch.
  var rejected = false
  try:
    validateElimDispatchCoverage(elim, corrupted)
  except CgUnsupported as e:
    rejected = "does not cover registered constructor" in e.msg
  if not rejected:
    error("translation validation accepted a missing constructor branch")
  corrupted = copyNimTree(emitted)
  let badShapeDispatch = findCtorDispatch(corrupted)
  let firstBranch = badShapeDispatch[1]
  var shapeGuard: NimNode
  proc findIfExpr(node: NimNode) =
    if node.isNil or not shapeGuard.isNil: return
    if node.kind == nnkIfExpr:
      shapeGuard = node
      return
    for child in node:
      findIfExpr(child)
  findIfExpr(firstBranch)
  if shapeGuard.isNil or shapeGuard[0].kind != nnkElifBranch:
    error("generated constructor branch is missing its shape guard")
  shapeGuard[0][0] = newLit(true)
  rejected = false
  try:
    validateElimDispatchCoverage(elim, corrupted)
  except CgUnsupported as e:
    rejected = "does not check its expected spine length" in e.msg or
      "has no spine-shape guard" in e.msg
  if not rejected:
    error("translation validation accepted a branch without a spine-shape guard")
  result = quote do:
    echo "ok: Phase 1 eliminator dispatch validates rule coverage and spine guards"

checkElimTranslation(prog)

proc callByName(name: string, args: seq[Value]): Value =
  case name
  of "add42": eponymCompiled_add42(args, testPostulateBindings())
  of "twice": eponymCompiled_twice(args, testPostulateBindings())
  of "nestedLet": eponymCompiled_nestedLet(args, testPostulateBindings())
  of "higher": eponymCompiled_higher(args, testPostulateBindings())
  of "twiceVal": eponymCompiled_twiceVal(args, testPostulateBindings())
  of "pairMk": eponymCompiled_pairMk(args, testPostulateBindings())
  of "pairFst": eponymCompiled_pairFst(args, testPostulateBindings())
  of "const42": eponymCompiled_const42(args, testPostulateBindings())
  of "addTwice": eponymCompiled_addTwice(args, testPostulateBindings())
  of "two": eponymCompiled_two(args, testPostulateBindings())
  of "add3": eponymCompiled_add3(args, testPostulateBindings())
  of "isZero": eponymCompiled_isZero(args, testPostulateBindings())
  of "cloneVec": eponymCompiled_cloneVec(args, testPostulateBindings())
  of "notFn": eponymCompiled_notFn(args, testPostulateBindings())
  of "twiceTicked": eponymCompiled_twiceTicked(args, testPostulateBindings())
  of "stuckAdd": eponymCompiled_stuckAdd(args, testPostulateBindings())
  of "boomCaller": eponymCompiled_boomCaller(args, testPostulateBindings())
  of "fortyTwo": eponymCompiled_fortyTwo(args, testPostulateBindings())
  else: raise newException(ValueError, "unknown def " & name)

proc checkInt(name: string, args: seq[int]) =
  ## Compare compiled vs interpreter on Int arguments.
  let argVals = args.mapIt(vInt(it))
  let got = callByName(name, argVals)
  let want = callValueFuncDir("", prog, name, argVals,
    testPostulateBindings())
  expect(whnfEq(got, want),
    name & " compiled agrees with interpreter on " & $args)

# --- first-order Int definitions ---
for n in [-3, 0, 1, 41]:
  checkInt("add42", @[n])
for n in [0, 7, 21]:
  checkInt("twice", @[n])
  checkInt("nestedLet", @[n])
  checkInt("const42", @[n])
  checkInt("addTwice", @[n])
  
# pair construction then projection, differentially
block:
  let pairVal = eponymCompiled_pairMk(@[vInt(3), vInt(4)],
    testPostulateBindings())
  let wantPair = callValueFuncDir("", prog, "pairMk", @[vInt(3), vInt(4)],
    testPostulateBindings())
  expect(whnfEq(pairVal, wantPair), "pairMk value agrees")
  let gotFst = eponymCompiled_pairFst(@[pairVal], testPostulateBindings())
  let wantFst = callValueFuncDir("", prog, "pairFst", @[wantPair], testPostulateBindings())
  expect(gotFst.whnfKind == wInt and gotFst.whnfIntVal == 3,
    "compiled pairFst projects 3")
  expect(whnfEq(gotFst, wantFst), "pairFst agrees")

# higher-order: pass a compiled function value as the argument
block:
  let bnd = testPostulateBindings()
  let twiceFn = eponymCompiled_twice(@[], bnd)
  let twiceFnI = callValueFuncDir("", prog, "twiceVal", @[], testPostulateBindings())
  let got = eponymCompiled_higher(@[twiceFn, vInt(5)], bnd)
  let want = callValueFuncDir("", prog, "higher", @[twiceFnI, vInt(5)],
    testPostulateBindings())
  expect(got.whnfKind == wInt and got.whnfIntVal == 20, "higher-order applies")
  expect(whnfEq(got, want), "higher agrees")

# partial application: twiceVal's value applied later
block:
  let bnd = testPostulateBindings()
  let f = eponymCompiled_twiceVal(@[], bnd)
  let fI = callValueFuncDir("", prog, "twiceVal", @[], testPostulateBindings())
  let got = vAppWithBindings(f, vInt(21), bnd)
  let want = vAppWithBindings(fI, vInt(21), bnd)
  expect(got.whnfKind == wInt and got.whnfIntVal == 42,
    "partial application applies")
  expect(whnfEq(got, want), "partial application agrees")

# --- Issue #407: partially-applied eliminator eta-expands to a closure ---
block:
  let bnd = testPostulateBindings()
  let cVal = callValueFuncDir("", prog, "motiveNatLam", @[], bnd)
  let zVal = callValueFuncDir("", prog, "two", @[], bnd)
  let sVal = callValueFuncDir("", prog, "sucStepFn", @[], bnd)
  # compiled closure from the partial application `natElim C z s`
  let closC = eponymCompiled_natElimPartial(@[cVal, zVal, sVal], bnd)
  # interpreter's closure from the same partial application
  let closI = callValueFuncDir("", prog, "natElimPartial",
    @[cVal, zVal, sVal], bnd)
  let got = vAppWithBindings(closC, zVal, bnd)
  let want = vAppWithBindings(closI, zVal, bnd)
  expect(whnfEq(got, want),
    "eta-expanded natElim closure agrees with interpreter")
  # suc^2 (suc^2 zero) = suc^4 zero: count the suc spine
  var depth = 0
  var cur = got
  while cur.whnfKind == wRef and cur.whnfSpineLen == 1:
    inc depth
    cur = cur.whnfSpineArg(0)
  expect(depth == 4 and cur.whnfKind == wRef and cur.whnfSpineLen == 0,
    "closure computes 4 as a suc-chain")
  # the closure is a first-class value: pass it to another compiled def
  let got2 = eponymCompiled_applyToTwo(@[closC], bnd)
  let want2 = callValueFuncDir("", prog, "applyToTwo", @[closI], bnd)
  expect(whnfEq(got2, want2), "closure passed to compiled def agrees")

# --- Issue #407: bare eliminator reference eta-expands fully ---
block:
  let bnd = testPostulateBindings()
  let cVal = callValueFuncDir("", prog, "motiveNatLam", @[], bnd)
  let zVal = callValueFuncDir("", prog, "two", @[], bnd)
  let sVal = callValueFuncDir("", prog, "sucStepFn", @[], bnd)
  var got = eponymCompiled_natElimBare(@[], bnd)
  var want = callValueFuncDir("", prog, "natElimBare", @[], bnd)
  for v in [cVal, zVal, sVal, zVal]:
    got = vAppWithBindings(got, v, bnd)
    want = vAppWithBindings(want, v, bnd)
  expect(whnfEq(got, want), "bare natElim reference agrees with interpreter")

# --- Nat eliminator over suc-chains ---
block:
  let twoVal = callValueFuncDir("", prog, "two", @[], testPostulateBindings())
  let twoValC = eponymCompiled_two(@[], testPostulateBindings())
  expect(whnfEq(twoValC, twoVal), "two agrees")
  for (name, argSrc) in [("add3", twoVal), ("isZero", twoVal)]:
    let got = callByName(name, @[argSrc])
    let want = callValueFuncDir("", prog, name, @[argSrc],
      testPostulateBindings())
    expect(whnfEq(got, want), name & " over suc-chain agrees")
  # add3 (suc (suc zero)) = suc^5 zero: count the suc spine
  let got3 = eponymCompiled_add3(@[twoVal], testPostulateBindings())
  var depth = 0
  var cur = got3
  while cur.whnfKind == wRef and cur.whnfSpineLen == 1:
    inc depth
    cur = cur.whnfSpineArg(0)
  expect(depth == 5 and cur.whnfKind == wRef and cur.whnfSpineLen == 0,
    "add3 computes 5 as a suc-chain")

# --- dependent Vec motive: every constructor branch agrees with the interpreter ---
block:
  let bnd = testPostulateBindings()
  let globals = getGlobals(prog)
  let intTy = postulateValue(globals["Int"].tm.refId, bnd)
  let zero = postulateValue(globals["zero"].tm.refId, bnd)
  let one = vAppWithBindings(
    postulateValue(globals["suc"].tm.refId, bnd), zero, bnd)
  let empty = callValueFuncDir("", prog, "nilIntVec", @[], bnd)
  let singleton = callValueFuncDir("", prog, "oneIntVec", @[vInt(17)], bnd)
  for (label, index, vector) in [("empty", zero, empty),
                                 ("singleton", one, singleton)]:
    let args = @[intTy, index, vector]
    let got = eponymCompiled_cloneVec(args, testPostulateBindings())
    let want = callValueFuncDir("", prog, "cloneVec", args,
      testPostulateBindings())
    expect(whnfEq(got, want), "dependent Vec clone agrees on " & label)

# --- Bool eliminator ---
block:
  let rtGlobals = getGlobals(prog)
  let trueId = rtGlobals["trueD"].tm.refId
  let falseId = rtGlobals["falseD"].tm.refId
  let bnd = testPostulateBindings()
  let trueVal = postulateValue(trueId, bnd)
  let falseVal = postulateValue(falseId, bnd)
  let gotT = eponymCompiled_notFn(@[trueVal], bnd)
  let gotF = eponymCompiled_notFn(@[falseVal], bnd)
  let wantT = callValueFuncDir("", prog, "notFn", @[trueVal], testPostulateBindings())
  let wantF = callValueFuncDir("", prog, "notFn", @[falseVal], testPostulateBindings())
  expect(gotT.whnfKind == wRef and gotT.whnfRefId == falseId, "not true = false")
  expect(gotF.whnfKind == wRef and gotF.whnfRefId == trueId, "not false = true")
  expect(whnfEq(gotT, wantT) and whnfEq(gotF, wantF), "notFn agrees")

# --- stuck eliminator: neutral scrutinee stays neutral on both sides ---
block:
  let twoVal = callValueFuncDir("", prog, "two", @[], testPostulateBindings())
  let got = eponymCompiled_stuckAdd(@[twoVal], testPostulateBindings())
  let want = callValueFuncDir("", prog, "stuckAdd", @[twoVal], testPostulateBindings())
  expect(got.whnfKind == wRef, "stuck eliminator stays neutral (compiled)")
  expect(whnfEqExt(got, want, testPostulateBindings()),
    "stuck eliminator agrees")

# --- effectful postulate: effects happen exactly once per call on each side ---
block:
  let rtGlobals = getGlobals(prog)
  let tickId = rtGlobals["tick"].tm.refId
  let defs = getDefs(prog)
  let d = findDef(defs, "twiceTicked")
  var callsC = 0
  var bndC = testPostulateBindings()
  bndC[tickId] = vHostFunc(proc(x: Value): Value =
    inc callsC
    x)
  var callsI = 0
  var bndI = testPostulateBindings()
  bndI[tickId] = vHostFunc(proc(x: Value): Value =
    inc callsI
    x)
  let got = eponymCompiled_twiceTicked(@[vInt(7)], bndC)
  let want = callDefValueWithBindings(d, @[vInt(7)], bndI)
  expect(callsC == 2, "compiled calls tick exactly twice, got " & $callsC)
  expect(callsI == 2, "interpreter calls tick exactly twice, got " & $callsI)
  expect(whnfEq(got, want), "twiceTicked agrees")

# --- source positions: runtime errors map back to the test file ---
block:
  let rtGlobals = getGlobals(prog)
  let boomId = rtGlobals["boom"].tm.refId
  var bnd = testPostulateBindings()
  bnd[boomId] = vHostFunc(proc(x: Value): Value =
    raise newException(ValueError, "boom host failure"))
  var mapped = false
  try:
    discard eponymCompiled_boomCaller(@[vInt(1)], bnd)
  except ValueError as e:
    mapped = "test_codegen_phase1" in getStackTrace(e)
  expect(mapped, "runtime error stack trace maps to the test file")

# Generated Value application must never escape through the interpreter for a
# partially applied eliminator. Such a shape needs a generated eliminator
# dispatch proc, or compilation should have rejected it.
block:
  var supply = Supply()
  let partialEliminator = newRedRef(supply, vType(0), 2).refVal
  var rejected = false
  try:
    discard vCompiledAppWithBindings(partialEliminator, vInt(1),
      initRuntimeBindings())
  except ValueError as e:
    rejected = "compiled Value application reached a partial eliminator" in
      e.msg
  expect(rejected, "compiled Value application rejects partial eliminators")

echo "all Phase 1 codegen differential checks passed"
