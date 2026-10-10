## Issue #94: QTT erasure in staged residuals.
##
## Differential tests: residuals with 0-quantity binders evaluate to the same
## value as the unstaged interpreter (evalSym), while dropping the erased
## binders from the residual code. Plus a benchmark of the erasure win
## (residual size + wall-clock vs the non-erased residual).
##
## Corpus convention: `addErased : (0 n : Nat) -> Nat -> Nat` stands in for
## `length : (0 n : Nat) -> Vec A n -> Nat` — n is the erased index. (Vec
## itself is not in the tagless core; the erasure mechanism is identical.)

import std/[tables, times, strutils]
import ett
import ett_staged
import preterm  # Quantity, q0/q1/qOmega

let ev = evalSym
let st = stagedSym()
let addOp = primTable["add"]
let unitS = st.cUnit()
let unitV = ev.cUnit()

proc natV(n: int): Value = Value(kind: vkNat, natV: n)

# addErased : (0 n : Nat) -> Nat -> Nat  =  \(0 n). \m. m + 10
proc addErasedS(): SVal =
  cLamQ(unitS, q0, proc(n: SVal): SVal =
    st.cLam(unitS, proc(m: SVal): SVal =
      applyPrim(addOp, @[m, natLit(10)])))

proc addErasedV(): Value =
  ev.cLam(unitV, proc(n: Value): Value =
    ev.cLam(unitV, proc(m: Value): Value =
      natV(m.natV + 10)))

# addBoth : Nat -> Nat -> Nat  =  \n. \m. n + m  (qOmega: uses its argument)
proc addBothS(): SVal =
  st.cLam(unitS, proc(n: SVal): SVal =
    st.cLam(unitS, proc(m: SVal): SVal =
      applyPrim(addOp, @[n, m])))

proc check(name: string, cond: bool) =
  if not cond:
    raise newException(AssertionDefect, "FAILED: " & name)
  echo "ok: ", name

echo "=== Test 1: applied erasure — residual drops the erased argument ==="
let nD = dynamicVar("n")
let mD = dynamicVar("m")
let r1 = st.cApp(st.cApp(addErasedS(), nD), mD)
echo "    residual: ", $r1
echo "    nodes: ", countNodes(r1)
check("applied q0: residual mentions no n", countNodes(r1) == 2)  # (add m 10)
let env1 = {"n": natV(5), "m": natV(7)}.toTable
let got1 = evalSVal(r1, env1)
let want1 = ev.cApp(ev.cApp(addErasedV(), natV(5)), natV(7))
check("applied q0: staged == unstaged",
  got1.kind == vkNat and got1.natV == 17 and want1.natV == 17)

echo "=== Test 2: reifyLam drops the q0 binder, keeps qOmega ==="
let rq0 = reifyLam(addErasedS(), unitS)
echo "    reified q0: ", $rq0
check("reified q0 prints no binder", ($(rq0)).startsWith("(lam:q0 []"))
let rW = reifyLam(addBothS(), unitS)
echo "    reified w : ", $rW
check("reified qOmega keeps its binder", ($(rW)).contains("[lam"))

echo "=== Test 3: residual call sites drop the erased argument ==="
proc primTower(depth: int, x: SVal): SVal =
  ## An expensive residual: a depth-deep tower of add-nodes over x.
  var acc = x
  for _ in 1 .. depth: acc = applyPrim(addOp, @[acc, natLit(1)])
  acc
let bigArg = primTower(50, dynamicVar("z"))
let bigNodes = countNodes(bigArg)
echo "    erased argument residual nodes: ", bigNodes
let r3 = st.cApp(rq0, bigArg)          # residual redex against q0 lambda
let r3m = st.cApp(r3, mD)             # ... then applied to m
echo "    after call-site drop: ", $r3m, "  nodes: ", countNodes(r3m)
check("call site drops the 50-node erased argument", countNodes(r3m) == 2)
let got3 = evalSVal(r3m, {"m": natV(3), "z": natV(99)}.toTable)
check("dropped-arg residual still evaluates correctly",
  got3.kind == vkNat and got3.natV == 13)

echo "=== Test 4: boundary check fires loudly on misuse ==="
var raisedApp = false
try:
  discard st.cApp(
    cLamQ(unitS, q0, proc(n: SVal): SVal = st.cPair(n, st.cTt())),
    dynamicVar("n"))
except ValueError as e:
  raisedApp = true
  echo "    cApp misuse raised: ", e.msg
check("cApp boundary check fires", raisedApp)
var raisedReify = false
try:
  discard reifyLam(
    cLamQ(unitS, q0, proc(n: SVal): SVal = st.cPair(n, st.cTt())), unitS)
except ValueError as e:
  raisedReify = true
  echo "    reifyLam misuse raised: ", e.msg
check("reifyLam boundary check fires", raisedReify)

echo "=== Test 5: quantities thread through residual types (binder kept) ==="
let tq0 = cPiQ(unitS, q0, proc(n: SVal): SVal = unitS)
echo "    q0 Pi residual: ", $tq0
check("q0 Pi keeps its binder but records qty",
  ($(tq0)).contains(":q0") and ($(tq0)).contains("[pi"))
let tq1 = cSigmaQ(unitS, q1, proc(n: SVal): SVal = unitS)
check("q1 Sigma records qty", ($(tq1)).contains(":q1"))

echo "=== Test 6: qOmega / q1 application is unaffected ==="
let r6 = st.cApp(st.cApp(addBothS(), nD), mD)
echo "    residual: ", $r6
let got6 = evalSVal(r6, env1)
check("qOmega application stages and evaluates",
  got6.kind == vkNat and got6.natV == 12)

echo ""
echo "=== Benchmark: erasure win (issue #94, step 5) ==="
echo "    An expensive erased argument: fib(24) computed per call."
proc fib(n: int): int =
  if n < 2: n else: fib(n-1) + fib(n-2)
const M = 40
# Unstaged (non-erased): the interpreter evaluates the argument every call,
# even though the function ignores it.
let tUn = cpuTime()
var accU = 0
for i in 1 .. M:
  let r = ev.cApp(ev.cApp(addErasedV(), natV(fib(24))), natV(i))
  accU += r.natV
let unTime = cpuTime() - tUn
# Staged with erasure: the argument is dropped at staging time — the caller
# never even computes it (a dummy is passed; cApp discards it uninspected).
let tStage = cpuTime()
let stagedFn = st.cApp(addErasedS(), natLit(0))  # erased arg: dummy, dropped
let stagedBody = st.cApp(stagedFn, mD)
let stageTime = cpuTime() - tStage
echo "    staged residual: ", $stagedBody, "  nodes: ", countNodes(stagedBody)
let tSt = cpuTime()
var accS = 0
for i in 1 .. M:
  accS += evalSVal(stagedBody, {"m": natV(i)}.toTable).natV
let stTime = cpuTime() - tSt
check("benchmark agreement", accU == accS)
echo "    unstaged (evaluates fib(24) x", M, "): ", unTime * 1000, " ms"
echo "    staged residual eval x", M, ": ", stTime * 1000, " ms",
     "  (+ one-time stage ", stageTime * 1000, " ms)"
echo "    wall-clock speedup: ", unTime / stTime, "x"
echo "    residual nodes (erased): ", countNodes(stagedBody),
     " vs non-erased unstaged closure: takes n every call"

echo ""
echo "ALL #94 CHECKS PASSED"
