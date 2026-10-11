## End-to-end validation for Phase 2 (#17): ETT-specific staging rules.
##
## - Stages real ETT terms (twice / const / pairSwap from eponym.nim, built
##   once polymorphically over Sym[R]) and checks the staged result
##   evaluates to the same Value as the unstaged interpreter (evalSym).
## - Prints the residual: only ETT former nodes (var/app/pair/...); no
##   staging machinery (no SVal/Rep/Value wrappers) appears in it.
## - Benchmarks staging-time specialization: static beta-reductions and
##   static subterm evaluation move out of the dynamic loop.

import std/[tables, times]
import eponym
import ett_staged  # was staging/ett_staged (stale path); the module lives in tests/

# --- structural equality on values (neutrals compared by id) ---

proc eqVal(a, b: Value): bool =
  if a.kind != b.kind: return false
  case a.kind
  of vkStar, vkUnit, vkTt, vkEmpty: true
  of vkPi, vkSigma, vkLam: false  # not produced by these demos
  of vkPair: eqVal(a.fstV, b.fstV) and eqVal(a.sndV, b.sndV)
  of vkNat: a.natV == b.natV
  of vkNeutral:
    a.neutId == b.neutId and a.spine.len == b.spine.len

proc neutral(id: int): Value =
  Value(kind: vkNeutral, neutId: id, spine: @[])

proc check(name: string, staged: SVal, expected: Value, env: Table[string, Value]) =
  let got = evalSVal(staged, env)
  assert eqVal(got, expected), name & ": staged/unstaged mismatch"
  echo "ok: ", name, "  staged == unstaged"
  echo "    residual: ", $staged
  echo "    residual nodes: ", countNodes(staged),
       "   staging-time betas: ", betaCount

# --- shared setup ---

let ev = evalSym
let st = stagedSym()

# X = 1 x 1 (non-dependent sigma), shared by the demos
let Xv = ev.cSigma(ev.cUnit(), proc(u: Value): Value = ev.cUnit())
let Xs = st.cSigma(st.cUnit(), proc(u: SVal): SVal = st.cUnit())

echo "=== Demo 1: twice (X->X) -> X -> X, f static, x dynamic ==="
resetBetaCount()
let fV = ev.cLam(Xv, proc(p: Value): Value = ev.cPair(p, ev.cTt()))
let fs = st.cLam(Xs, proc(p: SVal): SVal = st.cPair(p, st.cTt()))
let xV = neutral(7)
let u1 = ev.cApp(ev.cApp(ev.cApp(twice(ev), Xv), fV), xV)
let s1 = st.cApp(st.cApp(st.cApp(twice(st), Xs), fs), dynamicVar("x"))
check("twice f x", s1, u1, {"x": xV}.toTable)

echo ""
echo "=== Demo 2: const A B (static tt) (dynamic y) ==> static tt ==="
resetBetaCount()
let yV = neutral(8)
let u2 = ev.cApp(ev.cApp(ev.cApp(ev.cApp(constFn(ev),
  ev.cUnit()), ev.cUnit()), ev.cTt()), yV)
let s2 = st.cApp(st.cApp(st.cApp(st.cApp(constFn(st),
  st.cUnit()), st.cUnit()), st.cTt()), dynamicVar("y"))
check("const <> y", s2, u2, {"y": yV}.toTable)

echo ""
echo "=== Demo 3: pairSwap (pair <> z) ==> (pair z <>) ==="
echo "    (exercises staging-time projection through a residual pair)"
resetBetaCount()
let zV = neutral(9)
let Pv = ev.cPair(ev.cTt(), zV)
let u3 = ev.cApp(pairSwap(ev), Pv)
let Ps = st.cPair(st.cTt(), dynamicVar("z"))
let s3 = st.cApp(pairSwap(st), Ps)
check("pairSwap (pair <> z)", s3, u3, {"z": zV}.toTable)

# --- Benchmark A: static spine of L functions over dynamic x ---
#
# Staging unrolls the L applications at staging time (L host calls, once);
# the residual is a straight-line nest of pair nodes. The unstaged
# interpreter pays a vApp dispatch + closure call per application per input.

echo ""
echo "=== Benchmark A: L static fns applied to dynamic x, M inputs ==="
const LA = 300
const MA = 300
let fiVA = ev.cLam(Xv, proc(p: Value): Value = ev.cPair(p, ev.cTt()))
let fiSA = st.cLam(Xs, proc(p: SVal): SVal = st.cPair(p, st.cTt()))

resetBetaCount()
let tStageA = cpuTime()
var accS: SVal = dynamicVar("x")
for _ in 1 .. LA:
  accS = st.cApp(fiSA, accS)
let stageTimeA = cpuTime() - tStageA
let betasA = betaCount
echo "stage: ", LA, " applications unrolled in ", stageTimeA * 1000, " ms",
     " (", betasA, " staging-time betas), residual nodes: ", countNodes(accS)

let tUnA = cpuTime()
for i in 1 .. MA:
  var acc: Value = neutral(1000 + i)
  for _ in 1 .. LA:
    acc = ev.cApp(fiVA, acc)
let unTimeA = cpuTime() - tUnA

let tStA = cpuTime()
for i in 1 .. MA:
  discard evalSVal(accS, {"x": neutral(1000 + i)}.toTable)
let stTimeA = cpuTime() - tStA

# spot-check agreement on one input
let spotU = block:
  var acc: Value = neutral(4242)
  for _ in 1 .. LA: acc = ev.cApp(fiVA, acc)
  acc
assert eqVal(evalSVal(accS, {"x": neutral(4242)}.toTable), spotU),
  "benchmark A: staged/unstaged mismatch"
echo "unstaged: ", MA, "x", LA, " apps in ", unTimeA * 1000, " ms"
echo "staged residual eval: ", stTimeA * 1000, " ms",
     "  (+ one-time stage ", stageTimeA * 1000, " ms)"
echo "per-input speedup (excl. one-time stage): ", unTimeA / stTimeA, "x"

# --- Benchmark B: hoisting a static subcomputation out of the loop ---
#
# Each fn body contains a *static* witness: sixtyfour id <> ~~> <>, i.e.
# 64 interpreter reductions. The naive unstaged interpreter re-derives it
# on every application; staging evaluates it once at staging time and the
# residual never mentions it.

echo ""
echo "=== Benchmark B: static 64-redex witness hoisted out of the loop ==="

proc churchTwo[R](s: Sym[R]): R =
  let UU = s.cArr(s.cUnit(), s.cUnit())
  s.cLam(UU, proc(f: R): R =
    s.cLam(s.cUnit(), proc(x: R): R = s.cApp(f, s.cApp(f, x))))

proc churchMult[R](s: Sym[R], m, n: R): R =
  ## mult m n = λf. m (n f).
  ## NOTE: app(m, n) is *exponentiation* n^m for Church numerals, not
  ## multiplication (app(two,two)=4=2^2 only by coincidence).
  let UU = s.cArr(s.cUnit(), s.cUnit())
  s.cLam(UU, proc(f: R): R = s.cApp(m, s.cApp(n, f)))

const LB = 32
const MB = 100

let twoV = churchTwo(ev)
let fourV = ev.cApp(twoV, twoV)          # 2^2 = 4
let sixteenV = churchMult(ev, fourV, fourV)      # 16
let sixtyfourV = churchMult(ev, sixteenV, fourV) # 64
let idV = ev.cLam(ev.cArr(ev.cUnit(), ev.cUnit()),
  proc(y: Value): Value = y)
let fiVB = ev.cLam(Xv, proc(p: Value): Value =
  # rebuilt and re-reduced on EVERY application (naive interpreter)
  let w = ev.cApp(ev.cApp(sixtyfourV, idV), ev.cTt())
  ev.cPair(w, p))

let twoS = churchTwo(st)
let fourS = st.cApp(twoS, twoS)            # 2^2 = 4
let sixteenS = churchMult(st, fourS, fourS)        # 16
let sixtyfourS = churchMult(st, sixteenS, fourS)   # 64
let idS = st.cLam(st.cArr(st.cUnit(), st.cUnit()),
  proc(y: SVal): SVal = y)
let fiSB = st.cLam(Xs, proc(p: SVal): SVal =
  # reduced ONCE per staging-time application; the residual keeps only tt
  let w = st.cApp(st.cApp(sixtyfourS, idS), st.cTt())
  st.cPair(w, p))

resetBetaCount()
let tStageB = cpuTime()
var accSB: SVal = dynamicVar("x")
for _ in 1 .. LB:
  accSB = st.cApp(fiSB, accSB)
let stageTimeB = cpuTime() - tStageB
let betasB = betaCount
echo "stage: ", LB, " fns x 64-redex witness in ", stageTimeB * 1000, " ms",
     " (", betasB, " staging-time betas), residual nodes: ", countNodes(accSB)
echo "residual (depth-limited): ", $accSB

let tUnB = cpuTime()
for i in 1 .. MB:
  var acc: Value = neutral(2000 + i)
  for _ in 1 .. LB:
    acc = ev.cApp(fiVB, acc)
let unTimeB = cpuTime() - tUnB

let tStB = cpuTime()
for i in 1 .. MB:
  discard evalSVal(accSB, {"x": neutral(2000 + i)}.toTable)
let stTimeB = cpuTime() - tStB

let spotUB = block:
  var acc: Value = neutral(5150)
  for _ in 1 .. LB: acc = ev.cApp(fiVB, acc)
  acc
assert eqVal(evalSVal(accSB, {"x": neutral(5150)}.toTable), spotUB),
  "benchmark B: staged/unstaged mismatch"
echo "unstaged: ", MB, "x", LB, " apps (+64 redexes each) in ",
     unTimeB * 1000, " ms"
echo "staged residual eval: ", stTimeB * 1000, " ms",
     "  (+ one-time stage ", stageTimeB * 1000, " ms)"
echo "per-input speedup (excl. one-time stage): ", unTimeB / stTimeB, "x"

echo ""
echo "ALL CHECKS PASSED"
