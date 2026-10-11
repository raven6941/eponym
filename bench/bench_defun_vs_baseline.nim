## Before/after benchmark for issue #53 (defunctionalize before staging).
##
## Stages a SHARED corpus through both pipelines and compares residual
## size (node count) and staging wall-clock:
##   - baseline: higher-order Sym[SVal] stager (tests/ett_staged.nim),
##     closures as host procs (svStaticLam), binders as host closures.
##   - defun:    first-order defunctionalized stager (tests/staged_defun.nim),
##     closures as data (dvLam = code pointer + env), explicit applyD dispatch,
##     residual binders as de Bruijn levels.
##
## Every program also runs unstaged (evalSym); both pipelines must agree
## with it. Timings: per-program staging wall-clock over 5 reps (min
## reported); scale benchmark (300 unrolled applications) over 3 reps.
## Residual node counts via countNodes / countDNodes (statics contribute 0
## in both counters).

import std/[tables, times]
import eponym
import ett_staged
import staged_defun

# --- agreement on values (neutrals by id) ---

proc agree(a, b: Value): bool =
  if a.kind != b.kind: return false
  case a.kind
  of vkStar, vkUnit, vkTt, vkEmpty: true
  of vkPi, vkSigma, vkLam: false
  of vkPair: agree(a.fstV, b.fstV) and agree(a.sndV, b.sndV)
  of vkNat: a.natV == b.natV
  of vkNeutral:
    a.neutId == b.neutId and a.spine.len == b.spine.len

proc neutralB(id: int): Value =
  Value(kind: vkNeutral, neutId: id, spine: @[])

let ev = evalSym
let st = stagedSym()

# X = 1 x 1 (non-dependent sigma), shared
let Xv = ev.cSigma(ev.cUnit(), proc(u: Value): Value = ev.cUnit())
let Xs = st.cSigma(st.cUnit(), proc(u: SVal): SVal = st.cUnit())

proc stageMin(reps: int, body: proc(): void): float =
  ## Min wall-clock (ms) of `reps` runs.
  result = high(float)
  for _ in 1 .. reps:
    let t0 = cpuTime()
    body()
    result = min(result, (cpuTime() - t0) * 1000.0)

# ================= Program 1: twice f x (f static, x dynamic) =============

let twiceProg = dLam(dLam(dLam(dApp(dVar 1, dApp(dVar 1, dVar 0)))))
let fD1 = dLamVal(dPair(dVar 0, dTt()))
let fV1 = ev.cLam(Xv, proc(p: Value): Value = ev.cPair(p, ev.cTt()))
let fS1 = st.cLam(Xs, proc(p: SVal): SVal = st.cPair(p, st.cTt()))
let xV1 = neutralB(7)
let u1 = ev.cApp(ev.cApp(ev.cApp(twice(ev), Xv), fV1), xV1)

var dRes1: DVal
let tDef1 = stageMin(5, proc() =
  var s = stageD(twiceProg, @[], 0)
  s = applyD(s, staticD(Xv), 0)
  s = applyD(s, fD1, 0)
  dRes1 = applyD(s, dynLvl(0), 1))

var bRes1: SVal
let tBase1 = stageMin(5, proc() =
  bRes1 = st.cApp(st.cApp(st.cApp(twice(st), staticVal(Xv)), fS1),
                  dynamicVar("x")))

assert agree(evalD(dRes1, {0: xV1}.toTable, 1), u1), "p1 defun agreement"
assert agree(evalSVal(bRes1, {"x": xV1}.toTable), u1), "p1 baseline agreement"
echo "p1 twice f x:        defun  nodes=", countDNodes(dRes1),
     " time=", tDef1, "ms   | baseline nodes=", countNodes(bRes1),
     " time=", tBase1, "ms"

# ================= Program 2: const A B x y (y dynamic) ====================

let constProg = dLam(dLam(dLam(dLam(dVar 1))))
let yV2 = neutralB(8)
let u2 = ev.cApp(ev.cApp(ev.cApp(ev.cApp(constFn(ev),
  ev.cUnit()), ev.cUnit()), ev.cTt()), yV2)

var dRes2: DVal
let tDef2 = stageMin(5, proc() =
  var s = stageD(constProg, @[], 0)
  s = applyD(s, staticD(ev.cUnit()), 0)
  s = applyD(s, staticD(ev.cUnit()), 0)
  s = applyD(s, staticD(ev.cTt()), 0)
  dRes2 = applyD(s, dynLvl(0), 1))

var bRes2: SVal
let tBase2 = stageMin(5, proc() =
  bRes2 = st.cApp(st.cApp(st.cApp(st.cApp(constFn(st),
    st.cUnit()), st.cUnit()), st.cTt()), dynamicVar("y")))

assert agree(evalD(dRes2, {0: yV2}.toTable, 1), u2), "p2 defun agreement"
assert agree(evalSVal(bRes2, {"y": yV2}.toTable), u2), "p2 baseline agreement"
echo "p2 const <> y:       defun  nodes=", countDNodes(dRes2),
     " time=", tDef2, "ms   | baseline nodes=", countNodes(bRes2),
     " time=", tBase2, "ms"

# ================= Program 3: pairSwap (pair <> z) (z dynamic) =============

let swapProg = dLam(dPair(dSnd(dVar 0), dFst(dVar 0)))
let zV3 = neutralB(9)
let Pv3 = ev.cPair(ev.cTt(), zV3)
let u3 = ev.cApp(pairSwap(ev), Pv3)

var dRes3: DVal
let tDef3 = stageMin(5, proc() =
  dRes3 = applyD(stageD(swapProg, @[], 0),
    DVal(kind: dvDyn, node: DNode(kind: dnPair,
      a: staticD(ev.cTt()), b: dynLvl(0))), 1))

var bRes3: SVal
let tBase3 = stageMin(5, proc() =
  bRes3 = st.cApp(pairSwap(st), st.cPair(st.cTt(), dynamicVar("z"))))

assert agree(evalD(dRes3, {0: zV3}.toTable, 1), u3), "p3 defun agreement"
assert agree(evalSVal(bRes3, {"z": zV3}.toTable), u3), "p3 baseline agreement"
echo "p3 pairSwap:         defun  nodes=", countDNodes(dRes3),
     " time=", tDef3, "ms   | baseline nodes=", countNodes(bRes3),
     " time=", tBase3, "ms"

# ================= Program 4: compose id id x (closes over 2 binders) ======

proc compose[R](s: Sym[R]): R =
  let UU = s.cArr(s.cUnit(), s.cUnit())
  s.cLam(UU, proc(f: R): R =
    s.cLam(UU, proc(g: R): R =
      s.cLam(s.cUnit(), proc(x: R): R = s.cApp(f, s.cApp(g, x)))))

let composeProg = dLam(dLam(dLam(dApp(dVar 2, dApp(dVar 1, dVar 0)))))
let UU = ev.cArr(ev.cUnit(), ev.cUnit())
let idV = ev.cLam(UU, proc(y: Value): Value = y)
let idD = dLamVal(dVar 0)
let idS = st.cLam(st.cArr(st.cUnit(), st.cUnit()),
  proc(y: SVal): SVal = y)
let xV4 = neutralB(10)
let u4 = ev.cApp(ev.cApp(ev.cApp(compose(ev), idV), idV), xV4)

var dRes4: DVal
let tDef4 = stageMin(5, proc() =
  var s = stageD(composeProg, @[], 0)
  s = applyD(s, idD, 0)
  s = applyD(s, idD, 0)
  dRes4 = applyD(s, dynLvl(0), 1))

var bRes4: SVal
let tBase4 = stageMin(5, proc() =
  bRes4 = st.cApp(st.cApp(st.cApp(compose(st), idS), idS), dynamicVar("x")))

assert agree(evalD(dRes4, {0: xV4}.toTable, 1), u4), "p4 defun agreement"
assert agree(evalSVal(bRes4, {"x": xV4}.toTable), u4), "p4 baseline agreement"
echo "p4 compose id id x:  defun  nodes=", countDNodes(dRes4),
     " time=", tDef4, "ms   | baseline nodes=", countNodes(bRes4),
     " time=", tBase4, "ms"

# ================= Program 5: residual lambda (defun-only capability) =======
#
# Baseline cLam always yields a staging-time svStaticLam; it never
# produces a residual lambda node. The closest analogue is staging-time
# application, which ELIMINATES the binder (residual = just the var).
# Defun reifyD RESIDUALIZES it (residual = (lam [v0] v0)). Not
# apples-to-apples: the point is the capability delta.

var dRes5: DVal
let tDef5 = stageMin(5, proc() =
  dRes5 = reifyD(dLamVal(dVar 0), 0))
let wN5 = neutralB(11)
assert agree(ev.cApp(evalD(dRes5, initTable[int, Value](), 1), wN5), wN5),
  "p5 defun: reified identity misbehaves"

var bRes5: SVal
let tBase5 = stageMin(5, proc() =
  bRes5 = st.cApp(st.cLam(Xs, proc(x: SVal): SVal = x), dynamicVar("w")))
assert agree(evalSVal(bRes5, {"w": wN5}.toTable), wN5),
  "p5 baseline: staged identity misbehaves"

echo "p5 residual lambda:  defun  nodes=", countDNodes(dRes5),
     " (", $dRes5, ") time=", tDef5, "ms"
echo "                     baseline nodes=", countNodes(bRes5),
     " (binder eliminated at staging time) time=", tBase5, "ms"

# ================= Scale: 300 static fns unrolled onto dynamic x ===========
#
# Staging unrolls all 300 applications at staging time (staging-time
# betas); the residual is a straight-line nest of pair nodes. Measures
# whether the first-order apply dispatch is materially faster/slower
# than host-closure invocation at scale.

const L = 300
let fiD = dLamVal(dPair(dVar 0, dTt()))
let fiS = st.cLam(Xs, proc(p: SVal): SVal = st.cPair(p, st.cTt()))
let fiV = ev.cLam(Xv, proc(p: Value): Value = ev.cPair(p, ev.cTt()))

var dScale: DVal
let tDefS = stageMin(3, proc() =
  var acc: DVal = dynLvl(0)
  for _ in 1 .. L: acc = applyD(fiD, acc, 1)
  dScale = acc)

var bScale: SVal
let tBaseS = stageMin(3, proc() =
  var acc: SVal = dynamicVar("x")
  for _ in 1 .. L: acc = st.cApp(fiS, acc)
  bScale = acc)

let spotV = block:
  var acc: Value = neutralB(4242)
  for _ in 1 .. L: acc = ev.cApp(fiV, acc)
  acc
assert agree(evalD(dScale, {0: neutralB(4242)}.toTable, 1), spotV),
  "scale defun agreement"
assert agree(evalSVal(bScale, {"x": neutralB(4242)}.toTable), spotV),
  "scale baseline agreement"

echo "scale 300x unroll:   defun  nodes=", countDNodes(dScale),
     " time=", tDefS, "ms   | baseline nodes=", countNodes(bScale),
     " time=", tBaseS, "ms"

# ============ Scheme equivalence: flattened vs compositional ==============
#
# Issue #71 acceptance: the flattened closure must compute exactly what
# stageD (and the compositional #60 scheme) computes. Head-to-head on
# the corpus bodies: same args through applyD, then reifyD to a residual
# tree and compare structure + node count.

proc eqScheme(name: string, body: DForm, args: seq[DVal], lvl: int) =
  var vF = DVal(kind: dvLam, body: body, env: @[], code: compileD(body))
  var vC = DVal(kind: dvLam, body: body, env: @[],
                code: compileDCompositional(body))
  for a in args:
    vF = applyD(vF, a, lvl)
    vC = applyD(vC, a, lvl)
  let rF = reifyD(vF, lvl)
  let rC = reifyD(vC, lvl)
  assert countDNodes(rF) == countDNodes(rC),
    name & ": node count differs (" & $countDNodes(rF) & " vs " &
    $countDNodes(rC) & ")"
  assert $rF == $rC,
    name & ": residual differs\n  flat=" & $rF & "\n  comp=" & $rC
  echo "equiv ok: ", name, "  nodes=", countDNodes(rF)

eqScheme("twice (full application)", twiceProg,
         @[staticD(Xv), fD1, dynLvl(0)], 1)
eqScheme("twice (partial: one arg, nested lam)", twiceProg,
         @[staticD(Xv)], 0)
eqScheme("compose", composeProg, @[idD, idD, dynLvl(0)], 1)
eqScheme("pairSwap", swapProg,
         @[DVal(kind: dvDyn, node: DNode(kind: dnPair,
           a: staticD(ev.cTt()), b: dynLvl(0)))], 1)
eqScheme("const (3 static, y dynamic)", constProg,
         @[staticD(ev.cUnit()), staticD(ev.cUnit()), staticD(ev.cTt()),
           dynLvl(0)], 1)
block:
  # scale fn through chained betas (the repeated-beta path)
  let pairBody = dPair(dVar 0, dTt())
  let lamF = DVal(kind: dvLam, body: pairBody, env: @[],
                  code: compileD(pairBody))
  let lamC = DVal(kind: dvLam, body: pairBody, env: @[],
                  code: compileDCompositional(pairBody))
  var accF: DVal = dynLvl(0)
  var accC: DVal = dynLvl(0)
  for _ in 1 .. 10:
    accF = applyD(lamF, accF, 1)
    accC = applyD(lamC, accC, 1)
  assert countDNodes(accF) == countDNodes(accC),
    "scale-fn loop: node count differs"
  assert $accF == $accC, "scale-fn loop: residual differs"
  echo "equiv ok: scale-fn x10 chained betas  nodes=", countDNodes(accF)

echo ""
echo "ALL BENCHMARK AGREEMENT CHECKS PASSED"
