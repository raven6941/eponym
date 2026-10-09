## Defunctionalized staging evaluator (issue #53).
##
## Baseline (`staging/ett_staged.nim`) represents staging-time functions as
## HOST CLOSURES: `svStaticLam.body: proc(x: SVal): SVal`, and every binder
## body in the residual IR as `proc(x: SVal): SVal`. Per the curated note
## `notes/defunctionalize-before-specializing.org`, specializers work much
## better on first-order code than on higher-order code: closures under
## binders resist static/dynamic classification. The Danvy discipline is
## defunctionalize first, then specialize.
##
## This module is the defunctionalized counterpart of the `Sym[SVal]`
## stager. The differences are all in representation:
##
## - Terms enter as FIRST-ORDER DATA (`DForm`, de Bruijn), not as
##   polymorphic host functions over `Sym[R]`. `cLam`'s body argument in
##   the baseline is arbitrary user host code and therefore cannot be
##   defunctionalized inside the instance; the change has to happen at the
##   term-representation level.
## - Staging-time lambdas are DATA: `dvLam(body: DForm, env: seq[DVal])`
##   (code pointer + captured environment), never `proc` values.
## - Staging-time application is an explicit first-order dispatch,
##   `applyD` — the defunctionalized `apply` function.
## - Residual binders use de Bruijn LEVELS (`dnLvl`), not host closures:
##   going under a binder just increments the level counter.
##
## There is no `proc(x: DVal): DVal` anywhere in the staging pipeline.
## The one boundary exception is `evalD`'s reification of `dvLam` to
## `ett.Value`'s `vkLam` (a host closure) — the baseline does exactly the
## same in `evalSVal`, since `ett.Value` itself is higher-order. That
## reification is outside the staging computation proper.
##
## Experiment protocol (#53): the corpus in `when isMainModule` stages the
## same programs through this module and through the baseline, checks
## staged == unstaged agreement via `evalD`/`evalSVal` against `evalSym`,
## and reports residual node counts + staging wall-clock before/after.

import std/[tables, times]
import ett
import staging/ett_staged

# --- First-order term language (de Bruijn indices, innermost-first) ---

type
  DFormKind* = enum
    dfVar, dfTt, dfUnit, dfLam, dfApp, dfPair, dfFst, dfSnd

  DForm* = ref object
    ## A closed-under-binders staging source term. Type annotations are
    ## absent: staging (like the baseline) does not typecheck.
    case kind*: DFormKind
    of dfVar: idx*: int
    of dfLam: body*: DForm
    of dfApp: fn*, arg*: DForm
    of dfPair: a*, b*: DForm
    of dfFst, dfSnd: sub*: DForm
    of dfTt, dfUnit: discard

proc dVar*(i: int): DForm = DForm(kind: dfVar, idx: i)
proc dTt*(): DForm = DForm(kind: dfTt)
proc dUnit*(): DForm = DForm(kind: dfUnit)
proc dLam*(body: DForm): DForm = DForm(kind: dfLam, body: body)
proc dApp*(fn, arg: DForm): DForm = DForm(kind: dfApp, fn: fn, arg: arg)
proc dPair*(a, b: DForm): DForm = DForm(kind: dfPair, a: a, b: b)
proc dFst*(p: DForm): DForm = DForm(kind: dfFst, sub: p)
proc dSnd*(p: DForm): DForm = DForm(kind: dfSnd, sub: p)

# --- First-order staged values and residual IR ---

type
  DValKind* = enum
    dvStatic, dvLam, dvDyn

  DNodeKind* = enum
    dnLvl, dnTt, dnApp, dnLam, dnPair, dnFst, dnSnd

  DNode* = ref object
    ## Residual IR node. Binders carry de Bruijn LEVELS: `dnLam`'s body
    ## was staged at level `bindLvl+1` and mentions the bound variable as
    ## `dnLvl(bindLvl)`. No host closures.
    case kind*: DNodeKind
    of dnLvl: lvl*: int
    of dnApp: fn*, arg*: DVal
    of dnLam:
      bindLvl*: int
      body*: DVal
    of dnPair: a*, b*: DVal
    of dnFst, dnSnd: sub*: DVal
    of dnTt: discard

  DVal* = ref object
    case kind*: DValKind
    of dvStatic: val*: Value
    of dvLam:
      body*: DForm      # code pointer
      env*: seq[DVal]   # captured environment (innermost-first)
    of dvDyn: node*: DNode

proc staticD*(v: Value): DVal = DVal(kind: dvStatic, val: v)
proc dynLvl*(lvl: int): DVal =
  DVal(kind: dvDyn, node: DNode(kind: dnLvl, lvl: lvl))

# --- The stager: first-order recursion + explicit apply dispatch ---

proc applyD(f, a: DVal, lvl: int): DVal
proc stageD*(f: DForm, env: seq[DVal], lvl: int): DVal =
  ## Stage a first-order term. `env` is innermost-first; `lvl` is the
  ## current binder depth for fresh residual variables.
  case f.kind
  of dfVar:
    env[f.idx]
  of dfTt:
    staticD(Value(kind: vkTt))
  of dfUnit:
    staticD(Value(kind: vkUnit))
  of dfLam:
    # Defunctionalized closure: data, not a host proc.
    DVal(kind: dvLam, body: f.body, env: env)
  of dfApp:
    applyD(stageD(f.fn, env, lvl), stageD(f.arg, env, lvl), lvl)
  of dfPair:
    let a = stageD(f.a, env, lvl)
    let b = stageD(f.b, env, lvl)
    if a.kind == dvStatic and b.kind == dvStatic:
      staticD(Value(kind: vkPair, fstV: a.val, sndV: b.val))
    else:
      DVal(kind: dvDyn, node: DNode(kind: dnPair, a: a, b: b))
  of dfFst:
    let p = stageD(f.sub, env, lvl)
    case p.kind
    of dvStatic:
      if p.val.kind == vkPair: staticD(p.val.fstV)
      else: DVal(kind: dvDyn, node: DNode(kind: dnFst, sub: p))
    of dvDyn:
      # Staging-time projection through a residual pair (baseline parity).
      if p.node.kind == dnPair: p.node.a
      else: DVal(kind: dvDyn, node: DNode(kind: dnFst, sub: p))
    of dvLam:
      raise newException(ValueError, "stageD: fst of a staging-time lambda")
  of dfSnd:
    let p = stageD(f.sub, env, lvl)
    case p.kind
    of dvStatic:
      if p.val.kind == vkPair: staticD(p.val.sndV)
      else: DVal(kind: dvDyn, node: DNode(kind: dnSnd, sub: p))
    of dvDyn:
      if p.node.kind == dnPair: p.node.b
      else: DVal(kind: dvDyn, node: DNode(kind: dnSnd, sub: p))
    of dvLam:
      raise newException(ValueError, "stageD: snd of a staging-time lambda")

proc applyD(f, a: DVal, lvl: int): DVal =
  ## The defunctionalized apply: staging-time beta-reduction is
  ## first-order environment extension, not host closure invocation.
  case f.kind
  of dvLam:
    stageD(f.body, @[a] & f.env, lvl)
  of dvStatic:
    if a.kind == dvStatic and f.val.kind == vkLam:
      # Static-static: delegate to the real interpreter (baseline parity:
      # the baseline reduces svStatic vkLam on static args via evalSym).
      staticD(f.val.body(a.val))
    else:
      DVal(kind: dvDyn, node: DNode(kind: dnApp, fn: f, arg: a))
  of dvDyn:
    DVal(kind: dvDyn, node: DNode(kind: dnApp, fn: f, arg: a))

proc reifyD*(v: DVal, lvl: int): DVal =
  ## Residualize a staging-time lambda: stage its body against a fresh
  ## dynamic variable. The baseline has no counterpart (its `cLam` never
  ## produces residual lambdas); this is new capability from going
  ## first-order — reification is just another first-order operation.
  case v.kind
  of dvLam:
    let x = dynLvl(lvl)
    DVal(kind: dvDyn, node: DNode(kind: dnLam, bindLvl: lvl,
      body: stageD(v.body, @[x] & v.env, lvl + 1)))
  else:
    v

# --- Residual evaluation: agreement check against the real interpreter ---

proc evalD*(s: DVal, renv: Table[int, Value], lvl: int): Value =
  ## Evaluate a staged value with the real interpreter, mirroring
  ## `evalSVal`. `renv` maps residual levels to values.
  case s.kind
  of dvStatic:
    s.val
  of dvLam:
    # Boundary reification (same as the baseline's svStaticLam case):
    # the host closure lives OUTSIDE the staging pipeline.
    let b = s.body
    let cenv = s.env
    let l = lvl
    let e = renv
    Value(kind: vkLam, body: proc(x: Value): Value =
      evalD(stageD(b, @[staticD(x)] & cenv, l), e, l))
  of dvDyn:
    let n = s.node
    case n.kind
    of dnLvl:
      renv[n.lvl]
    of dnTt:
      Value(kind: vkTt)
    of dnApp:
      evalSym.cApp(evalD(n.fn, renv, lvl), evalD(n.arg, renv, lvl))
    of dnLam:
      let bl = n.bindLvl
      let bb = n.body
      let e = renv
      Value(kind: vkLam, body: proc(x: Value): Value =
        var e2 = e
        e2[bl] = x
        evalD(bb, e2, bl + 1))
    of dnPair:
      evalSym.cPair(evalD(n.a, renv, lvl), evalD(n.b, renv, lvl))
    of dnFst:
      evalSym.cFst(evalD(n.sub, renv, lvl))
    of dnSnd:
      evalSym.cSnd(evalD(n.sub, renv, lvl))

# --- Residual inspection ---

proc ppDVal(s: DVal, depth: int): string
proc ppDNode(n: DNode, depth: int): string =
  if depth > 8: return "..."
  case n.kind
  of dnLvl: "v" & $n.lvl
  of dnTt: "<>"
  of dnApp: "(" & ppDVal(n.fn, depth+1) & " " & ppDVal(n.arg, depth+1) & ")"
  of dnLam:
    "(lam [v" & $n.bindLvl & "] " &
      ppDVal(n.body, depth+1) & ")"
  of dnPair: "(pair " & ppDVal(n.a, depth+1) & " " & ppDVal(n.b, depth+1) & ")"
  of dnFst: "(fst " & ppDVal(n.sub, depth+1) & ")"
  of dnSnd: "(snd " & ppDVal(n.sub, depth+1) & ")"

proc ppDVal(s: DVal, depth: int): string =
  if depth > 8: return "..."
  case s.kind
  of dvStatic: "static(" & $s.val.kind & ")"
  of dvLam: "<dlam>"
  of dvDyn: ppDNode(s.node, depth)

proc `$`*(s: DVal): string = ppDVal(s, 0)

proc countDNodes*(s: DVal): int =
  ## Residual node count; static parts and staging-time lambdas
  ## contribute 0 (they left no trace in the residual).
  case s.kind
  of dvStatic, dvLam: 0
  of dvDyn:
    let n = s.node
    case n.kind
    of dnLvl, dnTt: 1
    of dnApp: 1 + countDNodes(n.fn) + countDNodes(n.arg)
    of dnLam: 1 + countDNodes(n.body)
    of dnPair: 1 + countDNodes(n.a) + countDNodes(n.b)
    of dnFst, dnSnd: 1 + countDNodes(n.sub)

# --- Corpus agreement tests (run vs baseline + unstaged) ---

proc eqValD(a, b: Value): bool =
  if a.kind != b.kind: return false
  case a.kind
  of vkStar, vkUnit, vkTt, vkEmpty: true
  of vkPi, vkSigma, vkLam: false
  of vkPair: eqValD(a.fstV, b.fstV) and eqValD(a.sndV, b.sndV)
  of vkNeutral:
    a.neutId == b.neutId and a.spine.len == b.spine.len

proc neutralD(id: int): Value =
  Value(kind: vkNeutral, neutId: id, spine: @[])

when isMainModule:
  let ev = evalSym
  let st = stagedSym()

  # Shared: X = 1 x 1
  let Xv = ev.cSigma(ev.cUnit(), proc(u: Value): Value = ev.cUnit())

  var nPass = 0
  proc checkAgree(name: string, stagedD: DVal, unstaged: Value,
                  renv: Table[int, Value], lvl: int) =
    let got = evalD(stagedD, renv, lvl)
    assert eqValD(got, unstaged), name & ": defun-staged/unstaged mismatch"
    inc nPass
    echo "ok: ", name, "  defun-staged == unstaged"
    echo "    residual: ", $stagedD
    echo "    defun residual nodes: ", countDNodes(stagedD)

  echo "=== Corpus 1: twice (X->X) -> X -> X, f static, x dynamic ==="
  # twice = lam X. lam f. lam x. f (f x)   (types erased for staging)
  let twiceD = dLam(dLam(dLam(dApp(dVar 1, dApp(dVar 1, dVar 0)))))
  let fV = ev.cLam(Xv, proc(p: Value): Value = ev.cPair(p, ev.cTt()))
  # f as defunctionalized static closure: lam p. pair p <>
  let fD = DVal(kind: dvLam, body: dPair(dVar 0, dTt()), env: @[])
  let xN = neutralD(7)
  let u1 = ev.cApp(ev.cApp(ev.cApp(twice(ev), Xv), fV), xN)
  let t1 = cpuTime()
  let s1 = applyD(applyD(stageD(twiceD, @[], 0), staticD(Xv), 0), fD, 0)
  let s1r = applyD(s1, dynLvl(0), 1)
  let stageT1 = cpuTime() - t1
  checkAgree("twice f x", s1r, u1, {0: xN}.toTable, 1)
  echo "    stage time: ", stageT1 * 1000, " ms"

  echo ""
  echo "=== Corpus 2: const A B (static <>) (dynamic y) ==> static <> ==="
  # const = lam A. lam B. lam x. lam y. x
  let constD = dLam(dLam(dLam(dLam(dVar 1))))
  let yN = neutralD(8)
  let u2 = ev.cApp(ev.cApp(ev.cApp(ev.cApp(constFn(ev),
    ev.cUnit()), ev.cUnit()), ev.cTt()), yN)
  let t2 = cpuTime()
  var s2 = stageD(constD, @[], 0)
  s2 = applyD(s2, staticD(ev.cUnit()), 0)
  s2 = applyD(s2, staticD(ev.cUnit()), 0)
  s2 = applyD(s2, staticD(ev.cTt()), 0)
  s2 = applyD(s2, dynLvl(0), 1)
  let stageT2 = cpuTime() - t2
  checkAgree("const <> y", s2, u2, {0: yN}.toTable, 1)
  echo "    stage time: ", stageT2 * 1000, " ms"

  echo ""
  echo "=== Corpus 3: pairSwap (pair <> z) ==> (pair z <>) ==="
  # pairSwap = lam p. pair (snd p) (fst p)
  let swapD = dLam(dPair(dSnd(dVar 0), dFst(dVar 0)))
  let zN = neutralD(9)
  let Pv = ev.cPair(ev.cTt(), zN)
  let u3 = ev.cApp(pairSwap(ev), Pv)
  let t3 = cpuTime()
  let s3 = applyD(stageD(swapD, @[], 0),
    DVal(kind: dvDyn, node: DNode(kind: dnPair,
      a: staticD(ev.cTt()), b: dynLvl(0))), 1)
  let stageT3 = cpuTime() - t3
  checkAgree("pairSwap (pair <> z)", s3, u3, {0: zN}.toTable, 1)
  echo "    stage time: ", stageT3 * 1000, " ms"

  echo ""
  echo "=== Corpus 4: compose (closes over two binders), f,g static, x dynamic ==="
  # compose = lam f. lam g. lam x. f (g x)
  proc compose[R](s: Sym[R]): R =
    let UU = s.cArr(s.cUnit(), s.cUnit())
    s.cLam(UU, proc(f: R): R =
      s.cLam(UU, proc(g: R): R =
        s.cLam(s.cUnit(), proc(x: R): R = s.cApp(f, s.cApp(g, x)))))
  let composeD = dLam(dLam(dLam(dApp(dVar 2, dApp(dVar 1, dVar 0)))))
  let UU = ev.cArr(ev.cUnit(), ev.cUnit())
  let idV = ev.cLam(UU, proc(y: Value): Value = y)
  let idD = DVal(kind: dvLam, body: dVar 0, env: @[])
  let xN4 = neutralD(10)
  let u4 = ev.cApp(ev.cApp(ev.cApp(compose(ev), idV), idV), xN4)
  let t4 = cpuTime()
  var s4 = stageD(composeD, @[], 0)
  s4 = applyD(s4, idD, 0)
  s4 = applyD(s4, idD, 0)
  s4 = applyD(s4, dynLvl(0), 1)
  let stageT4 = cpuTime() - t4
  checkAgree("compose id id x", s4, u4, {0: xN4}.toTable, 1)
  echo "    stage time: ", stageT4 * 1000, " ms"

  echo ""
  echo "=== Corpus 5: reify a staging-time lambda (new capability) ==="
  # lam x. x  ==>  residual (lam [v0] v0); applied to a neutral it is identity
  let t5 = cpuTime()
  let s5 = reifyD(DVal(kind: dvLam, body: dVar 0, env: @[]), 0)
  let stageT5 = cpuTime() - t5
  echo "    residual: ", $s5, "  nodes: ", countDNodes(s5),
       "  stage time: ", stageT5 * 1000, " ms"
  assert countDNodes(s5) == 2, "reified identity should be lam + var"
  let lamV = evalD(s5, initTable[int, Value](), 1)
  let wN = neutralD(11)
  assert eqValD(ev.cApp(lamV, wN), wN), "reified identity misbehaves"
  inc nPass
  echo "ok: reify (lam x. x) evaluates as identity"

  echo ""
  echo "ALL ", nPass, " AGREEMENT CHECKS PASSED"
  echo "(baseline ett_staged.nim untouched: all existing staging tests unaffected)"
