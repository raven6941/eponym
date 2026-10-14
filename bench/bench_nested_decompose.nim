## bench_nested_decompose.nim — Issue #104: staged unification completeness
##
## Corpus of staging goals exercising nested binding inference, drawn from
## real typeo residuals (typeoData in staging/typeo_relgoal.nim — the STLC+NAT
## typing relation). Each goal is staged twice: with decomposeNested=true
## (current structural unifier) and =false (legacy pre-#104 head-only
## behavior). Metrics per goal:
##   - StagedGoal kind (sgDone / sgFail / sgResidual)
##   - bindings learned (env size delta)
##   - residual node count and disjunct (rgDisj) count
##   - staging wall-clock (median per iteration)
##
## The unit goals (1-11) are individual equations from real typeo branches;
## the relation goals (12-15) stage the full typeo relation under different
## static/dynamic splits and measure real residual size.
##
## Usage: nim c -r --path:src --path:src/experimental/relational --path:src/experimental/staging bench/bench_nested_decompose.nim

import staging/relgoal
import staging/stagegoal
import staging/typeo_relgoal
import staging/modes
import minikanren
import rel_elab   # natTy, arrTy, varTm, lamTm, appTm, zeroTm, sucTm
import tables
import sets
import times
import strformat
import strutils
import sequtils

# --- goal/term size metrics ------------------------------------------------

proc termNodes(t: RTerm): int =
  if t.isNil: 0
  else:
    case t.kind
    of rkVar, rkAtom: 1
    of rkPair: 1 + termNodes(t.head) + termNodes(t.tail)

proc goalNodes(g: RelGoal): int =
  case g.kind
  of rgFail, rgSucceed: 1
  of rgEq, rgNeq: 1 + termNodes(g.left) + termNodes(g.right)
  of rgConj, rgDisj: 1 + goalNodes(g.leftG) + goalNodes(g.rightG)
  of rgFresh: 1 + goalNodes(g.body)
  of rgCall: 1 + g.args.mapIt(termNodes(it)).foldl(a + b, 0)
  of rgSetEq: 1 + g.cells.mapIt(termNodes(it)).foldl(a + b, 0) +
                  g.values.mapIt(termNodes(it)).foldl(a + b, 0)
  of rgBranch: 1 + g.vars.mapIt(termNodes(it)).foldl(a + b, 0)

proc disjCount(g: RelGoal): int =
  ## Number of rgDisj nodes (residual branch count).
  case g.kind
  of rgFail, rgSucceed, rgEq, rgNeq: 0
  of rgConj: disjCount(g.leftG) + disjCount(g.rightG)
  of rgDisj: 1 + disjCount(g.leftG) + disjCount(g.rightG)
  of rgFresh: disjCount(g.body)
  of rgCall, rgSetEq, rgBranch: 0

# --- corpus ----------------------------------------------------------------

type
  CorpusGoal = object
    name*: string
    goal*: RelGoal
    env*: Table[string, RTerm]   # static bindings at entry
    dyn*: HashSet[string]        # dynamicVars (must-not-bind)

proc cg(name: string, goal: RelGoal,
        env: Table[string, RTerm] = initTable[string, RTerm](),
        dyn: HashSet[string] = initHashSet[string]()): CorpusGoal =
  CorpusGoal(name: name, goal: goal, env: env, dyn: dyn)

proc buildCorpus(): seq[CorpusGoal] =
  let nat = natTy()
  let zero = zeroTm()
  let suc0 = sucTm(zero)
  let suc1 = sucTm(suc0)
  let n = ratom("__var_n")
  let tm = ratom("__var_tm")
  let ty = ratom("__var_ty")
  let ctx = ratom("__var_ctx")
  let ty0 = ratom("__var_ty0")
  let ctxTail = ratom("__var_ctxTail")
  result = @[]

  # 1. sucCase nested binding: tm=suc(zero) static, tm == suc(n) => n=zero
  var e1 = initTable[string, RTerm]()
  e1["__var_tm"] = suc0
  result.add cg("01 suc-nested", rgEq(tm, sucTm(n)), e1)

  # 2. varCase context destructuring: ctx=(nat.nil) static => ty0=nat, ctxTail=nil
  var e2 = initTable[string, RTerm]()
  e2["__var_ctx"] = rpair(nat, rpair(nat, rnil()))
  result.add cg("02 ctx-destructure",
    rgEq(ctx, rpair(ty0, ctxTail)), e2)

  # 3. lamCase nested arrow: ty=arr(nat,arr(nat,nat)) static => d=nat, c=arr(nat,nat)
  var e3 = initTable[string, RTerm]()
  e3["__var_ty"] = arrTy(nat, arrTy(nat, nat))
  let d = ratom("__var_d"); let c = ratom("__var_c")
  result.add cg("03 arr-nested", rgEq(ty, arrTy(d, c)), e3)

  # 4. appCase application destructuring: tm=app(var(0),zero) static
  var e4 = initTable[string, RTerm]()
  e4["__var_tm"] = appTm(varTm(0), zero)
  let f = ratom("__var_f"); let a = ratom("__var_a")
  result.add cg("04 app-destructure", rgEq(tm, appTm(f, a)), e4)

  # 5. lamCase prune: ty=nat static, ty == arr(d,c) => prune
  var e5 = initTable[string, RTerm]()
  e5["__var_ty"] = nat
  result.add cg("05 prune-lam", rgEq(ty, arrTy(d, c)), e5)

  # 6. head prune: tm=zero static, tm == suc(n) => prune
  var e6 = initTable[string, RTerm]()
  e6["__var_tm"] = zero
  result.add cg("06 prune-suc-zero", rgEq(tm, sucTm(n)), e6)

  # 7. deep prune: suc(suc(n)) == suc(zero) => prune (structural)
  result.add cg("07 deep-prune",
    rgEq(sucTm(sucTm(n)), sucTm(zero)))

  # 8. deep nested: suc(suc(n)) == suc(suc(zero)) => n=zero
  result.add cg("08 deep-nested",
    rgEq(sucTm(sucTm(n)), sucTm(suc1)))

  # 9. occurs: n == suc(n) => residualize, no binding
  result.add cg("09 occurs", rgEq(n, sucTm(n)))

  # 10. mOut dynamic: v == suc(vn), v in dynamicVars => residualize
  var dyn10 = initHashSet[string]()
  dyn10.incl("__var_v")
  result.add cg("10 dyn-mout",
    rgEq(ratom("__var_v"), sucTm(ratom("__var_vn"))),
    initTable[string, RTerm](), dyn10)

  # 11. alias chain: (x == suc(n)) ∧ (x == suc(suc(zero))) => n=suc(zero)
  let x = ratom("__var_x")
  result.add cg("11 alias-chain",
    rgConj(rgEq(x, sucTm(n)), rgEq(x, sucTm(suc1))))

# --- unit goal runner ------------------------------------------------------

type UnitResult = object
  kindNew, kindOld: StagedGoalKind
  bindNew, bindOld: int
  nodesNew, nodesOld: int
  disjNew, disjOld: int
  msNew, msOld: float

const UnitIters = 500

proc runUnit(g: CorpusGoal): UnitResult =
  var tctx = newSpecCtx()
  # new (decomposeNested=true)
  var envN = g.env
  let t0 = cpuTime()
  var sN: StagedGoal
  for _ in 0 ..< UnitIters:
    var e = g.env
    sN = stageGoal(g.goal, e, g.dyn, tctx, true)
  let msN = (cpuTime() - t0) / UnitIters.float * 1000.0
  sN = stageGoal(g.goal, envN, g.dyn, tctx, true)  # final run for inspection
  # old (legacy)
  var envO = g.env
  let t1 = cpuTime()
  var sO: StagedGoal
  for _ in 0 ..< UnitIters:
    var e = g.env
    sO = stageGoal(g.goal, e, g.dyn, tctx, false)
  let msO = (cpuTime() - t1) / UnitIters.float * 1000.0
  sO = stageGoal(g.goal, envO, g.dyn, tctx, false)
  result = UnitResult(
    kindNew: sN.kind, kindOld: sO.kind,
    bindNew: envN.len, bindOld: envO.len,
    nodesNew: (if sN.kind == sgResidual: goalNodes(sN.goal) else: 0),
    nodesOld: (if sO.kind == sgResidual: goalNodes(sO.goal) else: 0),
    disjNew: (if sN.kind == sgResidual: disjCount(sN.goal) else: 0),
    disjOld: (if sO.kind == sgResidual: disjCount(sO.goal) else: 0),
    msNew: msN, msOld: msO)

# --- relation-level runner -------------------------------------------------

type RelResult = object
  specsNew, specsOld: int
  nodesNew, nodesOld: int
  disjNew, disjOld: int
  msNew, msOld: float
  oldCrashed*: bool  # legacy unifier pruned the whole relation (unsound)

const RelIters = 20

proc specializeOnce(staticParams: Table[string, RTerm],
                    dyn: HashSet[string], decomp: bool): (string, SpecCtx) =
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mIn, mIn], body: typeoData())
  var ctx = newSpecCtx(relEnv, fuel = 8)
  let top = specializeRelation(ctx, "typeo", staticParams, dyn, decomp)
  (top, ctx)

proc specTotals(ctx: SpecCtx): (int, int, int) =
  var nodes = 0
  var disj = 0
  for _, e in ctx.specs:
    nodes += goalNodes(e.body)
    disj += disjCount(e.body)
  (ctx.specs.len, nodes, disj)

proc runRel(name: string, staticParams: Table[string, RTerm],
            dyn: HashSet[string]): RelResult =
  let t0 = cpuTime()
  var topN = ""
  var ctxN: SpecCtx
  for _ in 0 ..< RelIters:
    (topN, ctxN) = specializeOnce(staticParams, dyn, true)
  let msN = (cpuTime() - t0) / RelIters.float * 1000.0
  let (spN, noN, diN) = specTotals(ctxN)
  let t1 = cpuTime()
  var crashed = false
  var spO = 0; var noO = 0; var diO = 0
  var msO = 0.0
  for _ in 0 ..< RelIters:
    try:
      discard specializeOnce(staticParams, dyn, false)
    except ValueError:
      # Legacy unifier unsoundly pruned the whole relation to Fail
      # (placeholder-vs-pair was a static No). Record once, stop timing.
      crashed = true
      break
  if not crashed:
    msO = (cpuTime() - t1) / RelIters.float * 1000.0
    # re-run once for totals (cheap; keeps the code simple)
    var relEnv = initTable[string, RelDef]()
    relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                             modes: @[mIn, mIn, mIn], body: typeoData())
    var ctxO = newSpecCtx(relEnv, fuel = 8)
    discard specializeRelation(ctxO, "typeo", staticParams, dyn, false)
    (spO, noO, diO) = specTotals(ctxO)
  else:
    msO = (cpuTime() - t1) / 1.0 * 1000.0  # time-to-crash, single attempt
  result = RelResult(specsNew: spN, specsOld: spO,
                     nodesNew: noN, nodesOld: noO,
                     disjNew: diN, disjOld: diO,
                     msNew: msN, msOld: msO,
                     oldCrashed: crashed)

# --- main ------------------------------------------------------------------

when isMainModule:
  echo "=== Issue #104: nested-decomposition corpus ==="
  echo "each goal staged with decomposeNested=true (new) and =false (legacy)"
  echo ""
  echo "--- unit goals (equations from real typeo branches) ---"
  echo "goal               kind new   kind old   bind n/o nodes n/o   ms n/o        verdict"
  var improved = 0
  var fixed = 0
  var same = 0
  for g in buildCorpus():
    let r = runUnit(g)
    # Verdicts: the legacy unifier was unsound on placeholder-vs-pair
    # (d231d19 fixed this): old=Fail on a satisfiable goal is a FIXED
    # soundness bug, not just a missed optimization.
    let satisfiableOldFail =
      r.kindOld == sgFail and r.kindNew in {sgDone, sgResidual}
    let verdict =
      if satisfiableOldFail: "FIXED (old unsound prune)"
      elif r.kindNew == sgDone and r.kindOld == sgResidual: "IMPROVED"
      elif r.nodesNew < r.nodesOld: "IMPROVED"
      elif r.nodesNew == r.nodesOld and r.kindNew == r.kindOld: "same"
      else: "diff (see note)"
    if verdict == "IMPROVED": inc improved
    elif verdict.startsWith("FIXED"): inc fixed
    elif verdict == "same": inc same
    echo fmt"{g.name:<18} {($r.kindNew)[2..^1]:<10} {($r.kindOld)[2..^1]:<10} " &
         fmt"{r.bindNew}/{r.bindOld:<7} {r.nodesNew}/{r.nodesOld:<9} " &
         fmt"{r.msNew:.4f}/{r.msOld:.4f}   {verdict}"
  echo ""
  echo fmt"unit goals: {improved} improved, {fixed} soundness fixes, {same} same"

  echo ""
  echo "--- relation goals (full typeo specialization) ---"
  echo "goal                       specs n/o nodes n/o    disj n/o ms n/o"
  type RelCase = tuple[name: string, sp: Table[string, RTerm], dyn: HashSet[string]]
  var cases: seq[RelCase] = @[]
  # 12: ty=nat static (the #19 1st projection), tm/ctx dynamic
  var sp12 = initTable[string, RTerm](); sp12["ty"] = natTy()
  var dyn12 = initHashSet[string]()
  dyn12.incl("__var_tm"); dyn12.incl("__var_ctx")
  cases.add((name: "12 ty=nat projection", sp: sp12, dyn: dyn12))
  # 13: tm=suc(suc(zero)) static, ty/ctx dynamic
  var sp13 = initTable[string, RTerm]()
  sp13["tm"] = sucTm(sucTm(zeroTm()))
  var dyn13 = initHashSet[string]()
  dyn13.incl("__var_ty"); dyn13.incl("__var_ctx")
  cases.add((name: "13 tm=suc(suc(zero))", sp: sp13, dyn: dyn13))
  # 14: ty=arr(nat,nat) static (lam branch survives), tm/ctx dynamic
  var sp14 = initTable[string, RTerm]()
  sp14["ty"] = arrTy(natTy(), natTy())
  var dyn14 = initHashSet[string]()
  dyn14.incl("__var_tm"); dyn14.incl("__var_ctx")
  cases.add((name: "14 ty=arr(nat,nat)", sp: sp14, dyn: dyn14))
  # 15: ctx=(nat.nil) static, tm/ty dynamic
  var sp15 = initTable[string, RTerm]()
  sp15["ctx"] = rpair(natTy(), rnil())
  var dyn15 = initHashSet[string]()
  dyn15.incl("__var_tm"); dyn15.incl("__var_ty")
  cases.add((name: "15 ctx=(nat.nil)", sp: sp15, dyn: dyn15))
  for c in cases:
    let r = runRel(c.name, c.sp, c.dyn)
    if r.oldCrashed:
      echo (c.name & " ".repeat(max(0, 26 - c.name.len)) &
        $r.specsNew & "/crash    " &
        $r.nodesNew & "/-          " &
        "-        " &
        fmt"{r.msNew:.2f}" & "/crash      legacy: whole relation unsoundly pruned")
    else:
      echo fmt"{c.name:<26} {r.specsNew}/{r.specsOld:<8} {r.nodesNew}/{r.nodesOld:<10} " &
           fmt"{r.disjNew}/{r.disjOld:<8} {r.msNew:.2f}/{r.msOld:.2f}"
  echo ""
  echo "nodes = total RelGoal nodes across all specialized relations;"
  echo "disj = total rgDisj branch nodes; ms = staging wall-clock per run."
