## Benchmark: staged typeo vs hand-written relational typeo (issues #19/#20)
##
## Aaron's chosen Track C step: "stage the bidirectional typing relation typeo
## (not just evalo) and benchmark it against the hand-written elaborator."
##
## Honest comparison design: the SAME relation (STLC+Nat typeo), the SAME
## engine (minikanren.nim), the SAME term representation (RTerm S-exprs) —
## differing only in whether staging specialized it. The baseline is
## rel_elab.typeo, the hand-written relational version that typeoData()
## mirrors. (The full Experiment-3 elaborator in src/elab.nim targets a much
## richer fragment/IR, so wall-clock against it would be apples-to-oranges;
## this benchmark decides whether the relational+staging path is competitive
## on its own terms first.)
##
## Method: stage typeo with ty static (nat, resp. arr(nat,nat)) and tm/ctx
## dynamic, with fuel for call inlining (#20). Convert the residual with
## toGoal once (staging cost, amortized), then per query substitute the
## ground term/ctx and run on the engine. Baseline runs rel_elab.typeo
## directly. Correctness: both must agree (accept/reject) on every query.
## Timing: min of 5 rounds x 200 iterations, cpuTime, reported per query.

import staging/relgoal
import staging/stagegoal
import staging/stage_typeo  # typeoData()
import staging/modes
import minikanren
import rel_elab
import tables
import sets
import times
import strformat
import math

# --- residual sanity: every rgCall must resolve -------------------------------
# Residuals legitimately contain rgCall — but only to *specialized*
# relations (partial deduction, issue #19). A call to anything else would
# not execute faithfully via toGoal. Assert full resolution.

proc unresolvedCalls(rg: RelGoal, specs: Table[string, RelEntry]): seq[string] =
  case rg.kind
  of rgCall:
    if rg.relName in specs: @[]
    else: @[rg.relName]
  of rgConj, rgDisj:
    unresolvedCalls(rg.leftG, specs) & unresolvedCalls(rg.rightG, specs)
  of rgFresh: unresolvedCalls(rg.body, specs)
  of rgFail, rgSucceed, rgEq, rgNeq, rgSetEq, rgBranch: @[]

# --- staging ---------------------------------------------------------------

proc specializeChecker*(tyStatic: RTerm, fuel: int):
    tuple[top: string, specs: Table[string, RelEntry]] =
  ## Partially deduce typeo with ty static; return the top specialized
  ## relation name plus all specialized bodies (for toGoal).
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mIn, mIn], body: typeoData())
  var ctx = newSpecCtx(relEnv, fuel)
  var staticParams = initTable[string, RTerm]()
  staticParams["ty"] = tyStatic
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")
  let top = specializeRelation(ctx, "typeo", staticParams, dynamicVars)
  for name, e in ctx.specs:
    let bad = unresolvedCalls(e.body, ctx.specs)
    doAssert bad.len == 0, "unresolved calls in " & name & ": " & $bad
  (top, ctx.specs)

# --- query execution --------------------------------------------------------

proc num(n: int): RTerm =
  result = zeroTm()
  for _ in 1 .. n: result = sucTm(result)

proc runCheck(g: Goal): bool =
  ## Checking query: succeeds iff the goal has at least one answer.
  run(freshVar(), g, 1).len > 0

proc baselineCheck(tm: RTerm, ty: RTerm): bool =
  runCheck(typeo(tm, ty, rnil()))

proc stagedGoalFor(top: string, specs: Table[string, RelEntry],
                   tm: RTerm): Goal =
  ## Instantiate the top specialized checker's dynamic placeholders for
  ## one ground query term, then compile to a Goal via toGoal.
  ## (Per-term instantiation is staging cost, done once per term —
  ## not per iteration.)
  let e = specs[top]
  let inst = substAtom(substAtom(e.body, ratom("__var_tm"), tm),
                       ratom("__var_ctx"), rnil())
  toGoal(inst, specs)

proc stagedCheck(top: string, specs: Table[string, RelEntry],
                 tm: RTerm, ty: RTerm): bool =
  ## Instantiate the residual's dynamic placeholders, then run.
  ## (ty is only used for the baseline; the residual has it baked in.)
  runCheck(stagedGoalFor(top, specs, tm))

# --- timing -----------------------------------------------------------------

proc timeIt(iters: int, body: proc()): float =
  ## Min-of-5 rounds, seconds per iteration.
  var best = Inf
  for _ in 1 .. 5:
    let t0 = cpuTime()
    for _ in 1 .. iters: body()
    let dt = cpuTime() - t0
    if dt < best: best = dt
  best / iters.float

# --- benchmark --------------------------------------------------------------

type Query = ref object
  name: string
  tm: RTerm
  valid: bool  # expected answer

proc benchChecker(label: string, ty: RTerm, queries: seq[Query], fuel: int) =
  echo &"=== {label} (fuel={fuel}) ==="
  let tStage0 = cpuTime()
  let (top, specs) = specializeChecker(ty, fuel)
  let tStage = cpuTime() - tStage0
  echo &"staging time (one-off): {tStage*1000:.2f} ms"
  echo &"specialized relations: {top} + {specs.len - 1} more"
  echo ""
  echo &"""{"query":28} {"ok?":4} {"baseline us":>11} {"staged us":>10} {"speedup":>7}"""
  for q in queries:
    # correctness: both engines must agree, and match expectation
    let qtm = q.tm            # copy refs to locals so closures can capture
    let qname = q.name
    let qvalid = q.valid
    let bAns = baselineCheck(qtm, ty)
    let sAns = stagedCheck(top, specs, qtm, ty)
    doAssert bAns == sAns,
      &"MISMATCH on {qname}: baseline={bAns} staged={sAns}"
    doAssert bAns == qvalid,
      &"WRONG ANSWER on {qname}: got {bAns}, expected {qvalid}"
    let ok = if bAns: "yes" else: "no"
    const iters = 200
    let tBase = timeIt(iters, proc() = discard baselineCheck(qtm, ty))
    let stagedGoal = stagedGoalFor(top, specs, qtm)  # compile once per term
    let tStaged = timeIt(iters, proc() = discard runCheck(stagedGoal))
    echo &"""{qname:28} {ok:4} {tBase*1e6:11.1f} {tStaged*1e6:10.1f} {tBase/tStaged:7.2f}x"""
  echo ""

when isMainModule:
  const fuel = 8

  let natQueries = @[
    Query(name: "zero", tm: zeroTm(), valid: true),
    Query(name: "suc(zero)", tm: num(1), valid: true),
    Query(name: "suc^3(zero)", tm: num(3), valid: true),
    Query(name: "suc^6(zero)", tm: num(6), valid: true),
    Query(name: "app(lam x.x, suc^2)", tm: appTm(lamTm(varTm(0)), num(2)), valid: true),
    Query(name: "suc(lam x.x) [invalid]", tm: sucTm(lamTm(varTm(0))), valid: false),
    Query(name: "app(zero, zero) [invalid]", tm: appTm(zeroTm(), zeroTm()), valid: false),
    Query(name: "var(0) in empty ctx [invalid]", tm: varTm(0), valid: false),
  ]
  benchChecker("nat checker", natTy(), natQueries, fuel)

  let arrTyNN = arrTy(natTy(), natTy())
  let arrQueries = @[
    Query(name: "lam x.x", tm: lamTm(varTm(0)), valid: true),
    Query(name: "lam x.suc(x)", tm: lamTm(sucTm(varTm(0))), valid: true),
    Query(name: "lam x.lam y.y", tm: lamTm(lamTm(varTm(0))), valid: true),
    Query(name: "zero [invalid]", tm: zeroTm(), valid: false),
    Query(name: "suc(zero) [invalid]", tm: num(1), valid: false),
    Query(name: "var(1) in empty ctx [invalid]", tm: varTm(1), valid: false),
  ]
  benchChecker("arr(nat,nat) checker", arrTyNN, arrQueries, fuel)

  echo "All correctness asserts passed: staged and baseline agree on every query."
