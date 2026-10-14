## bench_typeo.nim — Issue #19: wall-clock staged vs unstaged typeo
##
## Honest design (per the #19 thread): same relation (rel_elab.typeo),
## same engine, same RTerm representation — the only difference is that
## the staged side runs the specialized residual (typeo_s0/typeo_s1)
## derived by stageGoal rules, while the unstaged side runs the original
## relation. Two questions:
##   1. Differential correctness: do staged and unstaged agree on every
##      test term?
##   2. Wall-clock: per-term timing over N iterations; report speedup.
##
## Usage: nim c -r --path:src src/experimental/staging/bench_typeo.nim

import staging/relgoal
import staging/stagegoal
import staging/stage_typeo  # typeoData
import staging/modes
import minikanren
import rel_elab
import tables
import sets
import times
import strformat

const MaxDepth = 20        # generous: correctness oracle depth
const ItersPerTerm = 15    # timing iterations per term

# --- Specialization (the "compile" step) --------------------------------

proc buildSpecialized(): (string, Table[string, RelEntry]) =
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mIn, mIn], body: typeoData())
  var ctx = newSpecCtx(relEnv, fuel = 8)
  var staticParams = initTable[string, RTerm]()
  staticParams["ty"] = natTy()
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")
  let top = specializeRelation(ctx, "typeo", staticParams, dynamicVars)
  (top, ctx.specs)

# --- Checkers ------------------------------------------------------------

proc checkUnstaged(tm, ctxTm: RTerm, depth: int): bool =
  ## Run the original typeo(tm, nat, ctx); true iff it succeeds.
  let q = freshVar()
  let g = conj(typeo(tm, natTy(), ctxTm), `==`(q, ratom("yes")))
  run(q, g, 1, depth).len > 0

proc checkStaged(top: string, specs: Table[string, RelEntry],
                 tm, ctxTm: RTerm, depth: int): bool =
  ## Run the specialized residual via toGoal (lazy rgCall expansion).
  let q = freshVar()
  let g = conj(toGoal(rgCall(top, @[tm, natTy(), ctxTm]), specs),
               `==`(q, ratom("yes")))
  run(q, g, 1, depth).len > 0

# --- Test terms ----------------------------------------------------------

proc sucN(n: int): RTerm =
  result = zeroTm()
  for _ in 1..n: result = sucTm(result)

type TestCase = tuple[name: string, tm: RTerm, ctxTm: RTerm, expect: bool]

proc testCases(): seq[TestCase] =
  let nilCtx = rnil()
  let natCtx = rpair(natTy(), nilCtx)
  let arrCtx = rpair(arrTy(natTy(), natTy()), nilCtx)
  @[
    ("zero",              zeroTm(),                nilCtx, true),
    ("suc(zero)",         sucN(1),                 nilCtx, true),
    ("suc^3",             sucN(3),                 nilCtx, true),
    ("suc^5",             sucN(5),                 nilCtx, true),
    ("app(lam(0), zero)", appTm(lamTm(varTm(0)), zeroTm()), nilCtx, true),
    ("var(0) in nat-ctx", varTm(0),                natCtx, true),
    ("lam(0) : nat",      lamTm(varTm(0)),         nilCtx, false),
    ("var(0) in arr-ctx", varTm(0),                arrCtx, false),
    ("suc(lam(0))",       sucTm(lamTm(varTm(0))),  nilCtx, false),
  ]

# --- Depth calibration ---------------------------------------------------

proc calibrateDepth(top: string, specs: Table[string, RelEntry],
                    cases: seq[TestCase]): int =
  ## Smallest depth where both sides stabilize to their MaxDepth answers.
  ## (run uses iterative deepening 1..depth, so timing at this depth is
  ##  the honest minimal cost; both sides pay the same deepening.)
  var oracleU, oracleS: seq[bool]
  for c in cases:
    oracleU.add checkUnstaged(c.tm, c.ctxTm, MaxDepth)
    oracleS.add checkStaged(top, specs, c.tm, c.ctxTm, MaxDepth)
  for d in 2..MaxDepth:
    var ok = true
    for i, c in cases:
      if checkUnstaged(c.tm, c.ctxTm, d) != oracleU[i]: ok = false; break
      if checkStaged(top, specs, c.tm, c.ctxTm, d) != oracleS[i]: ok = false; break
    if ok: return d
  MaxDepth

# --- Main ----------------------------------------------------------------

when isMainModule:
  echo "=== Issue #19 benchmark: staged vs unstaged typeo ==="
  echo ""

  let tStage0 = cpuTime()
  let (top, specs) = buildSpecialized()
  echo &"Specialization ({top} + {specs.len - 1} more): " &
       &"{(cpuTime() - tStage0) * 1000:.1f} ms one-off"
  echo ""

  let cases = testCases()

  # 1. Differential correctness at generous depth.
  echo "--- Differential correctness (depth ", MaxDepth, ") ---"
  var allAgree = true
  for c in cases:
    let u = checkUnstaged(c.tm, c.ctxTm, MaxDepth)
    let s = checkStaged(top, specs, c.tm, c.ctxTm, MaxDepth)
    let agree = (u == s)
    let sane = (u == c.expect)
    if not agree: allAgree = false
    echo &"  {c.name:<22} unstaged={u:<5} staged={s:<5} " &
         &"agree={agree}  (expected {c.expect}, sane={sane})"
  echo ""
  if allAgree:
    echo "PASS: staged and unstaged agree on all ", cases.len, " terms."
  else:
    echo "FAIL: staged/unstaged disagree — do not trust timings."
    quit(1)
  echo ""

  # 2. Wall-clock at calibrated depth.
  let depth = calibrateDepth(top, specs, cases)
  echo "--- Wall-clock (", ItersPerTerm, " iters/term, depth ", depth, ") ---"
  var totU, totS = 0.0
  for c in cases:
    let t0 = cpuTime()
    for _ in 1..ItersPerTerm: discard checkUnstaged(c.tm, c.ctxTm, depth)
    let msU = (cpuTime() - t0) * 1000 / ItersPerTerm.float
    let t1 = cpuTime()
    for _ in 1..ItersPerTerm: discard checkStaged(top, specs, c.tm, c.ctxTm, depth)
    let msS = (cpuTime() - t1) * 1000 / ItersPerTerm.float
    totU += msU; totS += msS
    let speed = if msS > 0: msU / msS else: 0.0
    echo &"  {c.name:<22} unstaged={msU:>8.2f} ms  staged={msS:>8.2f} ms  " &
         &"speedup={speed:.2f}x"
  echo ""
  echo &"Total per-iter: unstaged={totU:.2f} ms  staged={totS:.2f} ms  " &
       &"speedup={totU / max(totS, 1e-9):.2f}x"
