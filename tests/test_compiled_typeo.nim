## test_compiled_typeo.nim — Issue #35 acceptance: compiled residual
##
## 1. Differential correctness: compiled staged typeo vs unstaged typeo
##    on the bench_typeo corpus (9 terms + expectations).
## 2. Wall-clock: compiled residual vs unstaged (and vs the interpreted
##    residual, to check compilation actually removes the overhead).
##
## Usage: nim c -r --path:src src/staging/test_compiled_typeo.nim

import staging/relcompile   # stagedTypeoProcs macro + rgFailGoal helpers
import staging/relgoal
import staging/stagegoal
import staging/typeo_relgoal
import staging/modes
import minikanren
import rel_elab
import tables
import sets
import times
import strformat

# Compile-time: specialize typeo(tm, nat, ctx), emit procs + stagedTypeo.
stagedTypeoProcs()

const MaxDepth = 20
const ItersPerTerm = 15

proc checkUnstaged(tm, ctxTm: RTerm, depth: int): bool =
  let q = freshVar()
  let g = conj(typeo(tm, natTy(), ctxTm), `==`(q, ratom("yes")))
  run(q, g, 1, depth).len > 0

proc checkCompiled(tm, ctxTm: RTerm, depth: int): bool =
  let q = freshVar()
  let g = conj(stagedTypeo(tm, ctxTm), `==`(q, ratom("yes")))
  run(q, g, 1, depth).len > 0

proc checkInterpreted(top: string, specs: Table[string, RelEntry],
                      tm, ctxTm: RTerm, depth: int): bool =
  let q = freshVar()
  let g = conj(toGoal(rgCall(top, @[tm, natTy(), ctxTm]), specs),
               `==`(q, ratom("yes")))
  run(q, g, 1, depth).len > 0

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

when isMainModule:
  echo "=== Issue #35: compiled residual vs unstaged typeo ==="
  echo ""

  # Interpreted-residual baseline (same specialization, toGoal execution).
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mIn, mIn], body: typeoData())
  var spCtx = newSpecCtx(relEnv, fuel = 8)
  var staticParams = initTable[string, RTerm]()
  staticParams["ty"] = natTy()
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")
  let top = specializeRelation(spCtx, "typeo", staticParams, dynamicVars)
  let specs = spCtx.specs

  let cases = testCases()

  echo "--- Differential correctness (depth ", MaxDepth, ") ---"
  var allAgree = true
  for c in cases:
    let u = checkUnstaged(c.tm, c.ctxTm, MaxDepth)
    let k = checkCompiled(c.tm, c.ctxTm, MaxDepth)
    let agree = (u == k)
    let sane = (k == c.expect)
    if not agree: allAgree = false
    echo &"  {c.name:<22} unstaged={u:<5} compiled={k:<5} " &
         &"agree={agree}  (expected {c.expect}, sane={sane})"
  echo ""
  if allAgree:
    echo "PASS: compiled and unstaged agree on all ", cases.len, " terms."
  else:
    echo "FAIL: compiled/unstaged disagree — do not trust timings."
    quit(1)
  echo ""

  echo "--- Wall-clock (", ItersPerTerm, " iters/term, depth ", MaxDepth, ") ---"
  var totU, totI, totC = 0.0
  for c in cases:
    let t0 = cpuTime()
    for _ in 1..ItersPerTerm: discard checkUnstaged(c.tm, c.ctxTm, MaxDepth)
    let msU = (cpuTime() - t0) * 1000 / ItersPerTerm.float
    let t1 = cpuTime()
    for _ in 1..ItersPerTerm:
      discard checkInterpreted(top, specs, c.tm, c.ctxTm, MaxDepth)
    let msI = (cpuTime() - t1) * 1000 / ItersPerTerm.float
    let t2 = cpuTime()
    for _ in 1..ItersPerTerm: discard checkCompiled(c.tm, c.ctxTm, MaxDepth)
    let msC = (cpuTime() - t2) * 1000 / ItersPerTerm.float
    totU += msU; totI += msI; totC += msC
    echo &"  {c.name:<22} unstaged={msU:>8.2f}  interp={msI:>8.2f}  " &
         &"compiled={msC:>8.2f} ms  (compiled/unstaged={msU/max(msC,1e-9):.2f}x)"
  echo ""
  echo &"Total per-iter: unstaged={totU:.2f} ms  interp-residual={totI:.2f} ms  " &
       &"compiled={totC:.2f} ms"
  echo &"Compiled vs unstaged speedup: {totU/max(totC,1e-9):.2f}x; " &
       &"compiled vs interpreted residual: {totI/max(totC,1e-9):.2f}x"
