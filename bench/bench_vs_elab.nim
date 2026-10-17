## bench_vs_elab.nim — Issue #19 acceptance criterion 4:
## wall-clock of the compiled staged typeo residual against the
## hand-written elaborator (src/elab.nim checkTm), on the same terms.
##
## Fairness design:
## - Same terms on both sides, each in its native representation
##   (RTerm S-exprs for the staged checker, PreTerm for the elaborator),
##   built once from a shared spec — no parsing or translation inside
##   the timed loop.
## - Staged side: stagedTypeo (compiled residual, ty=Nat static) through
##   the miniKanren engine at calibrated minimal depth.
## - Elaborator side: checkTm against Nat with a fresh MetaStore per
##   iteration (each check independent, as on the staged side).
## - Unstaged typeo timed as a third column for reference.
##
## Usage: nim c -r --path:src src/experimental/staging/bench_vs_elab.nim

import staging/relcompile   # stagedTypeoProcs macro + stagedTypeo template
import minikanren
import rel_elab
import elab
import preterm
import eponym_init
import unify
import tables
import times
import strformat

stagedTypeoProcs()

const MaxDepth = 25
const ItersPerTerm = 30
const Rounds = 2

# --- shared corpus ----------------------------------------------------

type Case = object
  name: string
  rtm: RTerm    # staged-side term (native representation)
  rctx: RTerm   # staged-side context
  pre: PreTerm  # elaborator-side term (native representation)
  ectx: Ctx     # elaborator-side context (innermost-first)
  expect: bool

proc sucN(n: int): RTerm =
  result = zeroTm()
  for _ in 1..n: result = sucTm(result)

proc buildCases(natTm, arrNN: Term): seq[Case] =
  # NOTE: the staged typeo fragment's variable rule only handles de Bruijn
  # index 0 (rel_elab.nim), so multi-variable contexts are inexpressible.
  # `add` is therefore the single context entry, applied to closed
  # literals — same workload shape as the issue's `add two two` example.
  let addCtxR = rpair(arrTy(natTy(), arrTy(natTy(), natTy())), rnil())
  let addCtxE = @[CtxEntry(name: "add", ty: arrNN)]
  let funCtxR = rpair(arrTy(natTy(), natTy()), rnil())
  let funCtxE = @[CtxEntry(name: "f", ty: tmPi(natTm, "_", natTm))]
  @[
    Case(name: "zero", rtm: zeroTm(), rctx: rnil(),
         pre: mkVar("zero"), ectx: @[], expect: true),
    Case(name: "suc^5", rtm: sucN(5), rctx: rnil(),
         pre: mkInt(5), ectx: @[], expect: true),
    Case(name: "suc^20", rtm: sucN(20), rctx: rnil(),
         pre: mkInt(20), ectx: @[], expect: true),
    Case(name: "app(lam(0),zero)", rtm: appTm(lamTm(varTm(0)), zeroTm()),
         rctx: rnil(),
         pre: mkApp(mkLam("x", nil, mkVar("x")), mkVar("zero")),
         ectx: @[], expect: true),
    Case(name: "var(0) in nat-ctx", rtm: varTm(0),
         rctx: rpair(natTy(), rnil()),
         pre: mkVar("a"), ectx: @[CtxEntry(name: "a", ty: natTm)],
         expect: true),
    # The issue's suggested workload, adapted to the fragment (see NOTE).
    Case(name: "add 2 2",
         rtm: appTm(appTm(varTm(0), sucN(2)), sucN(2)), rctx: addCtxR,
         pre: mkApp(mkApp(mkVar("add"), mkInt(2)), mkInt(2)),
         ectx: addCtxE, expect: true),
    Case(name: "add 10 10",
         rtm: appTm(appTm(varTm(0), sucN(10)), sucN(10)), rctx: addCtxR,
         pre: mkApp(mkApp(mkVar("add"), mkInt(10)), mkInt(10)),
         ectx: addCtxE, expect: true),
    Case(name: "app(f,5) f:Nat->Nat", rtm: appTm(varTm(0), sucN(5)),
         rctx: funCtxR,
         pre: mkApp(mkVar("f"), mkInt(5)),
         ectx: funCtxE, expect: true),
    Case(name: "lam(x.x) : Nat", rtm: lamTm(varTm(0)), rctx: rnil(),
         pre: mkLam("x", nil, mkVar("x")), ectx: @[], expect: false),
    Case(name: "var(0) in arr-ctx", rtm: varTm(0),
         rctx: rpair(arrTy(natTy(), natTy()), rnil()),
         pre: mkVar("f"),
         ectx: @[CtxEntry(name: "f", ty: tmPi(natTm, "_", natTm))],
         expect: false),
    Case(name: "suc(lam(x.x))", rtm: sucTm(lamTm(varTm(0))), rctx: rnil(),
         pre: mkApp(mkVar("suc"), mkLam("x", nil, mkVar("x"))),
         ectx: @[], expect: false),
  ]

# --- checkers ----------------------------------------------------------

proc checkUnstaged(tm, ctxTm: RTerm, depth: int): bool =
  let q = freshVar()
  let g = conj(typeo(tm, natTy(), ctxTm), `==`(q, ratom("yes")))
  run(q, g, 1, depth).len > 0

proc checkStaged(tm, ctxTm: RTerm, depth: int): bool =
  let q = freshVar()
  let g = conj(stagedTypeo(tm, ctxTm), `==`(q, ratom("yes")))
  run(q, g, 1, depth).len > 0

proc checkElab(pre: PreTerm, ectx: Ctx, globals: Globals,
               expTy: Term): bool =
  var ms = initMetaStore()
  var supply = Supply()
  try:
    discard checkTermElab(pre, ectx, globals, ms, supply, expTy)
    true
  except ElabError:
    false

proc calibrateDepth(cases: seq[Case]): int =
  ## Smallest depth where the staged checker stabilizes to its MaxDepth
  ## answers on every case (same honest-depth idea as bench_typeo).
  var oracle: seq[bool] = @[]
  for c in cases:
    oracle.add checkStaged(c.rtm, c.rctx, MaxDepth)
  for i, c in cases:
    if oracle[i] != c.expect:
      echo "WARNING: staged oracle disagrees with expectation on ", c.name,
           " (oracle=", oracle[i], ")"
  for d in 2..MaxDepth:
    var ok = true
    for i, c in cases:
      if checkStaged(c.rtm, c.rctx, d) != oracle[i]: ok = false; break
    if ok: return d
  MaxDepth

# --- main ---------------------------------------------------------------

when isMainModule:
  echo "=== Issue #19: compiled staged typeo vs hand-written elaborator ==="
  echo ""

  let tPre = cpuTime()
  let prelude = elabPrelude("""
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
""")
  echo &"Prelude elaboration (one-off): {(cpuTime() - tPre) * 1000:.1f} ms"
  let natTm = prelude.globals["Nat"].tm
  let arrNN = tmPi(natTm, "_", tmPi(natTm, "_", natTm))
  let globals = prelude.globals
  let cases = buildCases(natTm, arrNN)
  echo ""

  let depth = calibrateDepth(cases)
  echo "Calibrated depth: ", depth
  echo ""

  # Differential correctness: staged vs unstaged vs elaborator.
  echo "--- Differential correctness (depth ", depth, ") ---"
  var allAgree = true
  for c in cases:
    let u = checkUnstaged(c.rtm, c.rctx, depth)
    let s = checkStaged(c.rtm, c.rctx, depth)
    let e = checkElab(c.pre, c.ectx, globals, natTm)
    let agree = (u == s) and (s == e) and (e == c.expect)
    if not agree: allAgree = false
    echo &"  {c.name:<20} unstaged={u:<5} staged={s:<5} elab={e:<5} " &
         &"agree={agree} (expected {c.expect})"
  echo ""
  if allAgree:
    echo "PASS: all three agree on all ", cases.len, " terms."
  else:
    echo "FAIL: disagreement — do not trust timings."
    quit(1)
  echo ""

  # Wall-clock.
  echo "--- Wall-clock (", ItersPerTerm, " iters/term x ", Rounds,
       " rounds, depth ", depth, ") ---"
  var totE, totS, totU = 0.0
  for c in cases:
    var msE, msS, msU = 0.0
    for _ in 1..Rounds:
      discard checkElab(c.pre, c.ectx, globals, natTm)   # warmup
      discard checkStaged(c.rtm, c.rctx, depth)
      discard checkUnstaged(c.rtm, c.rctx, depth)
      let t0 = cpuTime()
      for _ in 1..ItersPerTerm:
        discard checkElab(c.pre, c.ectx, globals, natTm)
      msE += (cpuTime() - t0) * 1000 / ItersPerTerm.float
      let t1 = cpuTime()
      for _ in 1..ItersPerTerm:
        discard checkStaged(c.rtm, c.rctx, depth)
      msS += (cpuTime() - t1) * 1000 / ItersPerTerm.float
      let t2 = cpuTime()
      for _ in 1..ItersPerTerm:
        discard checkUnstaged(c.rtm, c.rctx, depth)
      msU += (cpuTime() - t2) * 1000 / ItersPerTerm.float
    msE /= Rounds.float; msS /= Rounds.float; msU /= Rounds.float
    totE += msE; totS += msS; totU += msU
    echo &"  {c.name:<20} elab={msE:>8.2f}  staged={msS:>8.2f}  " &
         &"unstaged={msU:>8.2f} ms  (elab/staged={msE/max(msS,1e-9):.2f}x)"
  echo ""
  echo &"Total per-iter: elab={totE:.2f} ms  staged={totS:.2f} ms  " &
       &"unstaged={totU:.2f} ms"
  echo &"Elaborator vs staged: {totE/max(totS,1e-9):.2f}x " &
       &"(>1 means staged is faster)"
  echo &"Staged vs unstaged: {totU/max(totS,1e-9):.2f}x"
