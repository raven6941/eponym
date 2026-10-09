## fuzz_soundness.nim — Issue #29: differential soundness testing
##
## Seeded generator produces goals over typeo/evalo plus small RelGoals
## exercising the staging rules (rgNeq/rgSetEq/rgBranch residualization,
## disjunction reification, capture-avoiding substitution). Each goal runs
## against (a) the unstaged relational engine and (b) the stageGoal-derived
## residual; the reified answer sets (order-insensitive, logic-var ids
## canonicalized) must agree.
##
## On divergence: shrink to a minimal failing case, print the seed and the
## minimal case, exit 1.
##
## Fixed-seed suite (CI):   nim c -r --path:src src/staging/fuzz_soundness.nim -- --seed 424242 -n 1000
## Fresh-seed fuzz (local): nim c -r --path:src src/staging/fuzz_soundness.nim -- --seed random -n 5000
##
## Search is bounded (FuzzDepth/FuzzN), so every goal terminates; a goal
## that hits the answer cap is reported as capped (inconclusive), never as
## agreement or divergence.

import staging/relgoal
import staging/stagegoal
import staging/stage_typeo   # typeoData
import staging/stage_evalo   # evaloData, addoData
import staging/modes
import minikanren
import rel_elab
import rel_interp
import tables
import sets
import strutils
import sequtils
import algorithm
import times
import os

const FuzzDepth = 10   # iterative-deepening bound per run
const FuzzN = 10       # max answers compared per goal
const ShrinkRounds = 40

# --- Seeded RNG (xorshift64*, deterministic across platforms) -------------

type Rng = object
  s: uint64

proc initRng(seed: uint64): Rng =
  var s = seed
  if s == 0: s = 0x9E3779B97F4A7C15'u64
  Rng(s: s)

proc next(r: var Rng): uint64 =
  var x = r.s
  x = x xor (x shr 12)
  x = x xor (x shl 25)
  x = x xor (x shr 27)
  r.s = x
  x * 0x2545F4914F6CDD1D'u64

proc below(r: var Rng, n: int): int =
  ## Uniform-ish int in [0, n). Modulo bias is irrelevant for fuzzing.
  (r.next() mod n.uint64).int

# --- Generators -----------------------------------------------------------

proc genType(r: var Rng, depth: int): RTerm =
  if depth <= 0 or r.below(2) == 0: natTy()
  else: arrTy(genType(r, depth - 1), genType(r, depth - 1))

proc genTm(r: var Rng, depth: int, maxVar: int): RTerm =
  ## STLC+Nat terms: zero | suc | var | lam | app.
  if depth <= 0:
    if r.below(2) == 0: zeroTm() else: varTm(r.below(maxVar + 1))
  else:
    case r.below(6)
    of 0: zeroTm()
    of 1: sucTm(genTm(r, depth - 1, maxVar))
    of 2: varTm(r.below(maxVar + 1))
    of 3: lamTm(genTm(r, depth - 1, maxVar))
    of 4: appTm(genTm(r, depth - 1, maxVar), genTm(r, depth - 1, maxVar))
    else: sucTm(genTm(r, depth - 1, maxVar))

proc genCtx(r: var Rng): RTerm =
  var elems = newSeq[RTerm]()
  for _ in 0 ..< r.below(3):
    elems.add(genType(r, 1))
  rlist(elems)

proc genArithTm(r: var Rng, depth: int): RTerm =
  ## evalo terms: zero | suc | add (mul is out of scope for the staged
  ## evaloData on main; the generator covers exactly the staged fragment).
  if depth <= 0 or r.below(4) == 0: zeroTm()
  else:
    case r.below(3)
    of 0: sucTm(genArithTm(r, depth - 1))
    of 1: addTm(genArithTm(r, depth - 1), genArithTm(r, depth - 1))
    else: sucTm(genArithTm(r, depth - 1))

proc genGroundN(r: var Rng): RTerm =
  ## Tiny ground values for rule-level goals.
  case r.below(4)
  of 0: zeroTm()
  of 1: sucTm(zeroTm())
  of 2: rint(r.below(3))
  else: sucTm(sucTm(zeroTm()))

proc genRuleAtom(r: var Rng, pool: seq[string]): RelGoal =
  ## One staging-rule-relevant atom over the placeholder pool:
  ## head-constructor eq, nested binding, recursive-call shapes via the
  ## helper relations, plus =/=, setEqo, branch (always-residualized).
  ## Discipline: binder names (u/v) only occur under their rgFresh, so
  ## every *free* placeholder is dynamic (__var_x/__var_y) — the same
  ## discipline as the hand-staged relations.
  let x = ratom("__var_" & pool[r.below(pool.len)])
  let y = ratom("__var_" & pool[r.below(pool.len)])
  case r.below(10)
  of 0: rgEq(x, genGroundN(r))
  of 1: rgEq(y, genGroundN(r))
  of 2: rgEq(x, y)
  of 3: rgEq(x, sucTm(y))
  of 4: rgNeq(x, genGroundN(r))
  of 5: rgNeq(x, y)
  of 6: rgCall("isZero", @[x])
  of 7: rgCall("plus1", @[x, y])
  of 8: RelGoal(kind: rgSetEq, cells: @[x], values: @[genGroundN(r)])
  else: RelGoal(kind: rgBranch, vars: @[x, y])

proc genRuleGoal(r: var Rng, depth: int, pool: seq[string]): RelGoal =
  if depth <= 0: return genRuleAtom(r, pool)
  case r.below(9)
  of 0: genRuleAtom(r, pool)
  of 1: rgConj(genRuleGoal(r, depth - 1, pool), genRuleGoal(r, depth - 1, pool))
  of 2: rgDisj(genRuleGoal(r, depth - 1, pool), genRuleGoal(r, depth - 1, pool))
  of 3:
    let b = if r.below(2) == 0: "u" else: "v"
    rgFresh(b, genRuleGoal(r, depth - 1, pool & @[b]))
  of 4: rgCall("plus1", @[ratom("__var_" & pool[r.below(pool.len)]),
                          genGroundN(r)])
  of 5: rgDisj(genRuleAtom(r, pool), genRuleGoal(r, depth - 1, pool))
  of 6:
    # Sequential same-name binders: the env-pollution stress case.
    # (fresh u. u==zero) ∧ (fresh u. u==suc(zero)) is satisfiable;
    # a flat staging env leaks the first binding into the second.
    rgConj(rgFresh("u", genRuleAtom(r, @["x", "y", "u"])),
           rgFresh("u", genRuleAtom(r, @["x", "y", "u"])))
  of 7: rgFresh("x", genRuleGoal(r, depth - 1, pool))  # shadows dynamic var
  else: genRuleAtom(r, pool)

# --- Staged variants (built once) ------------------------------------------

type StagedRel = tuple[top: string, specs: Table[string, RelEntry]]

proc buildStagedCheck(): StagedRel =
  ## stageGoal-specialized typeo, ty=nat static (mirrors bench_typeo).
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mIn, mIn], body: typeoData())
  var ctx = newSpecCtx(relEnv, fuel = 8)
  var staticParams = initTable[string, RTerm]()
  staticParams["ty"] = natTy()
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")
  (specializeRelation(ctx, "typeo", staticParams, dynamicVars), ctx.specs)

proc buildStagedSynth(): StagedRel =
  ## stageGoal-specialized typeo, fully dynamic (tm:mIn, ty:mOut, ctx:mIn).
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mOut, mIn], body: typeoData())
  var ctx = newSpecCtx(relEnv, fuel = 8)
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ty")
  dynamicVars.incl("__var_ctx")
  (specializeRelation(ctx, "typeo", initTable[string, RTerm](), dynamicVars),
   ctx.specs)

proc buildStagedEvalo(): StagedRel =
  ## stageGoal-specialized evalo, fully dynamic; addo in relEnv so the
  ## residual's addo calls resolve at toGoal time.
  var relEnv = initTable[string, RelDef]()
  relEnv["evalo"] = RelDef(name: "evalo", params: @["tm", "v"],
                           modes: @[mIn, mOut], body: evaloData())
  relEnv["addo"] = RelDef(name: "addo", params: @["a", "b", "c"],
                          modes: @[mIn, mIn, mOut], body: addoData())
  var ctx = newSpecCtx(relEnv, fuel = 8)
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_v")
  (specializeRelation(ctx, "evalo", initTable[string, RTerm](), dynamicVars),
   ctx.specs)

proc ruleHelperEnvs(): (Table[string, RelDef], Table[string, RelEntry]) =
  ## Helper relations for rule-level goals, as defs (staging input) and
  ## entries (toGoal input).
  let isZeroBody = rgEq(ratom("__var_x"), zeroTm())
  let plus1Body = rgEq(ratom("__var_y"), sucTm(ratom("__var_x")))
  var defs = initTable[string, RelDef]()
  defs["isZero"] = RelDef(name: "isZero", params: @["x"],
                          modes: @[mIn], body: isZeroBody)
  defs["plus1"] = RelDef(name: "plus1", params: @["x", "y"],
                         modes: @[mIn, mOut], body: plus1Body)
  var entries = initTable[string, RelEntry]()
  entries["isZero"] = RelEntry(params: @["x"], body: isZeroBody)
  entries["plus1"] = RelEntry(params: @["x", "y"], body: plus1Body)
  (defs, entries)

# --- Answer comparison ------------------------------------------------------

proc canonVarIds(s: string): string =
  ## Rename ?v<id> to ?v0,?v1,... in order of first appearance, so staged
  ## vs unstaged runs (different fresh-counter states) compare equal.
  var mapping = initTable[string, int]()
  var nextId = 0
  result = ""
  var i = 0
  while i < s.len:
    if s[i] == '?' and i + 1 < s.len and s[i + 1] == 'v':
      var j = i + 2
      while j < s.len and s[j] in {'0'..'9'}: inc j
      let tok = s[i ..< j]
      if tok notin mapping:
        mapping[tok] = nextId
        inc nextId
      result.add("?v" & $mapping[tok])
      i = j
    else:
      result.add(s[i])
      inc i

proc answers(q: RTerm, g: Goal, n: int = FuzzN):
    tuple[capped: bool, ans: seq[string]] =
  ## Take up to 4n raw answers, then canonicalize logic-var ids and dedup.
  ## (Iterative deepening mints fresh var ids per depth level, so raw
  ## answer strings over-count: the same answer reappears as ?v7, ?v23,
  ## ... Reporting capped on the raw count would cry wolf.)
  ## Capped now means: n genuinely distinct answers were found.
  let rs = run(q, g, 4 * n, FuzzDepth)
  var seen = initHashSet[string]()
  var canon: seq[string] = @[]
  for t in rs:
    let k = canonVarIds($t)
    if k notin seen:
      seen.incl(k)
      canon.add(k)
  (canon.len >= n, canon.sorted())

# --- Per-shape differentials -------------------------------------------------
#
# Each returns (capped, unstaged, staged); the driver treats capped as
# inconclusive and compares the answer sets otherwise.

proc diffCheck(sr: StagedRel, tm, ctxTm: RTerm):
    tuple[capped: bool, u, s: seq[string]] =
  let qu = freshVar()
  let uu = run(qu, conj(typeo(tm, natTy(), ctxTm), `==`(qu, ratom("yes"))),
               1, FuzzDepth)
  let qs = freshVar()
  let ss = run(qs, conj(toGoal(rgCall(sr.top, @[tm, natTy(), ctxTm]), sr.specs),
                       `==`(qs, ratom("yes"))), 1, FuzzDepth)
  (false, uu.mapIt($it), ss.mapIt($it))

proc diffSynth(sr: StagedRel, tm, ctxTm: RTerm):
    tuple[capped: bool, u, s: seq[string]] =
  let qu = freshVar()
  let (cu, au) = answers(qu, typeo(tm, qu, ctxTm))
  let qs = freshVar()
  let (cs, aseq) = answers(qs, toGoal(rgCall(sr.top, @[tm, qs, ctxTm]), sr.specs))
  (cu or cs, au, aseq)

proc diffEvalo(sr: StagedRel, tm: RTerm):
    tuple[capped: bool, u, s: seq[string]] =
  let qu = freshVar()
  let (cu, au) = answers(qu, evalo(tm, qu))
  let qs = freshVar()
  let (cs, aseq) = answers(qs, toGoal(rgCall(sr.top, @[tm, qs]), sr.specs))
  (cu or cs, au, aseq)

proc diffRule(g: RelGoal, defs: Table[string, RelDef],
              entries: Table[string, RelEntry]):
    tuple[capped: bool, u, s: seq[string]] =
  ## Instantiate placeholders with fresh engine vars, then compare the
  ## original goal against the stageGoal residual (also instantiated).
  let X = freshVar()
  let Y = freshVar()
  let q = rlist(@[X, Y])
  let gi = substAtom(substAtom(g, ratom("__var_x"), X), ratom("__var_y"), Y)
  # Rule goals branch more than term queries; compare deeper before
  # calling a goal capped (inconclusive).
  const RuleN = 40
  let (cu, au) = answers(q, toGoal(gi, entries), RuleN)
  var sctx = newSpecCtx(defs, fuel = 6)
  var env = initTable[string, RTerm]()
  var dyn = initHashSet[string]()
  dyn.incl("__var_x")
  dyn.incl("__var_y")
  let staged = stageGoal(g, env, dyn, sctx)
  var resid: RelGoal
  case staged.kind
  of sgDone: resid = rgSucceed()
  of sgFail: resid = rgFail()
  of sgResidual: resid = staged.goal
  # toGoal env: original entries + specializations the stager produced.
  var goalEnv = entries
  for name, e in sctx.specs: goalEnv[name] = e
  let gr = substAtom(substAtom(resid, ratom("__var_x"), X),
                     ratom("__var_y"), Y)
  let (cs, aseq) = answers(q, toGoal(gr, goalEnv), RuleN)
  (cu or cs, au, aseq)

# --- Shrinking ----------------------------------------------------------------

proc ctorOf(t: RTerm): string =
  if t.kind == rkPair and t.head.kind == rkAtom: t.head.name else: ""

proc argsOf(t: RTerm): seq[RTerm] =
  result = @[]
  var cur = if t.kind == rkPair: t.tail else: t
  while cur.kind == rkPair:
    result.add(cur.head)
    cur = cur.tail

proc shrinkTm(t: RTerm): seq[RTerm] =
  ## Simpler candidate terms, simplest first (deduped by printed form —
  ## sequtils.deduplicate would resolve `==` to the miniKanren goal).
  var cands = @[zeroTm()]
  let a = argsOf(t)
  case ctorOf(t)
  of "suc", "lam":
    if a.len >= 1: cands.add(a[0])
  of "app", "add":
    if a.len >= 2:
      cands.add(a[0])
      cands.add(a[1])
  of "var": discard
  else: discard
  var seen = initHashSet[string]()
  for c in cands:
    let k = $c
    if k notin seen:
      seen.incl(k)
      result.add(c)

proc shrinkCtx(c: RTerm): seq[RTerm] =
  result = @[rnil()]
  let elems = argsOf(c)
  for i in 0 ..< elems.len:
    var rest = elems
    rest.delete(i)
    result.add(rlist(rest))

proc shrinkRuleGoal(g: RelGoal): seq[RelGoal] =
  case g.kind
  of rgConj: @[g.leftG, g.rightG, rgSucceed()]
  of rgDisj: @[g.leftG, g.rightG, rgSucceed()]
  of rgFresh: @[g.body, rgSucceed()]
  else: @[rgSucceed()]

# --- Driver --------------------------------------------------------------------

type
  Shape = enum
    shCheck = 0, shSynth, shPartial, shEvalo, shRule

proc shapeName(s: Shape): string =
  case s
  of shCheck: "typeo-check"
  of shSynth: "typeo-synth"
  of shPartial: "typeo-partial"
  of shEvalo: "evalo"
  of shRule: "rule-level"

proc diverges(shape: Shape, tm, ctxTm: RTerm, rg: RelGoal,
              checkRel, synthRel, evaloRel: StagedRel,
              defs: Table[string, RelDef],
              entries: Table[string, RelEntry]):
    tuple[isDiv: bool, capped: bool, u, s: seq[string]] =
  var capped = false
  var u, s: seq[string]
  case shape
  of shCheck:
    let d = diffCheck(checkRel, tm, ctxTm)
    (capped, u, s) = (d.capped, d.u, d.s)
  of shSynth:
    let d = diffSynth(synthRel, tm, ctxTm)
    (capped, u, s) = (d.capped, d.u, d.s)
  of shPartial:
    # app(lam(0), q) : nat with q ranging over a small finite domain
    # (one candidate ill-typed, so it must be filtered). A logic var in a
    # checkable position flowing through the staged app/lam branches;
    # answers are finite, so set comparison is honest.
    let q = freshVar()
    let domU = disj(`==`(q, zeroTm()),
               disj(`==`(q, sucTm(zeroTm())), `==`(q, lamTm(zeroTm()))))
    # NOTE: the domain constraint goes first — otherwise typeo runs in
    # synthesis mode and enumerates nat inhabitants for q (infinite
    # generate-and-test). With q ground, both sides just check.
    let (cu, au) = answers(q, conj(domU, typeo(appTm(lamTm(varTm(0)), q),
                                               natTy(), ctxTm)))
    let qr = freshVar()
    let domS = disj(`==`(qr, zeroTm()),
               disj(`==`(qr, sucTm(zeroTm())), `==`(qr, lamTm(zeroTm()))))
    let goalS = conj(domS, toGoal(rgCall(checkRel.top,
        @[appTm(lamTm(varTm(0)), qr), natTy(), ctxTm]), checkRel.specs))
    let (cs, aseq) = answers(qr, goalS)
    (capped, u, s) = (cu or cs, au, aseq)
  of shEvalo:
    let d = diffEvalo(evaloRel, tm)
    (capped, u, s) = (d.capped, d.u, d.s)
  of shRule:
    let d = diffRule(rg, defs, entries)
    (capped, u, s) = (d.capped, d.u, d.s)
  (isDiv: not capped and u != s, capped: capped, u: u, s: s)

proc shrink(shape: Shape, tm, ctxTm: RTerm, rg: RelGoal,
            checkRel, synthRel, evaloRel: StagedRel,
            defs: Table[string, RelDef],
            entries: Table[string, RelEntry]):
    tuple[tm: RTerm, ctxTm: RTerm, rg: RelGoal] =
  ## Greedy delta debugging: repeatedly take the first simpler candidate
  ## that still diverges.
  var ctm = tm
  var cctx = ctxTm
  var crg = rg
  for _ in 1..ShrinkRounds:
    var progressed = false
    case shape
    of shRule:
      for cand in shrinkRuleGoal(crg):
        let d = diverges(shape, ctm, cctx, cand, checkRel, synthRel,
                         evaloRel, defs, entries)
        if d.isDiv and not d.capped:
          crg = cand
          progressed = true
          break
    else:
      for cand in shrinkTm(ctm):
        let d = diverges(shape, cand, cctx, crg, checkRel, synthRel,
                         evaloRel, defs, entries)
        if d.isDiv and not d.capped:
          ctm = cand
          progressed = true
          break
      if not progressed and shape in {shCheck, shSynth, shPartial}:
        for cand in shrinkCtx(cctx):
          let d = diverges(shape, ctm, cand, crg, checkRel, synthRel,
                           evaloRel, defs, entries)
          if d.isDiv and not d.capped:
            cctx = cand
            progressed = true
            break
    if not progressed: break
  (ctm, cctx, crg)

proc goalDesc(shape: Shape, tm, ctxTm: RTerm, rg: RelGoal): string =
  case shape
  of shRule: "goal: " & $rg
  of shPartial:
    "goal: typeo(app(lam(0), q), nat) with q in {zero, suc(zero), lam(zero)}" &
    "  ctx: " & $ctxTm
  else: "tm: " & $tm & "  ctx: " & $ctxTm

proc runRegression(checkRel, synthRel, evaloRel: StagedRel,
                   defs: Table[string, RelDef],
                   entries: Table[string, RelEntry]): bool =
  ## Fixed regression goals, run before the random suite. Includes the
  ## divergence the fuzzer found on 2026-10-09: stageGoal's rgFresh leaked
  ## the inner binder's staging-time binding into the shared env, so
  ## (fresh u. u==zero) ∧ (fresh u. u==suc(zero)) staged to Fail.
  result = true
  let x = ratom("__var_x")
  let u = ratom("__var_u")
  let regs = @[
    ("seq-binders",
     rgConj(rgFresh("u", rgEq(u, zeroTm())),
            rgFresh("u", rgEq(u, sucTm(zeroTm()))))),
    ("nested-shadow",
     rgFresh("x", rgConj(rgEq(x, zeroTm()),
                         rgFresh("x", rgEq(x, sucTm(zeroTm())))))),
    ("disj-keep-both",
     rgDisj(rgEq(x, rint(1)), rgEq(x, rint(2)))),
    ("fresh-propagates-outer",
     rgConj(rgFresh("u", rgConj(rgEq(u, zeroTm()), rgEq(x, sucTm(u)))),
            rgEq(x, sucTm(zeroTm())))),
  ]
  for (name, g) in regs:
    let d = diffRule(g, defs, entries)
    if d.capped:
      echo "  regression ", name, ": capped (inconclusive)"
    elif d.u != d.s:
      echo "  regression ", name, ": DIVERGENCE"
      echo "    unstaged: ", d.u
      echo "    staged:   ", d.s
      result = false
    else:
      echo "  regression ", name, ": agree ", d.u
  # A typeo spot check through each staged variant (ground truth: the
  # 9-case bench corpus expectations).
  let spotTm = appTm(lamTm(varTm(0)), zeroTm())
  let dc = diffCheck(checkRel, spotTm, rnil())
  if dc.u != dc.s or dc.u != @["yes"]:
    echo "  regression typeo-spot-check: DIVERGENCE ", dc.u, " vs ", dc.s
    result = false
  else:
    echo "  regression typeo-spot-check: agree"
  let de = diffEvalo(evaloRel, addTm(sucTm(zeroTm()), sucTm(zeroTm())))
  if de.u != de.s or de.u != @["(suc (suc zero))"]:
    echo "  regression evalo-spot: DIVERGENCE ", de.u, " vs ", de.s
    result = false
  else:
    echo "  regression evalo-spot: agree ", de.u

when isMainModule:
  var seedStr = "424242"
  var n = 1000
  var i = 1
  while i <= paramCount():
    let a = paramStr(i)
    if a == "--":
      discard  # separator leaked through by `nim c -r --`; skip
    elif a == "--seed" and i < paramCount():
      inc i
      seedStr = paramStr(i)
    elif (a == "--n" or a == "-n") and i < paramCount():
      inc i
      n = parseInt(paramStr(i))
    elif a == "--help" or a == "-h":
      echo "usage: fuzz_soundness [--seed N|random] [--n N]"
      quit(0)
    else:
      echo "unknown arg: ", a
      quit(2)
    inc i

  var seed: uint64
  if seedStr == "random":
    let t = getTime()
    seed = cast[uint64](t.toUnix()) * 1_000_000_007'u64 +
           cast[uint64](t.nanosecond)
    echo "random seed: ", seed
  else:
    seed = parseUInt(seedStr).uint64

  echo "=== Issue #29: differential soundness fuzzing ==="
  echo "seed=", seed, " n=", n
  echo ""

  let tBuild = cpuTime()
  let checkRel = buildStagedCheck()
  let synthRel = buildStagedSynth()
  let evaloRel = buildStagedEvalo()
  let (defs, entries) = ruleHelperEnvs()
  echo "staged variants built in ", (cpuTime() - tBuild) * 1000, " ms"
  echo "  check: ", checkRel.top, " (+", checkRel.specs.len - 1, " more)"
  echo "  synth: ", synthRel.top, " (+", synthRel.specs.len - 1, " more)"
  echo "  evalo: ", evaloRel.top, " (+", evaloRel.specs.len - 1, " more)"
  echo ""

  echo "--- fixed regression goals ---"
  if not runRegression(checkRel, synthRel, evaloRel, defs, entries):
    echo "FAIL: fixed regression goals diverge."
    quit(1)
  echo ""

  var r = initRng(seed)
  var ran = 0
  var capped = 0
  var divergences = 0
  var perShape = [0, 0, 0, 0, 0]
  var cappedShape = [0, 0, 0, 0, 0]
  let t0 = cpuTime()
  for iter in 1..n:
    let shape = Shape(r.below(5))
    let tm =
      case shape
      of shEvalo: genArithTm(r, 4)
      of shRule: zeroTm()  # unused for rule shape
      else: genTm(r, 4, 1)
    let ctxTm = genCtx(r)
    let rg = if shape == shRule: genRuleGoal(r, 3, @["x", "y"])
               else: rgSucceed()
    inc perShape[shape.ord]
    let d = diverges(shape, tm, ctxTm, rg, checkRel, synthRel, evaloRel,
                     defs, entries)
    if d.capped:
      inc capped
      inc cappedShape[shape.ord]
      continue
    inc ran
    if d.isDiv:
      inc divergences
      echo "--- DIVERGENCE #", divergences, " (iter ", iter, ", shape ",
           shapeName(shape), ") ---"
      echo "  original: ", goalDesc(shape, tm, ctxTm, rg)
      echo "  unstaged: ", d.u
      echo "  staged:   ", d.s
      let m = shrink(shape, tm, ctxTm, rg, checkRel, synthRel, evaloRel,
                     defs, entries)
      echo "  minimal:  ", goalDesc(shape, m.tm, m.ctxTm, m.rg)
      echo "  reproduce: --seed ", seed, " (iter ", iter, ")"
      echo ""
  let ms = (cpuTime() - t0) * 1000
  echo "=== summary ==="
  echo "goals: ", n, "  compared: ", ran, "  capped(inconclusive): ", capped,
       "  divergences: ", divergences
  echo "per shape: check=", perShape[0], " synth=", perShape[1],
       " partial=", perShape[2], " evalo=", perShape[3],
       " rule=", perShape[4]
  echo "capped per shape: check=", cappedShape[0], " synth=", cappedShape[1],
       " partial=", cappedShape[2], " evalo=", cappedShape[3],
       " rule=", cappedShape[4]
  echo "time: ", ms, " ms (", ms / max(n.float, 1.0), " ms/goal)"
  if divergences > 0:
    echo "FAIL: staged/unstaged divergences found."
    quit(1)
  echo "PASS: staged and unstaged agree on all compared goals."
