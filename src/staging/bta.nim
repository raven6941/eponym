## Binding-time analysis for relational staging (issue #31)
##
## Computes the static/dynamic fallback boundary instead of hand-drawing it.
##
## Hand-drawn fallback inventory (issue #31, step 1) — every place where a
## human currently decides what is static vs dynamic, and what static
## information each decision depends on:
##
## 1. Staging *entry* (stage_typeo.nim, bench_typeo.nim): `staticParams["ty"]
##    = natTy()`, `dynamicVars = {__var_tm, __var_ctx}`. Depends on knowing
##    the query pattern — which top-level args are ground at staging time.
##    NOW COMPUTED by `inferEntry` from the relation's modes + the known
##    args. This was the only hand-drawn input to the stageGoal pipeline.
## 2. Per-specialization dynamic params (stagegoal.nim rgCall case): dynamic
##    params join dynamicVars automatically — already computed, BTA reports
##    each call's static/dynamic signature via `analyzeBoundary`.
## 3. rgNeq / rgSetEq / rgBranch (stagegoal.nim): always residualize.
##    Conservative hand choice; depends on the *absence* of staging-time
##    disequality/constraint reasoning. BTA surfaces each as a fallback
##    point with its reason instead of hiding it in the code.
## 4. staged_synth.nim `synthNat`: fully hand-written; the app branch is a
##    hand-drawn fallback to interpretive typeo. Legacy prototype,
##    superseded by the stageGoal derivation — not touched by BTA.
## 5. staged_codegen.nim: macro emits only the zero/suc fragment — the
##    fragment choice is the author's. Legacy prototype.
## 6. staged_fwd.nim `inferType`: lam/vecnil raise "needs expected type" —
##    hand-drawn fallback points of the forward direction (would fall back
##    to bidirectional checking). Legacy prototype.
## 7. Fuel default (8): hand-chosen specialization budget. Orthogonal to
##    binding times; BTA does not change it.
##
## What this module adds:
## - `inferEntry`: entry annotation (staticParams, dynamicVars) derived from
##   modes + known-static args. Grounds the issue's definition: static =
##   known at staging time (ground subterms); dynamic = residualized (mOut
##   params, unknowns).
## - `analyzeBoundary`: abstract interpretation of a RelGoal body over the
##   entry annotation. Every subgoal gets a verdict — discharged / pruned /
##   fallback / specialize — plus *which* dynamic placeholders' unknown
##   values force each fallback. The boundary becomes inspectable data.
## - `stageWithBTA`: entry inference piped into specializeRelation: staged
##   typeo with zero manual markers.
## - `boundaryReport`: human-readable rendering of the computed boundary.
##
## The abstract interpreter mirrors stageGoal's rules (same env threading:
## bound/dynamic/free placeholders, branch-local disjunction envs,
## constructor decomposition in unification), so its verdicts agree with
## what the specializer will actually do. Agreement is tested, not assumed:
## the BTA-derived residual must be syntactically identical to the
## hand-drawn residual, and both must agree with unstaged typeo on the
## differential corpus.

import staging/relgoal
import staging/stagegoal
import staging/modes
import minikanren
import tables
import sets
import sequtils
import strutils

# ---------------------------------------------------------------------------
# Verdicts and notes

type
  BTAVerdict* = enum
    bvDischarged  ## decided at staging time (no residual)
    bvPruned      ## statically impossible (branch eliminated)
    bvFallback    ## residualized: needs static info unavailable at staging
    bvSpecialize  ## relation call: static/dynamic signature computed

  BTANote* = object
    goal*: string       ## the subgoal (or summary scope) this note is about
    verdict*: BTAVerdict
    reason*: string     ## why this verdict
    missing*: seq[string] ## dynamic placeholders whose unknown value forces
                          ## the fallback (empty unless verdict == bvFallback)

# ---------------------------------------------------------------------------
# Abstract binding-time environment
#
# Mirrors stageGoal's (staticEnv, dynamicVars) pair:
# - bound: __var_<name> -> abstract term (may mention dynamic placeholders,
#   exactly like stageGoal's staticEnv values can)
# - dyn: placeholders that must NOT be observed at staging time
#   (runtime inputs / mOut params)
# - free: placeholders in neither (fresh binders start here; bindable)

proc isPH(t: RTerm): bool =
  t.kind == rkAtom and t.name.startsWith("__var_")

proc btaDeref(t: RTerm, bound: Table[string, RTerm]): RTerm =
  ## Chase bound placeholders. Bindings are acyclic (occurs-check on bind).
  case t.kind
  of rkAtom:
    if isPH(t) and t.name in bound: btaDeref(bound[t.name], bound)
    else: t
  of rkPair:
    rpair(btaDeref(t.head, bound), btaDeref(t.tail, bound))
  of rkVar:
    t

proc phNames(t: RTerm): HashSet[string] =
  ## All __var_ placeholder names occurring in t.
  result = initHashSet[string]()
  var stack = @[t]
  while stack.len > 0:
    let x = stack.pop()
    case x.kind
    of rkAtom:
      if x.name.startsWith("__var_"): result.incl(x.name)
    of rkPair:
      stack.add(x.head); stack.add(x.tail)
    of rkVar: discard

proc isGroundBT(t: RTerm): bool =
  ## Fully ground: no placeholders, no engine logic vars.
  case t.kind
  of rkAtom: not t.name.startsWith("__var_")
  of rkPair: isGroundBT(t.head) and isGroundBT(t.tail)
  of rkVar: false

proc termDyn(t: RTerm, bound: Table[string, RTerm],
             dyn: HashSet[string]): HashSet[string] =
  ## Dynamic placeholders mentioned by t (after deref): the "missing
  ## static info" for any equation that needs t's value at staging time.
  ## Free placeholders are bindable, so they don't count.
  result = initHashSet[string]()
  for p in phNames(btaDeref(t, bound)):
    if p in dyn: result.incl(p)

# ---------------------------------------------------------------------------
# Abstract unification (mirrors stagegoal.unifyStage, with reasons)

proc btaUnify(a, b: RTerm, bound: var Table[string, RTerm],
              dyn: HashSet[string]):
    tuple[verdict: BTAVerdict, reason: string, missing: seq[string]] =
  let a2 = btaDeref(a, bound)
  let b2 = btaDeref(b, bound)
  if a2.kind == rkVar or b2.kind == rkVar:
    return (bvFallback, "engine logic var: undecidable at staging", @[])
  if isPH(a2):
    if a2.name in dyn:
      if isPH(b2) and b2.name == a2.name:
        return (bvDischarged, "same dynamic var", @[])
      return (bvFallback, "needs the value of dynamic " & a2.name,
              @[a2.name])
    if isPH(b2) and b2.name == a2.name:
      return (bvDischarged, "trivially equal", @[])
    if a2.name in phNames(b2):
      return (bvFallback, "cyclic equation: " & a2.name & " occurs in " & $b2,
              @[a2.name])
    bound[a2.name] = b2
    let m = toSeq(termDyn(b2, bound, dyn))
    return (bvDischarged, "bound " & a2.name & " at staging" &
              (if m.len > 0: "; value mentions dynamic " & m.join(", ") else: ""),
            m)
  if isPH(b2):
    if b2.name in dyn:
      return (bvFallback, "needs the value of dynamic " & b2.name,
              @[b2.name])
    if b2.name in phNames(a2):
      return (bvFallback, "cyclic equation: " & b2.name & " occurs in " & $a2,
              @[b2.name])
    bound[b2.name] = a2
    let m = toSeq(termDyn(a2, bound, dyn))
    return (bvDischarged, "bound " & b2.name & " at staging" &
              (if m.len > 0: "; value mentions dynamic " & m.join(", ") else: ""),
            m)
  if a2.kind != b2.kind:
    return (bvPruned, "kind mismatch (" & $a2.kind & " vs " & $b2.kind & ")", @[])
  case a2.kind
  of rkAtom:
    if a2.name == b2.name: (bvDischarged, "equal ground atoms", @[])
    else: (bvPruned, "atom mismatch: " & a2.name & " vs " & b2.name, @[])
  of rkPair:
    let (vh, rh, mh) = btaUnify(a2.head, b2.head, bound, dyn)
    if vh == bvPruned: return (bvPruned, "head: " & rh, mh)
    let (vt, rt, mt) = btaUnify(a2.tail, b2.tail, bound, dyn)
    if vt == bvPruned: return (bvPruned, "tail: " & rt, mt)
    if vh == bvFallback or vt == bvFallback:
      var m = mh
      for x in mt:
        if x notin m: m.add(x)
      return (bvFallback, "head: " & rh & "; tail: " & rt, m)
    (bvDischarged, "constructor match", @[])
  of rkVar:
    (bvFallback, "unreachable", @[])  # handled above; keeps compiler quiet

# ---------------------------------------------------------------------------
# Abstract interpretation of RelGoal

proc freshPHs(rg: RelGoal): HashSet[string] =
  ## __var_ names bound by rgFresh binders in rg.
  result = initHashSet[string]()
  case rg.kind
  of rgFresh:
    result.incl("__var_" & rg.varName)
    result = result + freshPHs(rg.body)
  of rgConj, rgDisj:
    result = result + freshPHs(rg.leftG) + freshPHs(rg.rightG)
  else: discard

proc newBindings(bNew, bOld: Table[string, RTerm],
                 exclude: HashSet[string]): seq[string] =
  ## Placeholder names bound in bNew but not bOld, minus excluded
  ## (fresh binders are branch-internal, not observable).
  for k in bNew.keys:
    if k notin bOld and k notin exclude: result.add(k)

proc branchNotesAll(notes: seq[BTANote], lo, hi: int,
                    v: BTAVerdict): bool =
  for i in lo ..< hi:
    if notes[i].verdict != v: return false
  true

proc btaGoal(rg: RelGoal, bound: var Table[string, RTerm],
             dyn: HashSet[string], notes: var seq[BTANote]): bool =
  ## Analyze rg under the abstract env; append per-subgoal notes.
  ## Returns true iff rg is statically dead (impossible).
  ## Mirrors stageGoal's env threading, including branch-local
  ## disjunction envs and the no-observable-bindings commit rule.
  case rg.kind
  of rgFail:
    notes.add BTANote(goal: $rg, verdict: bvPruned, reason: "fail")
    true
  of rgSucceed:
    notes.add BTANote(goal: $rg, verdict: bvDischarged, reason: "succeed")
    false
  of rgEq:
    let (v, r, m) = btaUnify(rg.left, rg.right, bound, dyn)
    notes.add BTANote(goal: $rg, verdict: v, reason: r, missing: m)
    v == bvPruned
  of rgNeq:
    let m = toSeq(termDyn(rg.left, bound, dyn) + termDyn(rg.right, bound, dyn))
    notes.add BTANote(goal: $rg, verdict: bvFallback,
      reason: "disequality: always residualized (conservative — no " &
              "staging-time =/= reasoning)",
      missing: m)
    false
  of rgConj:
    if btaGoal(rg.leftG, bound, dyn, notes): return true
    btaGoal(rg.rightG, bound, dyn, notes)
  of rgDisj:
    var bL = bound
    var bR = bound
    let n0 = notes.len
    let dl = btaGoal(rg.leftG, bL, dyn, notes)
    let n1 = notes.len
    let dr = btaGoal(rg.rightG, bR, dyn, notes)
    if dl and dr:
      notes.add BTANote(goal: "(disjunction)", verdict: bvPruned,
        reason: "both branches statically impossible")
      return true
    if dl:
      bound = bR
      notes.add BTANote(goal: "(disjunction)", verdict: bvDischarged,
        reason: "left branch pruned; right survives")
      return false
    if dr:
      bound = bL
      notes.add BTANote(goal: "(disjunction)", verdict: bvDischarged,
        reason: "right branch pruned; left survives")
      return false
    let freshL = freshPHs(rg.leftG)
    let freshR = freshPHs(rg.rightG)
    if branchNotesAll(notes, n0, n1, bvDischarged) and
       branchNotesAll(notes, n1, notes.len, bvDischarged) and
       newBindings(bL, bound, freshL).len == 0 and
       newBindings(bR, bound, freshR).len == 0:
      notes.add BTANote(goal: "(disjunction)", verdict: bvDischarged,
        reason: "statically true on all branches, no observable bindings")
      return false
    notes.add BTANote(goal: "(disjunction)", verdict: bvFallback,
      reason: "disjunction kept in residual (branches survive with " &
              "branch-local bindings)")
    false
  of rgFresh:
    let ph = "__var_" & rg.varName
    var had = false
    var saved: RTerm = nil
    if ph in bound:
      had = true; saved = bound[ph]
    bound.del(ph)  # binder starts free (shadow-safe)
    var dynLocal = dyn
    dynLocal.excl(ph)
    let d = btaGoal(rg.body, bound, dynLocal, notes)
    if not d and ph in bound:
      notes.add BTANote(goal: "(fresh " & rg.varName & ")", verdict: bvDischarged,
        reason: "binder solved away at staging; dropped from residual")
    if had: bound[ph] = saved
    else: bound.del(ph)
    d
  of rgCall:
    var sig = ""
    var missing: seq[string]
    for a in rg.args:
      let ad = btaDeref(a, bound)
      if isGroundBT(ad):
        sig &= "s"
      else:
        sig &= "d"
        for p in termDyn(a, bound, dyn):
          if p notin missing: missing.add(p)
        # free placeholders become dynamic params of the specialization
        # (stageGoal's rgCall case: only ground-static args specialize)
        for p in phNames(ad):
          if p notin dyn and p notin bound and p notin missing:
            missing.add(p & " (free→dynamic param)")
    notes.add BTANote(goal: $rg, verdict: bvSpecialize,
      reason: "call signature " & rg.relName & "(" & sig &
              "): s=static ground, d=dynamic",
      missing: missing)
    false
  of rgSetEq, rgBranch:
    notes.add BTANote(goal: $rg, verdict: bvFallback,
      reason: $rg.kind & ": always residualized (conservative — no " &
              "staging-time constraint reasoning)")
    false

# ---------------------------------------------------------------------------
# Entry inference: compute (staticParams, dynamicVars) from modes + known args

proc inferEntry*(rd: RelDef, known: Table[string, RTerm]):
    tuple[staticParams: Table[string, RTerm],
          dynamicVars: HashSet[string]] =
  ## Derive the staging entry annotation. This replaces the hand-drawn
  ## `staticParams["ty"] = natTy(); dynamicVars.incl("__var_tm")` lines.
  ##
  ## Rules (grounded in the mode checker):
  ## - mOut params are dynamic: outputs are computed at runtime, staging
  ##   must never bind them (the #41 soundness condition).
  ## - mIn / mGround params: static iff the caller supplies a ground value
  ##   in `known`; otherwise dynamic (runtime input / unknown).
  ## - A non-ground `known` value is a caller bug: raise, don't silently
  ##   degrade to dynamic.
  if rd.modes.len != rd.params.len:
    raise newException(ValueError, "inferEntry(" & rd.name &
      "): modes/params length mismatch")
  result = (initTable[string, RTerm](), initHashSet[string]())
  for i, p in rd.params:
    let ph = "__var_" & p
    case rd.modes[i]
    of mOut:
      result.dynamicVars.incl(ph)
    of mIn, mGround:
      if p in known:
        if not isGroundBT(known[p]):
          raise newException(ValueError, "inferEntry(" & rd.name &
            "): known arg '" & p & "' is not ground: " & $known[p])
        result.staticParams[p] = known[p]
      else:
        result.dynamicVars.incl(ph)
  for k in known.keys:
    if k notin rd.params:
      raise newException(ValueError, "inferEntry(" & rd.name &
        "): unknown param '" & k & "'")

proc analyzeBoundary*(rd: RelDef, known: Table[string, RTerm]): seq[BTANote] =
  ## Compute the fallback boundary for specializing rd with `known`
  ## static args: per-subgoal verdicts over the inferred entry.
  let (sp, dv) = inferEntry(rd, known)
  var bound = initTable[string, RTerm]()
  for p, t in sp: bound["__var_" & p] = t
  result = @[]
  discard btaGoal(rd.body, bound, dv, result)

proc boundaryReport*(notes: seq[BTANote]): string =
  ## Human-readable rendering of the computed boundary.
  var d, p, f, s = 0
  for n in notes:
    case n.verdict
    of bvDischarged: inc d
    of bvPruned: inc p
    of bvFallback: inc f
    of bvSpecialize: inc s
  result = "Boundary: " & $d & " discharged, " & $p & " pruned, " & $f &
           " fallback, " & $s & " specialized calls\n"
  result &= "Fallback points (static info unavailable at staging):\n"
  for n in notes:
    if n.verdict == bvFallback:
      result &= "  - " & n.goal & "\n    why: " & n.reason
      if n.missing.len > 0:
        result &= " [missing: " & n.missing.join(", ") & "]"
      result &= "\n"
  result &= "Pruned branches:\n"
  for n in notes:
    if n.verdict == bvPruned and n.goal notin ["fail"]:
      result &= "  - " & n.goal & "\n    why: " & n.reason & "\n"

proc stageWithBTA*(relEnv: Table[string, RelDef], relName: string,
                   known: Table[string, RTerm], fuel: int = 8):
    tuple[top: string, specs: Table[string, RelEntry]] =
  ## Specialize relName with `known` static args and zero manual markers:
  ## entry inference -> specializeRelation.
  if relName notin relEnv:
    raise newException(ValueError, "stageWithBTA: unknown relation " & relName)
  let rd = relEnv[relName]
  let (sp, dv) = inferEntry(rd, known)
  var ctx = newSpecCtx(relEnv, fuel)
  let top = specializeRelation(ctx, relName, sp, dv)
  (top, ctx.specs)

# ---------------------------------------------------------------------------
# Tests

when isMainModule:
  import staging/stage_typeo   # typeoData
  import staging/bench_typeo   # testCases, checkUnstaged, checkStaged
  import rel_elab              # natTy, zeroTm, sucTm, ...
  import times

  var failures = 0
  proc check(cond: bool, msg: string) =
    if cond: echo "  PASS: ", msg
    else: echo "  FAIL: ", msg; inc failures

  echo "=== BTA: binding-time analysis (issue #31) ==="
  echo ""

  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[Mode.mIn, Mode.mIn, Mode.mIn], body: typeoData())
  var known = initTable[string, RTerm]()
  known["ty"] = natTy()

  # --- Test 1: inferEntry reproduces the hand-drawn entry ---
  echo "--- inferEntry vs hand-drawn entry ---"
  let (sp, dv) = inferEntry(relEnv["typeo"], known)
  check(sp.len == 1 and "ty" in sp and $sp["ty"] == $natTy(),
        "staticParams == {ty: nat} (was hand-drawn)")
  check(dv == toHashSet(["__var_tm", "__var_ctx"]),
        "dynamicVars == {__var_tm, __var_ctx} (was hand-drawn)")

  # mOut params are dynamic even when "known"
  var relEnv2 = initTable[string, RelDef]()
  relEnv2["r"] = RelDef(name: "r", params: @["a", "b"], modes: @[Mode.mIn, Mode.mOut],
                        body: rgEq(ratom("__var_b"), rint(1)))
  var known2 = initTable[string, RTerm]()
  known2["a"] = rint(1); known2["b"] = rint(2)
  let (sp2, dv2) = inferEntry(relEnv2["r"], known2)
  check("b" notin sp2 and "__var_b" in dv2,
        "mOut param is dynamic even with a supplied value")
  check("a" in sp2 and "__var_a" notin dv2, "mIn + ground value is static")

  # error cases
  var raised = false
  try:
    var bad = initTable[string, RTerm]()
    bad["a"] = ratom("__var_x")  # not ground
    discard inferEntry(relEnv2["r"], bad)
  except ValueError: raised = true
  check(raised, "non-ground known value raises (caller bug, not silent)")
  raised = false
  try:
    var bad = initTable[string, RTerm]()
    bad["zzz"] = rint(1)
    discard inferEntry(relEnv2["r"], bad)
  except ValueError: raised = true
  check(raised, "unknown param name raises")
  echo ""

  # --- Test 2: BTA residual identical to hand-drawn residual ---
  echo "--- stageWithBTA vs hand-drawn specializeRelation ---"
  let tBta0 = cpuTime()
  let (topB, specsB) = stageWithBTA(relEnv, "typeo", known)
  let msBta = (cpuTime() - tBta0) * 1000
  # hand-drawn entry, exactly as bench_typeo.buildSpecialized
  var ctxH = newSpecCtx(relEnv, fuel = 8)
  var spH = initTable[string, RTerm]()
  spH["ty"] = natTy()
  var dvH = initHashSet[string]()
  dvH.incl("__var_tm"); dvH.incl("__var_ctx")
  let tHand0 = cpuTime()
  let topH = specializeRelation(ctxH, "typeo", spH, dvH)
  let msHand = (cpuTime() - tHand0) * 1000
  check(topB == topH, "same top specialization: " & topB)
  var sameBody = specsB.len == ctxH.specs.len
  if sameBody:
    for name, e in specsB:
      if name notin ctxH.specs or $e.body != $ctxH.specs[name].body:
        sameBody = false; break
  check(sameBody, "all " & $specsB.len &
        " specialized bodies syntactically identical to hand-drawn")
  let sizeB = block:
    var n = 0
    for _, e in specsB: n += ($e.body).len
    n
  let sizeH = block:
    var n = 0
    for _, e in ctxH.specs: n += ($e.body).len
    n
  check(sizeB == sizeH, "residual size identical (" & $sizeB & " chars)")
  echo "  staging time: BTA=" & $msBta & "ms hand=" & $msHand &
       "ms (acceptance: BTA < 2x hand)"
  check(msBta < 2 * max(msHand, 0.01), "BTA staging time within 2x of hand-drawn")
  echo ""

  # --- Test 3: differential corpus (staged == unstaged == expected) ---
  echo "--- differential correctness on bench corpus ---"
  let cases = testCases()
  var agree = true
  for c in cases:
    let u = checkUnstaged(c.tm, c.ctxTm, 20)
    let s = checkStaged(topB, specsB, c.tm, c.ctxTm, 20)
    if u != s or u != c.expect:
      agree = false
      echo "  MISMATCH: ", c.name, " unstaged=", u, " staged=", s,
           " expected=", c.expect
  check(agree, "BTA-staged and unstaged agree on all " & $cases.len &
        " corpus terms (expected values sane)")
  echo ""

  # --- Test 4: analyzeBoundary on typeo ---
  echo "--- analyzeBoundary(typeo, ty=nat) ---"
  let notes = analyzeBoundary(relEnv["typeo"], known)
  echo boundaryReport(notes)
  var sawPrunedArr = false
  var sawFallbackTm = false
  var sawFallbackCtx = false
  var nFallback = 0
  var nSpecialize = 0
  for n in notes:
    if n.verdict == bvPruned and "arr" in n.goal: sawPrunedArr = true
    if n.verdict == bvFallback:
      inc nFallback
      if "__var_tm" in n.missing: sawFallbackTm = true
      if "__var_ctx" in n.missing: sawFallbackCtx = true
    if n.verdict == bvSpecialize: inc nSpecialize
  check(sawPrunedArr, "lam branch pruned: (ty == (arr d c)) vs static nat")
  check(sawFallbackTm, "fallback points blame dynamic __var_tm")
  check(sawFallbackCtx, "fallback points blame dynamic __var_ctx")
  check(nFallback > 0 and nSpecialize > 0,
        "non-trivial boundary: " & $nFallback & " fallbacks, " &
        $nSpecialize & " specialized calls")
  echo ""

  # --- Test 5: micro-tests with exact verdicts ---
  echo "--- abstract interpreter micro-tests ---"
  proc analyzeOne(body: RelGoal, knownA: Table[string, RTerm],
                  modesA: seq[Mode], paramsA: seq[string]): seq[BTANote] =
    let rd = RelDef(name: "t", params: paramsA, modes: modesA, body: body)
    analyzeBoundary(rd, knownA)
  let noKnown = initTable[string, RTerm]()
  # (5 == 5): discharged
  var ns = analyzeOne(rgEq(rint(5), rint(5)), noKnown, @[], @[])
  check(ns.len == 1 and ns[0].verdict == bvDischarged, "(5==5) discharged")
  # (5 == 6): pruned
  ns = analyzeOne(rgEq(rint(5), rint(6)), noKnown, @[], @[])
  check(ns.len == 1 and ns[0].verdict == bvPruned, "(5==6) pruned")
  # (n == suc(n)), n free: cyclic -> fallback
  ns = analyzeOne(rgEq(ratom("__var_n"),
                       rpair(ratom("suc"), rpair(ratom("__var_n"), rnil()))),
                  noKnown, @[], @[])
  check(ns.len == 1 and ns[0].verdict == bvFallback, "(n==suc(n)) fallback (cyclic)")
  # dynamic param: (tm == zero) with tm unknown -> fallback missing tm
  ns = analyzeOne(rgEq(ratom("__var_tm"), ratom("zero")), noKnown,
                  @[Mode.mIn], @["tm"])
  check(ns.len == 1 and ns[0].verdict == bvFallback and
        ns[0].missing == @["__var_tm"],
        "(tm==zero), tm dynamic -> fallback missing [__var_tm]")
  # static param: (tm == zero) with tm=zero known -> discharged
  var kStatic = initTable[string, RTerm]()
  kStatic["tm"] = ratom("zero")
  ns = analyzeOne(rgEq(ratom("__var_tm"), ratom("zero")), kStatic,
                  @[Mode.mIn], @["tm"])
  check(ns.len == 1 and ns[0].verdict == bvDischarged,
        "(tm==zero), tm=zero static -> discharged")
  # disjunction: ((5==6) v (5==5)) -> discharged, left pruned
  ns = analyzeOne(rgDisj(rgEq(rint(5), rint(6)), rgEq(rint(5), rint(5))),
                  noKnown, @[], @[])
  var hasPruneSummary = false
  var allDischargedOrPrune = true
  for n in ns:
    if n.verdict == bvFallback: allDischargedOrPrune = false
    if n.verdict == bvDischarged and "pruned" in n.reason: hasPruneSummary = true
  check(allDischargedOrPrune and hasPruneSummary,
        "((5==6) v (5==5)): left pruned, disjunction discharged")
  # disequality always residualizes
  ns = analyzeOne(rgNeq(ratom("__var_tm"), rint(5)), noKnown, @[Mode.mIn], @["tm"])
  check(ns.len == 1 and ns[0].verdict == bvFallback,
        "=/= residualizes (conservative)")
  echo ""

  if failures == 0:
    echo "ALL BTA TESTS PASS"
  else:
    echo failures, " FAILURES"
    quit(1)
