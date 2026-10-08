## stageGoal: staging rules for RelGoal
##
## Symbolically executes a RelGoal with static/dynamic distinction.
## - Static RTerms (ground): unify now, prune impossible branches
## - Dynamic RTerms (with __var_ placeholders): unify at staging time
##   when possible (binding propagation, incl. nested), else residualize
##
## This is the relational analog of evalStaged: mix(relation, staticArgs).

import staging/relgoal
import staging/modes
import minikanren
import tables
import strutils
import sequtils
import sets

type
  StagedGoalKind* = enum
    sgDone,       # fully evaluated at staging time (success)
    sgFail,       # statically impossible (pruned)
    sgResidual    # residual RelGoal for runtime

  StagedGoal* = ref object
    case kind*: StagedGoalKind
    of sgDone: discard
    of sgFail: discard
    of sgResidual: goal*: RelGoal

type
  UnifyResult = enum
    urYes,      # definitely unifies (bindings recorded in env)
    urNo,       # definitely doesn't unify (prune!)
    urMaybe     # can't decide statically (residualize)

proc isPlaceholder(t: RTerm): bool =
  ## __var_<name> atoms stand for dynamic (runtime) variables.
  t.kind == rkAtom and t.name.startsWith("__var_")

proc deref(t: RTerm, env: Table[string, RTerm]): RTerm =
  ## Chase __var_ bindings in env. Env is acyclic (occurs-check on
  ## bind), so this terminates.
  case t.kind
  of rkAtom:
    if t.name.startsWith("__var_") and t.name in env:
      deref(env[t.name], env)
    else:
      t
  of rkPair:
    rpair(deref(t.head, env), deref(t.tail, env))
  of rkVar:
    t

proc occursIn(name: string, t: RTerm, env: Table[string, RTerm]): bool =
  ## Occurs check: does placeholder `name` occur in deref'd t?
  let td = deref(t, env)
  case td.kind
  of rkAtom: td.name == name
  of rkPair: occursIn(name, td.head, env) or occursIn(name, td.tail, env)
  of rkVar: false

proc unifyStage(a, b: RTerm, env: var Table[string, RTerm],
               dynamicVars: HashSet[string]): UnifyResult =
  ## Staging-time unification with binding propagation.
  ##
  ## - Unbound placeholder vs t: bind (unless occurs-check fails or
  ##   placeholder is in dynamicVars) → Yes.
  ##   This generalizes the old placeholder-vs-ground special case:
  ##   suc(__var_n) vs suc(zero) now learns n=zero through the
  ##   constructors; __var_v vs suc(__var_vn) learns v=suc(vn) UNLESS
  ##   v is in dynamicVars (mOut), in which case it residualizes.
  ## - Head-constructor mismatch, even under dynamic subterms → No (prune).
  ## - Cyclic equation (n vs suc(n)) → Maybe (residualize).
  ##
  ## Bindings are recorded in env; applyEnv substitutes them into
  ## residual goals, which is what makes dropping solved equations sound.
  ##
  ## dynamicVars: placeholders that must NOT be bound at staging time
  ## (e.g., mOut variables). Equations involving them residualize.
  let a2 = deref(a, env)
  let b2 = deref(b, env)
  if a2.kind == rkVar or b2.kind == rkVar:
    return urMaybe  # engine logic var: can't decide at staging time
  if isPlaceholder(a2):
    if a2.name in dynamicVars:
      return urMaybe  # mOut var: residualize, don't bind
    if isPlaceholder(b2) and a2.name == b2.name:
      return urYes
    if occursIn(a2.name, b2, env):
      return urMaybe
    env[a2.name] = b2
    return urYes
  if isPlaceholder(b2):
    if b2.name in dynamicVars:
      return urMaybe  # mOut var: residualize, don't bind
    if occursIn(b2.name, a2, env):
      return urMaybe
    env[b2.name] = a2
    return urYes
  if a2.kind != b2.kind:
    return urNo
  case a2.kind
  of rkAtom:
    # Ground atoms here (placeholders handled above)
    if a2.name == b2.name: urYes else: urNo
  of rkPair:
    let h = unifyStage(a2.head, b2.head, env, dynamicVars)
    if h == urNo: return urNo
    let t = unifyStage(a2.tail, b2.tail, env, dynamicVars)
    if t == urNo: return urNo
    if h == urYes and t == urYes: urYes else: urMaybe
  of rkVar:
    urMaybe  # unreachable (handled above), but safe

proc applyEnv(rg: RelGoal, env: Table[string, RTerm]): RelGoal =
  ## Substitute staging-time bindings into a residual goal.
  ## Partial evaluation proper: the residual carries the learned values,
  ## e.g. a recursive call's static arg is specialized in the residual.
  ## Note: assumes no shadowing of __var_ names by nested rgFresh.
  result = rg
  for name, val in env:
    result = substAtom(result, ratom(name), deref(val, env))

proc finishResidual(s: StagedGoal, env: Table[string, RTerm]): StagedGoal =
  ## Apply the final env to a residual built under env.
  if s.kind == sgResidual:
    StagedGoal(kind: sgResidual, goal: applyEnv(s.goal, env))
  else:
    s

proc termMentions(t: RTerm, name: string): bool =
  case t.kind
  of rkAtom: t.name == name
  of rkPair: termMentions(t.head, name) or termMentions(t.tail, name)
  of rkVar: false

proc mentionsVar(rg: RelGoal, varName: string): bool =
  ## Does placeholder __var_<varName> occur free in rg?
  let ph = "__var_" & varName
  case rg.kind
  of rgFail, rgSucceed: false
  of rgEq, rgNeq: termMentions(rg.left, ph) or termMentions(rg.right, ph)
  of rgConj, rgDisj:
    mentionsVar(rg.leftG, varName) or mentionsVar(rg.rightG, varName)
  of rgFresh:
    if rg.varName == varName: false  # shadowed by inner binder
    else: mentionsVar(rg.body, varName)
  of rgCall: rg.args.anyIt(termMentions(it, ph))
  of rgSetEq:
    rg.cells.anyIt(termMentions(it, ph)) or
      rg.values.anyIt(termMentions(it, ph))
  of rgBranch: rg.vars.anyIt(termMentions(it, ph))

proc stageGoal*(rg: RelGoal, staticEnv: var Table[string, RTerm],
               dynamicVars: HashSet[string] = initHashSet[string](),
               relEnv: Table[string, RelDef] = initTable[string, RelDef](),
               fuel: int = 0): StagedGoal =
  ## Stage a RelGoal given static bindings (mutated with learned bindings).
  ## staticEnv: maps __var_<name> to ground RTerm (static values)
  ## dynamicVars: placeholders that must NOT be bound (e.g., mOut vars)
  ## relEnv: relation definitions for call inlining (issue #20)
  ## fuel: inlining budget; 0 means no inlining (residualize calls)
  case rg.kind
  of rgFail:
    StagedGoal(kind: sgFail)
  of rgSucceed:
    StagedGoal(kind: sgDone)
  of rgEq:
    case unifyStage(rg.left, rg.right, staticEnv, dynamicVars)
    of urYes:
      StagedGoal(kind: sgDone)  # solved at staging time (bindings in env)
    of urNo:
      StagedGoal(kind: sgFail)  # statically impossible, prune
    of urMaybe:
      StagedGoal(kind: sgResidual, goal: rg)
  of rgNeq:
    # For prototype: always residualize (conservative)
    StagedGoal(kind: sgResidual, goal: rg)
  of rgConj:
    let sa = stageGoal(rg.leftG, staticEnv, dynamicVars, relEnv, fuel)
    if sa.kind == sgFail:
      return StagedGoal(kind: sgFail)
    # Bindings learned staging left are in staticEnv for right (conjunction)
    let sb = stageGoal(rg.rightG, staticEnv, dynamicVars, relEnv, fuel)
    if sb.kind == sgFail:
      return StagedGoal(kind: sgFail)
    if sa.kind == sgDone and sb.kind == sgDone:
      return StagedGoal(kind: sgDone)
    # At least one residual: combine, substituting learned bindings
    let ra = if sa.kind == sgResidual: sa.goal else: rgSucceed()
    let rb = if sb.kind == sgResidual: sb.goal else: rgSucceed()
    StagedGoal(kind: sgResidual, goal: applyEnv(rgConj(ra, rb), staticEnv))
  of rgDisj:
    # Branch-local envs: a binding learned in one disjunct does not hold
    # in the other. (A shared env wrongly pruned satisfiable branches,
    # e.g. (x==5 ∧ f(x)) ∨ (x==6): right must not see x=5 from the left.)
    var envL = staticEnv
    var envR = staticEnv
    let sa = stageGoal(rg.leftG, envL, dynamicVars, relEnv, fuel)
    let sb = stageGoal(rg.rightG, envR, dynamicVars, relEnv, fuel)
    if sa.kind == sgFail:
      staticEnv = envR
      return finishResidual(sb, envR)  # left impossible, take right
    if sb.kind == sgFail:
      staticEnv = envL
      return finishResidual(sa, envL)  # right impossible, take left
    if sa.kind == sgDone:
      staticEnv = envL
      return sa  # true ∨ P ≡ true; left's bindings hold
    if sb.kind == sgDone:
      staticEnv = envR
      return sb  # P ∨ true ≡ true
    # Note: Done-shortcircuit commits to one branch (deterministic-mode
    # staging). Answer-complete search staging would keep both branches;
    # see the "stage the Stream?" open question in the design doc.
    # Both residual: branch bindings stay local, outer env unchanged
    let ra = applyEnv(sa.goal, envL)
    let rb = applyEnv(sb.goal, envR)
    StagedGoal(kind: sgResidual, goal: rgDisj(ra, rb))
  of rgFresh:
    # Stage the body with the fresh var as dynamic (not in staticEnv).
    # The var remains a placeholder; if the body prunes to Fail, so do we.
    let stagedBody = stageGoal(rg.body, staticEnv, dynamicVars, relEnv, fuel)
    case stagedBody.kind
    of sgFail:
      StagedGoal(kind: sgFail)
    of sgDone:
      # Body fully evaluated; fresh var was eliminated
      StagedGoal(kind: sgDone)
    of sgResidual:
      let res = applyEnv(stagedBody.goal, staticEnv)
      if mentionsVar(res, rg.varName):
        StagedGoal(kind: sgResidual, goal: rgFresh(rg.varName, res))
      else:
        # Binder vacuous after substitution (var solved away): drop it
        StagedGoal(kind: sgResidual, goal: res)
  of rgCall:
    # Inline relation calls when fuel remains (issue #20).
    # Looks up the RelDef, substitutes args for params, stages the body
    # with fuel-1. Residualizes when fuel is exhausted or rel not found.
    if fuel > 0 and rg.relName in relEnv:
      let rd = relEnv[rg.relName]
      if rd.params.len == rg.args.len:
        var inlined = rd.body
        for i, param in rd.params:
          let placeholder = ratom("__var_" & param)
          inlined = substAtom(inlined, placeholder, rg.args[i])
        return stageGoal(inlined, staticEnv, dynamicVars, relEnv, fuel - 1)
    # No inlining: residualize
    StagedGoal(kind: sgResidual, goal: rg)
  of rgSetEq, rgBranch:
    StagedGoal(kind: sgResidual, goal: rg)

when isMainModule:
  echo "=== stageGoal: relational staging rules ==="
  echo ""

  # Test: (5 == 5) should evaluate to Done at staging time
  let g1 = rgEq(rint(5), rint(5))
  var env1 = initTable[string, RTerm]()
  let s1 = stageGoal(g1, env1)
  echo "(5 == 5): ", s1.kind, " (expected sgDone)"
  if s1.kind == sgDone: echo "✓"
  echo ""

  # Test: (5 == 6) should be Fail (pruned)
  let g2 = rgEq(rint(5), rint(6))
  var env2 = initTable[string, RTerm]()
  let s2 = stageGoal(g2, env2)
  echo "(5 == 6): ", s2.kind, " (expected sgFail)"
  if s2.kind == sgFail: echo "✓ Statically pruned"
  echo ""

  # Test: (x == 5) with x dynamic should residualize
  let g3 = rgEq(ratom("__var_x"), rint(5))
  var env3 = initTable[string, RTerm]()
  let s3 = stageGoal(g3, env3)
  echo "(x == 5) with x staging var: ", s3.kind, " (expected sgDone, x bound)"
  if s3.kind == sgDone:
    echo "✓ Bound x=5 at staging time"
  echo ""

  # Test: disjunction pruning
  let g4 = rgDisj(rgEq(rint(5), rint(6)), rgEq(rint(5), rint(5)))
  var env4 = initTable[string, RTerm]()
  let s4 = stageGoal(g4, env4)
  echo "((5==6) ∨ (5==5)): ", s4.kind, " (expected sgDone, left pruned)"
  if s4.kind == sgDone: echo "✓ Branch pruned at staging time"
  echo ""

  # Test: head-constructor pruning with dynamic subterms
  # suc(__var_n) vs zero → heads differ → prune, even though n is dynamic
  let g5 = rgEq(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())), ratom("zero"))
  var env5 = initTable[string, RTerm]()
  let s5 = stageGoal(g5, env5)
  echo "(suc(n) == zero) with n dynamic: ", s5.kind, " (expected sgFail)"
  if s5.kind == sgFail: echo "✓ Head-constructor mismatch pruned"
  else: echo "✗ Should have pruned"
  echo ""

  # Test: suc(__var_n) vs suc(__var_m) → heads match, alias n:=m, solved
  let g6 = rgEq(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())),
                rpair(ratom("suc"), rpair(ratom("__var_m"), rnil())))
  var env6 = initTable[string, RTerm]()
  let s6 = stageGoal(g6, env6)
  echo "(suc(n) == suc(m)): ", s6.kind, " (expected sgDone, n aliased to m)"
  if s6.kind == sgDone and env6["__var_n"].name == "__var_m":
    echo "✓ Aliased at staging time"
  else: echo "✗ Expected aliasing"
  echo ""

  # Test: nested binding — suc(n) == suc(zero) learns n=zero through ctors
  let g7 = rgEq(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())),
                rpair(ratom("suc"), rpair(ratom("zero"), rnil())))
  var env7 = initTable[string, RTerm]()
  let s7 = stageGoal(g7, env7)
  echo "(suc(n) == suc(zero)): ", s7.kind, " (expected sgDone, n=zero)"
  if s7.kind == sgDone and env7["__var_n"].name == "zero":
    echo "✓ Nested binding propagated"
  else: echo "✗ Expected n=zero, got: ", (if "__var_n" in env7: $env7["__var_n"] else: "<unbound>")
  echo ""

  # Test: deep prune — add(suc(n), zero) vs add(zero, zero), n dynamic
  let g8 = rgEq(rpair(ratom("add"), rpair(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())), rpair(ratom("zero"), rnil()))),
                rpair(ratom("add"), rpair(ratom("zero"), rpair(ratom("zero"), rnil()))))
  var env8 = initTable[string, RTerm]()
  let s8 = stageGoal(g8, env8)
  echo "(add(suc(n),zero) == add(zero,zero)): ", s8.kind, " (expected sgFail)"
  if s8.kind == sgFail: echo "✓ Deep constructor mismatch pruned"
  else: echo "✗ Should have pruned"
  echo ""

  # Test: occurs check — n == suc(n) is cyclic, must residualize not bind
  let g9 = rgEq(ratom("__var_n"),
                rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())))
  var env9 = initTable[string, RTerm]()
  let s9 = stageGoal(g9, env9)
  echo "(n == suc(n)): ", s9.kind, " (expected sgResidual, occurs check)"
  if s9.kind == sgResidual and "__var_n" notin env9:
    echo "✓ Cyclic equation residualized, no bogus binding"
  else: echo "✗ Occurs check failed"
  echo ""

  # Test: conjunction threads bindings — (n==zero) ∧ (suc(n)==suc(zero))
  let g10 = rgConj(rgEq(ratom("__var_n"), ratom("zero")),
                   rgEq(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())),
                        rpair(ratom("suc"), rpair(ratom("zero"), rnil()))))
  var env10 = initTable[string, RTerm]()
  let s10 = stageGoal(g10, env10)
  echo "((n==zero) ∧ (suc(n)==suc(zero))): ", s10.kind, " (expected sgDone)"
  if s10.kind == sgDone: echo "✓ Bindings threaded through conjunction"
  else: echo "✗ Threading failed"
  echo ""

  # Test: disjunction branch-locality —
  # ((x==5) ∧ f(x)) ∨ ((x==6) ∧ g(x)): right branch must NOT see x=5
  # from the left (old shared-env code wrongly pruned it as x==6 → Fail).
  let g11 = rgDisj(
    rgConj(rgEq(ratom("__var_x"), rint(5)), rgCall("f", @[ratom("__var_x")])),
    rgConj(rgEq(ratom("__var_x"), rint(6)), rgCall("g", @[ratom("__var_x")])))
  var env11 = initTable[string, RTerm]()
  let s11 = stageGoal(g11, env11)
  echo "(((x==5) ∧ f(x)) ∨ ((x==6) ∧ g(x))): ", s11.kind, " (expected sgResidual, both kept)"
  if s11.kind == sgResidual and "6" in $s11.goal and "(g " in $s11.goal:
    echo "✓ Right branch not wrongly pruned: ", s11.goal
  else: echo "✗ Branch leaked bindings: ", (if s11.kind == sgResidual: $s11.goal else: $s11.kind)
  echo ""

  # Test: disjunction with a statically-true branch —
  # (x==5) ∨ (x==6): right is satisfiable on its own → whole disj true
  let g11b = rgDisj(rgEq(ratom("__var_x"), rint(5)), rgEq(ratom("__var_x"), rint(6)))
  var env11b = initTable[string, RTerm]()
  let s11b = stageGoal(g11b, env11b)
  echo "((x==5) ∨ (x==6)): ", s11b.kind, " (expected sgDone, deterministic commit)"
  if s11b.kind == sgDone: echo "✓ True-branch short-circuit"
  else: echo "✗ Expected sgDone"
  echo ""

  # Test: residual substitution — (v==suc(vn)) ∧ f(v): residual shows suc(vn)
  let g12 = rgConj(
    rgEq(ratom("__var_v"), rpair(ratom("suc"), rpair(ratom("__var_vn"), rnil()))),
    rgCall("f", @[ratom("__var_v")]))
  var env12 = initTable[string, RTerm]()
  let s12 = stageGoal(g12, env12)
  echo "((v==suc(vn)) ∧ f(v)): ", s12.kind, " (expected sgResidual with substitution)"
  if s12.kind == sgResidual and "(suc __var_vn)" in $s12.goal:
    echo "✓ Learned binding substituted into residual: ", s12.goal
  else: echo "✗ Substitution missing: ", (if s12.kind == sgResidual: $s12.goal else: $s12.kind)
  echo ""

  # Test: call inlining with fuel (issue #20)
  # Define isZero(x) := (x == zero). Call isZero(suc(zero)) with fuel=1:
  # should inline, then prune (suc(zero) vs zero → Fail).
  var relEnv13 = initTable[string, RelDef]()
  relEnv13["isZero"] = RelDef(name: "isZero", params: @["x"], modes: @[mIn],
    body: rgEq(ratom("__var_x"), ratom("zero")))
  let g13 = rgCall("isZero", @[rpair(ratom("suc"), rpair(ratom("zero"), rnil()))])
  var env13 = initTable[string, RTerm]()
  let s13 = stageGoal(g13, env13,
    dynamicVars = initHashSet[string](),
    relEnv = relEnv13, fuel = 1)
  echo "isZero(suc(zero)) with fuel=1: ", s13.kind, " (expected sgFail, inlined then pruned)"
  if s13.kind == sgFail: echo "✓ Call inlined and pruned"
  else: echo "✗ Expected sgFail, got: ", (if s13.kind == sgResidual: $s13.goal else: $s13.kind)
  echo ""

  # Test: fuel exhaustion residualizes
  let g13b = rgCall("isZero", @[ratom("__var_y")])
  var env13b = initTable[string, RTerm]()
  let s13b = stageGoal(g13b, env13b,
    dynamicVars = initHashSet[string](),
    relEnv = relEnv13, fuel = 0)
  echo "isZero(y) with fuel=0: ", s13b.kind, " (expected sgResidual, no inlining)"
  if s13b.kind == sgResidual: echo "✓ Fuel exhaustion residualizes"
  else: echo "✗ Expected sgResidual"
  echo ""
  echo "stageGoal rules work. Next: apply to evalo."
