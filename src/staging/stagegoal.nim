## stageGoal: staging rules for RelGoal
##
## Symbolically executes a RelGoal with static/dynamic distinction.
## - Static RTerms (ground): unify now, prune impossible branches
## - Dynamic RTerms (with vars): residualize as RelGoal data
##
## This is the relational analog of evalStaged: mix(relation, staticArgs).

import staging/relgoal
import staging/modes
import minikanren
import tables
import strutils

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

proc isGround(t: RTerm): bool =
  ## Check if RTerm is ground (no vars, no dynamic placeholders).
  case t.kind
  of rkVar: false
  of rkAtom:
    # __var_ placeholders represent dynamic variables, not ground values
    not t.name.startsWith("__var_")
  of rkPair: isGround(t.head) and isGround(t.tail)


proc resolveStatic(t: RTerm, env: Table[string, RTerm]): RTerm =
  ## Replace __var_<name> placeholders with static values from env.
  case t.kind
  of rkAtom:
    if t.name.startsWith("__var_"):
      let key = t.name
      if key in env: env[key]
      else: t
    else: t
  of rkPair:
    rpair(resolveStatic(t.head, env), resolveStatic(t.tail, env))
  else: t

proc unifyGround(a, b: RTerm): bool =
  ## Check if two ground terms unify (structural equality).
  if a.kind != b.kind: return false
  case a.kind
  of rkAtom: a.name == b.name
  of rkPair: unifyGround(a.head, b.head) and unifyGround(a.tail, b.tail)
  of rkVar: false  # shouldn't happen for ground, but safe

type
  UnifyResult = enum
    urYes,      # definitely unifies
    urNo,       # definitely doesn't unify (prune!)
    urMaybe     # can't decide statically (residualize)

proc unifyHead(a, b: RTerm): UnifyResult =
  ## Partial unification: prune when head constructors differ,
  ## even if subterms are dynamic. Returns Maybe when undecidable.
  ##
  ## This improves on unifyGround by handling partial ground terms:
  ##   suc(__var_n) vs zero → No (heads suc vs zero differ)
  ##   suc(__var_n) vs add(__var_a, __var_b) → No
  ##   suc(__var_n) vs suc(__var_m) → Maybe (heads match, subterms dynamic)
  if a.kind == rkVar or b.kind == rkVar:
    return urMaybe  # logic var: can't decide
  if a.kind != b.kind:
    return urNo  # var vs atom/pair, etc.
  case a.kind
  of rkAtom:
    # Atoms: __var_ placeholders are dynamic, others are ground
    let aDyn = a.name.startsWith("__var_")
    let bDyn = b.name.startsWith("__var_")
    if aDyn or bDyn:
      # If both are the same placeholder, they unify; else maybe
      if a.name == b.name: urYes else: urMaybe
    else:
      if a.name == b.name: urYes else: urNo
  of rkPair:
    # Pairs: check heads first (constructor discrimination)
    let h = unifyHead(a.head, b.head)
    if h == urNo: return urNo
    # Heads maybe/yes: need to check tails
    let t = unifyHead(a.tail, b.tail)
    if t == urNo: return urNo
    if h == urYes and t == urYes: urYes else: urMaybe
  of rkVar: urMaybe  # unreachable, but safe

proc stageGoal*(rg: RelGoal, staticEnv: var Table[string, RTerm]): StagedGoal =
  ## Stage a RelGoal given static bindings (mutated with learned bindings).
  ## staticEnv: maps __var_<name> to ground RTerm (static values)
  case rg.kind
  of rgFail:
    StagedGoal(kind: sgFail)
  of rgSucceed:
    StagedGoal(kind: sgDone)
  of rgEq:
    let a = resolveStatic(rg.left, staticEnv)
    let b = resolveStatic(rg.right, staticEnv)
    case unifyHead(a, b)
    of urYes:
      StagedGoal(kind: sgDone)
    of urNo:
      StagedGoal(kind: sgFail)  # statically impossible, prune
    of urMaybe:
      # Try to learn a binding: placeholder == ground → bind it
      if a.kind == rkAtom and a.name.startsWith("__var_") and isGround(b):
        staticEnv[a.name] = b
        StagedGoal(kind: sgDone)  # solved by binding
      elif b.kind == rkAtom and b.name.startsWith("__var_") and isGround(a):
        staticEnv[b.name] = a
        StagedGoal(kind: sgDone)
      else:
        StagedGoal(kind: sgResidual, goal: rg)
  of rgNeq:
    # For prototype: always residualize (conservative)
    StagedGoal(kind: sgResidual, goal: rg)
  of rgConj:
    let sa = stageGoal(rg.leftG, staticEnv)
    if sa.kind == sgFail:
      return StagedGoal(kind: sgFail)
    # TODO: thread bindings from sa into staticEnv for rightG
    # For prototype: stage right with same env
    let sb = stageGoal(rg.rightG, staticEnv)
    if sb.kind == sgFail:
      return StagedGoal(kind: sgFail)
    if sa.kind == sgDone and sb.kind == sgDone:
      return StagedGoal(kind: sgDone)
    # At least one residual: combine
    let ra = if sa.kind == sgResidual: sa.goal else: rgSucceed()
    let rb = if sb.kind == sgResidual: sb.goal else: rgSucceed()
    StagedGoal(kind: sgResidual, goal: rgConj(ra, rb))
  of rgDisj:
    let sa = stageGoal(rg.leftG, staticEnv)
    let sb = stageGoal(rg.rightG, staticEnv)
    if sa.kind == sgFail:
      return sb  # left impossible, take right
    if sb.kind == sgFail:
      return sa  # right impossible, take left
    if sa.kind == sgDone:
      return sa  # left succeeds, prune right (deterministic)
    # Both residual or one done: residualize disjunction
    let ra = if sa.kind == sgResidual: sa.goal else: rgSucceed()
    let rb = if sb.kind == sgResidual: sb.goal else: rgSucceed()
    StagedGoal(kind: sgResidual, goal: rgDisj(ra, rb))
  of rgFresh:
    # Stage the body with the fresh var as dynamic (not in staticEnv).
    # The var remains a placeholder; if the body prunes to Fail, so do we.
    let stagedBody = stageGoal(rg.body, staticEnv)
    case stagedBody.kind
    of sgFail:
      StagedGoal(kind: sgFail)
    of sgDone:
      # Body fully evaluated; fresh var was eliminated
      StagedGoal(kind: sgDone)
    of sgResidual:
      StagedGoal(kind: sgResidual, goal: rgFresh(rg.varName, stagedBody.goal))
  of rgCall:
    # For prototype: residualize (no inlining yet)
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

  # Test: suc(__var_n) vs suc(__var_m) → heads match, subterms dynamic → residual
  let g6 = rgEq(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())),
                rpair(ratom("suc"), rpair(ratom("__var_m"), rnil())))
  var env6 = initTable[string, RTerm]()
  let s6 = stageGoal(g6, env6)
  echo "(suc(n) == suc(m)): ", s6.kind, " (expected sgResidual)"
  if s6.kind == sgResidual: echo "✓ Correctly residualized (can't decide)"
  echo ""
  echo "stageGoal rules work. Next: apply to evalo."
