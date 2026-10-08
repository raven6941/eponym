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
  StagedGoalKind = enum
    sgDone,       # fully evaluated at staging time (success)
    sgFail,       # statically impossible (pruned)
    sgResidual    # residual RelGoal for runtime

  StagedGoal = ref object
    case kind: StagedGoalKind
    of sgDone: discard
    of sgFail: discard
    of sgResidual: goal: RelGoal

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

proc stageGoal(rg: RelGoal, staticEnv: Table[string, RTerm]): StagedGoal =
  ## Stage a RelGoal given static bindings.
  ## staticEnv: maps __var_<name> to ground RTerm (static values)
  case rg.kind
  of rgFail:
    StagedGoal(kind: sgFail)
  of rgSucceed:
    StagedGoal(kind: sgDone)
  of rgEq:
    let a = resolveStatic(rg.left, staticEnv)
    let b = resolveStatic(rg.right, staticEnv)
    if isGround(a) and isGround(b):
      # Both static: unify now
      if unifyGround(a, b):
        StagedGoal(kind: sgDone)
      else:
        StagedGoal(kind: sgFail)  # statically impossible
    else:
      # Dynamic involved: residualize
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
    # For prototype: substitute a fresh placeholder and stage body
    # Full version: eliminate if var only used statically
    StagedGoal(kind: sgResidual, goal: rg)
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
  let s1 = stageGoal(g1, initTable[string, RTerm]())
  echo "(5 == 5): ", s1.kind, " (expected sgDone)"
  if s1.kind == sgDone: echo "✓"
  echo ""

  # Test: (5 == 6) should be Fail (pruned)
  let g2 = rgEq(rint(5), rint(6))
  let s2 = stageGoal(g2, initTable[string, RTerm]())
  echo "(5 == 6): ", s2.kind, " (expected sgFail)"
  if s2.kind == sgFail: echo "✓ Statically pruned"
  echo ""

  # Test: (x == 5) with x dynamic should residualize
  let g3 = rgEq(ratom("__var_x"), rint(5))
  let s3 = stageGoal(g3, initTable[string, RTerm]())
  echo "(x == 5) with x dynamic: ", s3.kind, " (expected sgResidual)"
  if s3.kind == sgResidual: echo "✓ Residualized"
  echo ""

  # Test: disjunction pruning
  let g4 = rgDisj(rgEq(rint(5), rint(6)), rgEq(rint(5), rint(5)))
  let s4 = stageGoal(g4, initTable[string, RTerm]())
  echo "((5==6) ∨ (5==5)): ", s4.kind, " (expected sgDone, left pruned)"
  if s4.kind == sgDone: echo "✓ Branch pruned at staging time"
  echo ""
  echo "stageGoal rules work. Next: apply to evalo."
