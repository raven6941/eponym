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

# --- Memoized specialization (partial deduction, issue #19) ---
#
# Inlining recursive calls with fuel (#20) cannot terminate when the
# recursion is on a *dynamic* argument: the specialized type checker must
# still recurse on subterms. Instead, calls are partially deduced:
# a call whose static signature (which params are bound to ground terms)
# matches an in-progress or completed specialization residualizes as a
# call to the *specialized* relation; a new signature triggers a new
# specialization (fuel bounds how many). This is Lloyd & Shepherdson's
# partial deduction, monovariant per static signature.
#
# Soundness condition: a specialization's dynamic params are added to
# dynamicVars while its body is staged, so staging never binds them —
# a dynamic param can only appear in residual equations. Two calls share
# a specialization iff they agree on the ground values of the static
# params; dynamic params are never observed at staging time.

type
  SpecCtx* = ref object
    relEnv*: Table[string, RelDef]  # original relation definitions
    memo*: Table[string, string]   # static-signature key -> specialized name
                                   # (also the recursion guard: inserted
                                   # before the body is staged)
    specs*: Table[string, RelEntry] # specialized name -> params + staged body
    counter*: int
    fuel*: int                      # budget for *new* specializations

proc newSpecCtx*(relEnv: Table[string, RelDef] = initTable[string, RelDef](),
                 fuel: int = 8): SpecCtx =
  SpecCtx(relEnv: relEnv, memo: initTable[string, string](),
          specs: initTable[string, RelEntry](), counter: 0, fuel: fuel)

proc isGroundStatic(t: RTerm): bool =
  ## True iff t has no placeholders and no engine logic vars —
  ## i.e. it is a fully static value the specializer may observe.
  case t.kind
  of rkVar: false
  of rkAtom: not t.name.startsWith("__var_")
  of rkPair: isGroundStatic(t.head) and isGroundStatic(t.tail)

proc specKey(relName: string, staticOf: seq[RTerm]): string =
  ## Static-signature key: per param, the ground static value or `d`.
  ## nil marks a dynamic param. $ on ground RTerms is canonical.
  result = relName & "("
  for t in staticOf:
    if t.isNil: result &= "d,"
    else: result &= "s:" & $t & ","
  result &= ")"

type
  UnifyResult = enum
    urYes,      # definitely unifies (bindings recorded in env)
    urNo,       # definitely doesn't unify (prune!)
    urMaybe     # can't decide statically (residualize)

# Note (issue #104): nested structural decomposition is controlled by the
# `decomposeNested` parameter on stageGoal/specializeRelation (default
# true), not a global — the compile-time staging macro (stagedTypeoProcs)
# runs stageGoal in the Nim VM, where a global toggle var is unreadable.
# The #104 corpus benchmark passes decomposeNested=false to measure the
# legacy pre-#104 head-only behavior (unifyStageLegacy).

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

proc isGroundNoPh(t: RTerm): bool =
  ## No placeholders and no engine logic vars — the old unifyGround-style
  ## notion used by the legacy top-level binding path.
  case t.kind
  of rkVar: false
  of rkAtom: not t.name.startsWith("__var_")
  of rkPair: isGroundNoPh(t.head) and isGroundNoPh(t.tail)

proc unifyHeadNoBind(a, b: RTerm): UnifyResult =
  ## Head-constructor comparison without binding (pre-#104 unifyHead):
  ## prune when head constructors differ, even if subterms are dynamic.
  ## suc(__var_n) vs zero → No; suc(__var_n) vs suc(__var_m) → Maybe.
  ## Same-placeholder atoms unify; otherwise dynamic atoms give Maybe.
  if a.kind == rkVar or b.kind == rkVar:
    return urMaybe
  if a.kind != b.kind:
    return urNo
  case a.kind
  of rkAtom:
    let aDyn = a.name.startsWith("__var_")
    let bDyn = b.name.startsWith("__var_")
    if aDyn or bDyn:
      if a.name == b.name: urYes else: urMaybe
    else:
      if a.name == b.name: urYes else: urNo
  of rkPair:
    let h = unifyHeadNoBind(a.head, b.head)
    if h == urNo: return urNo
    let t = unifyHeadNoBind(a.tail, b.tail)
    if t == urNo: return urNo
    if h == urYes and t == urYes: urYes else: urMaybe
  of rkVar: urMaybe  # unreachable, but safe

proc unifyStageLegacy(a, b: RTerm, env: var Table[string, RTerm],
                      dynamicVars: HashSet[string]): UnifyResult =
  ## Legacy pre-#104 staging-time unification: head-constructor pruning
  ## via unifyHeadNoBind, then top-level placeholder==ground binding only.
  ## No structural decomposition through constructors, no occurs check —
  ## the behavior the #104 corpus benchmarks against.
  let a2 = deref(a, env)
  let b2 = deref(b, env)
  case unifyHeadNoBind(a2, b2)
  of urNo:
    urNo
  of urYes:
    urYes
  of urMaybe:
    if isPlaceholder(a2) and a2.name notin dynamicVars and isGroundNoPh(b2):
      env[a2.name] = b2
      urYes
    elif isPlaceholder(b2) and b2.name notin dynamicVars and isGroundNoPh(a2):
      env[b2.name] = a2
      urYes
    else:
      urMaybe

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

proc freshPlaceholders(rg: RelGoal): HashSet[string] =
  ## All __var_<name> placeholders bound by rgFresh binders in rg.
  result = initHashSet[string]()
  case rg.kind
  of rgFail, rgSucceed: discard
  of rgEq, rgNeq:
    discard  # binders only occur in goals, not terms
  of rgConj, rgDisj:
    result = result + freshPlaceholders(rg.leftG) + freshPlaceholders(rg.rightG)
  of rgFresh:
    result.incl("__var_" & rg.varName)
    result = result + freshPlaceholders(rg.body)
  of rgCall, rgSetEq, rgBranch:
    discard

proc hasObservableBindings(branchEnv, entryEnv: Table[string, RTerm],
                            branchGoal: RelGoal): bool =
  ## Did staging the branch learn bindings for placeholders that stay
  ## meaningful outside the branch? Bindings for variables the branch
  ## itself introduced (rgFresh binders) are internal; anything else is
  ## an assumption about dynamic input.
  let fresh = freshPlaceholders(branchGoal)
  for k in branchEnv.keys:
    if k notin entryEnv and k notin fresh:
      return true
  false

proc reifyNewBindings(branchEnv, entryEnv: Table[string, RTerm]): RelGoal =
  ## Turn bindings learned in a branch (branchEnv minus entryEnv) into a
  ## residual conjunction of equalities, so a fully-evaluated branch can
  ## be kept as a disjunct without losing its answers.
  result = rgSucceed()
  for k, v in branchEnv:
    if k notin entryEnv:
      result = rgConj(result, rgEq(ratom(k), deref(v, branchEnv)))

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
               ctx: var SpecCtx,
               decomposeNested: bool = true): StagedGoal =
  ## Stage a RelGoal given static bindings (mutated with learned bindings).
  ## staticEnv: maps __var_<name> to ground RTerm (static values)
  ## dynamicVars: placeholders that must NOT be bound (e.g., mOut vars)
  ## ctx: relation definitions + memo tables for call specialization
  ##   (partial deduction, issue #19; subsumes fuel-based inlining #20:
  ##   a fully-static call specializes to Done/Fail, i.e. inlining).
  ##   Defaults to a fresh context (fuel=8, no relations).
  ## decomposeNested (issue #104): when true, rgEq uses the full
  ##   staging-time unifier (structural decomposition through matching
  ##   head constructors, occurs check). When false, the legacy pre-#104
  ##   head-only unifier runs (prune on constructor mismatch, top-level
  ##   placeholder==ground binding only). A parameter rather than a
  ##   global so the compile-time staging macro (stagedTypeoProcs, which
  ##   runs stageGoal in the Nim VM) keeps working.
  case rg.kind
  of rgFail:
    StagedGoal(kind: sgFail)
  of rgSucceed:
    StagedGoal(kind: sgDone)
  of rgEq:
    let ur = if decomposeNested:
               unifyStage(rg.left, rg.right, staticEnv, dynamicVars)
             else:
               unifyStageLegacy(rg.left, rg.right, staticEnv, dynamicVars)
    case ur
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
    let sa = stageGoal(rg.leftG, staticEnv, dynamicVars, ctx, decomposeNested)
    if sa.kind == sgFail:
      return StagedGoal(kind: sgFail)
    # Bindings learned staging left are in staticEnv for right (conjunction)
    let sb = stageGoal(rg.rightG, staticEnv, dynamicVars, ctx, decomposeNested)
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
    let sa = stageGoal(rg.leftG, envL, dynamicVars, ctx, decomposeNested)
    let sb = stageGoal(rg.rightG, envR, dynamicVars, ctx, decomposeNested)
    if sa.kind == sgFail:
      staticEnv = envR
      return finishResidual(sb, envR)  # left impossible, take right
    if sb.kind == sgFail:
      staticEnv = envL
      return finishResidual(sa, envL)  # right impossible, take left
    if sa.kind == sgDone and not hasObservableBindings(envL, staticEnv, rg.leftG):
      staticEnv = envL
      if sb.kind == sgDone:
        return sa  # both unconditionally true
      # Left always succeeds, but committing to it (returning Done) would
      # drop the right branch's *runtime* answers: disj(isZero(y), true)
      # must still yield y=zero (issue #29 differential found this).
      # Keep disj(succeed, right-residual): {empty} ∪ answers(right).
      let rb = finishResidual(sb, envR)
      return StagedGoal(kind: sgResidual, goal: rgDisj(rgSucceed(), rb.goal))
    if sb.kind == sgDone and not hasObservableBindings(envR, staticEnv, rg.rightG):
      staticEnv = envR
      if sa.kind == sgDone:
        return sa  # both unconditionally true
      # Symmetric: disj(true, P) keeps P's runtime answers.
      let ra = finishResidual(sa, envL)
      return StagedGoal(kind: sgResidual, goal: rgDisj(ra.goal, rgSucceed()))
    # A Done branch is NOT a license to commit (true ∨ P ≡ true): its
    # success may have assumed values for placeholders that are dynamic
    # outside this disjunct. Committing then is unsound for dynamic
    # inputs (e.g. it collapsed the staged typeo checker to "tm is zero
    # or suc(zero)"). Instead reify the learned bindings as residual
    # equalities and keep the disjunction, per the design doc ("if one
    # branch is statically impossible, take the other; else residualize
    # the disjunction").
    let ra = if sa.kind == sgDone: reifyNewBindings(envL, staticEnv)
             else: applyEnv(sa.goal, envL)
    let rb = if sb.kind == sgDone: reifyNewBindings(envR, staticEnv)
             else: applyEnv(sb.goal, envR)
    # Branch bindings stay local, outer env unchanged
    StagedGoal(kind: sgResidual, goal: rgDisj(ra, rb))
  of rgFresh:
    # Stage the body with the fresh var as dynamic (not in staticEnv).
    # The var remains a placeholder; if the body prunes to Fail, so do we.
    #
    # Scope discipline (issue #29): the binder's placeholder is
    # staging-local. Any outer binding for the same name is hidden while
    # the body is staged, and the body's binding for it is dropped
    # afterwards — otherwise the inner binding leaks into the shared env
    # and corrupts siblings, e.g. (fresh u. u==zero) ∧ (fresh u. u==suc(zero))
    # wrongly staged to Fail (differential found this: satisfiable goal
    # pruned). Bindings the body learns for *other* placeholders are
    # outer-meaningful and still propagate.
    let ph = "__var_" & rg.varName
    let hadOuter = ph in staticEnv
    let saved: RTerm = if hadOuter: staticEnv[ph] else: nil
    staticEnv.del(ph)
    let stagedBody = stageGoal(rg.body, staticEnv, dynamicVars, ctx, decomposeNested)
    staticEnv.del(ph)  # the inner binding dies with the binder
    if hadOuter: staticEnv[ph] = saved
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
    # Memoized specialization (partial deduction), issue #19.
    # Static signature: per param, the ground static value (nil = dynamic).
    # Memo hit — including recursive calls into an in-progress
    # specialization, since the memo entry is inserted before the body
    # is staged — residualizes as a call to the specialized relation.
    # New signature with fuel remaining: stage the body as a new
    # specialization (dynamic params join dynamicVars, so staging can
    # never bind them — the soundness condition). Fuel exhausted or
    # unknown relation: residualize the original call.
    if rg.relName in ctx.relEnv:
      let rd = ctx.relEnv[rg.relName]
      if rd.params.len == rg.args.len:
        var staticOf = newSeq[RTerm](rd.params.len)
        for i in 0 ..< rd.params.len:
          let t = deref(rg.args[i], staticEnv)
          if isGroundStatic(t): staticOf[i] = t
        let key = specKey(rg.relName, staticOf)
        var rargs = newSeq[RTerm](rg.args.len)
        for i, a in rg.args: rargs[i] = deref(a, staticEnv)
        if key in ctx.memo:
          return StagedGoal(kind: sgResidual, goal: rgCall(ctx.memo[key], rargs))
        if ctx.fuel > 0:
          dec ctx.fuel
          let specName = rg.relName & "_s" & $ctx.counter
          inc ctx.counter
          ctx.memo[key] = specName  # recursion guard: visible while body stages
          var bodyEnv = initTable[string, RTerm]()
          var bodyDyn = dynamicVars
          for i, p in rd.params:
            if not staticOf[i].isNil: bodyEnv["__var_" & p] = staticOf[i]
            else: bodyDyn.incl("__var_" & p)
          let staged = stageGoal(rd.body, bodyEnv, bodyDyn, ctx, decomposeNested)
          case staged.kind
          of sgFail:
            # Call statically impossible under this signature.
            ctx.specs[specName] = RelEntry(params: rd.params, body: rgFail())
            return StagedGoal(kind: sgFail)
          of sgDone:
            ctx.specs[specName] = RelEntry(params: rd.params, body: rgSucceed())
            return StagedGoal(kind: sgDone)
          of sgResidual:
            ctx.specs[specName] =
              RelEntry(params: rd.params, body: applyEnv(staged.goal, bodyEnv))
            return StagedGoal(kind: sgResidual, goal: rgCall(specName, rargs))
        # Fuel exhausted: residualize the original call.
        return StagedGoal(kind: sgResidual, goal: rgCall(rg.relName, rargs))
    # Unknown relation or arity mismatch: residualize unchanged.
    StagedGoal(kind: sgResidual, goal: rg)
  of rgSetEq, rgBranch:
    StagedGoal(kind: sgResidual, goal: rg)

proc specializeRelation*(ctx: var SpecCtx, relName: string,
                         staticParams: Table[string, RTerm] =
                           initTable[string, RTerm](),
                         dynamicVars: HashSet[string] =
                           initHashSet[string](),
                         decomposeNested: bool = true): string =
  ## Top-level partial-deduction driver: specialize relName for the given
  ## static params (param name -> ground static term; all other params
  ## are dynamic). Returns the specialized relation's name; specialized
  ## bodies accumulate in ctx.specs (keyed by name, as RelEntry for toGoal).
  ##
  ## Routes through the rgCall case so all memoization logic lives in one
  ## place: the synthetic top call gets a fresh specialization, and any
  ## recursive calls with the same static signature hit the memo.
  ##
  ## decomposeNested threads into stageGoal (issue #104 ablation).
  let rd = ctx.relEnv[relName]
  var args = newSeq[RTerm](rd.params.len)
  for i, p in rd.params:
    if p in staticParams: args[i] = staticParams[p]
    else: args[i] = ratom("__var_" & p)
  var env = initTable[string, RTerm]()
  let staged = stageGoal(rgCall(relName, args), env, dynamicVars, ctx,
                         decomposeNested)
  if staged.kind == sgResidual and staged.goal.kind == rgCall and
     staged.goal.relName in ctx.specs:
    return staged.goal.relName
  raise newException(ValueError, "specializeRelation(" & relName &
    "): could not specialize (statically impossible or fuel exhausted)")

when isMainModule:
  echo "=== stageGoal: relational staging rules ==="
  echo ""

  # Shared context for the call-free tests (no relations needed).
  var tctx = newSpecCtx()

  # Test: (5 == 5) should evaluate to Done at staging time
  let g1 = rgEq(rint(5), rint(5))
  var env1 = initTable[string, RTerm]()
  let s1 = stageGoal(g1, env1, ctx = tctx)
  echo "(5 == 5): ", s1.kind, " (expected sgDone)"
  if s1.kind == sgDone: echo "✓"
  echo ""

  # Test: (5 == 6) should be Fail (pruned)
  let g2 = rgEq(rint(5), rint(6))
  var env2 = initTable[string, RTerm]()
  let s2 = stageGoal(g2, env2, ctx = tctx)
  echo "(5 == 6): ", s2.kind, " (expected sgFail)"
  if s2.kind == sgFail: echo "✓ Statically pruned"
  echo ""

  # Test: (x == 5) with x dynamic should residualize
  let g3 = rgEq(ratom("__var_x"), rint(5))
  var env3 = initTable[string, RTerm]()
  let s3 = stageGoal(g3, env3, ctx = tctx)
  echo "(x == 5) with x staging var: ", s3.kind, " (expected sgDone, x bound)"
  if s3.kind == sgDone:
    echo "✓ Bound x=5 at staging time"
  echo ""

  # Test: disjunction pruning
  let g4 = rgDisj(rgEq(rint(5), rint(6)), rgEq(rint(5), rint(5)))
  var env4 = initTable[string, RTerm]()
  let s4 = stageGoal(g4, env4, ctx = tctx)
  echo "((5==6) ∨ (5==5)): ", s4.kind, " (expected sgDone, left pruned)"
  if s4.kind == sgDone: echo "✓ Branch pruned at staging time"
  echo ""

  # Test: head-constructor pruning with dynamic subterms
  # suc(__var_n) vs zero → heads differ → prune, even though n is dynamic
  let g5 = rgEq(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())), ratom("zero"))
  var env5 = initTable[string, RTerm]()
  let s5 = stageGoal(g5, env5, ctx = tctx)
  echo "(suc(n) == zero) with n dynamic: ", s5.kind, " (expected sgFail)"
  if s5.kind == sgFail: echo "✓ Head-constructor mismatch pruned"
  else: echo "✗ Should have pruned"
  echo ""

  # Test: suc(__var_n) vs suc(__var_m) → heads match, alias n:=m, solved
  let g6 = rgEq(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())),
                rpair(ratom("suc"), rpair(ratom("__var_m"), rnil())))
  var env6 = initTable[string, RTerm]()
  let s6 = stageGoal(g6, env6, ctx = tctx)
  echo "(suc(n) == suc(m)): ", s6.kind, " (expected sgDone, n aliased to m)"
  if s6.kind == sgDone and env6["__var_n"].name == "__var_m":
    echo "✓ Aliased at staging time"
  else: echo "✗ Expected aliasing"
  echo ""

  # Test: nested binding — suc(n) == suc(zero) learns n=zero through ctors
  let g7 = rgEq(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())),
                rpair(ratom("suc"), rpair(ratom("zero"), rnil())))
  var env7 = initTable[string, RTerm]()
  let s7 = stageGoal(g7, env7, ctx = tctx)
  echo "(suc(n) == suc(zero)): ", s7.kind, " (expected sgDone, n=zero)"
  if s7.kind == sgDone and env7["__var_n"].name == "zero":
    echo "✓ Nested binding propagated"
  else: echo "✗ Expected n=zero, got: ", (if "__var_n" in env7: $env7["__var_n"] else: "<unbound>")
  echo ""

  # Test: deep prune — add(suc(n), zero) vs add(zero, zero), n dynamic
  let g8 = rgEq(rpair(ratom("add"), rpair(rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())), rpair(ratom("zero"), rnil()))),
                rpair(ratom("add"), rpair(ratom("zero"), rpair(ratom("zero"), rnil()))))
  var env8 = initTable[string, RTerm]()
  let s8 = stageGoal(g8, env8, ctx = tctx)
  echo "(add(suc(n),zero) == add(zero,zero)): ", s8.kind, " (expected sgFail)"
  if s8.kind == sgFail: echo "✓ Deep constructor mismatch pruned"
  else: echo "✗ Should have pruned"
  echo ""

  # Test: occurs check — n == suc(n) is cyclic, must residualize not bind
  let g9 = rgEq(ratom("__var_n"),
                rpair(ratom("suc"), rpair(ratom("__var_n"), rnil())))
  var env9 = initTable[string, RTerm]()
  let s9 = stageGoal(g9, env9, ctx = tctx)
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
  let s10 = stageGoal(g10, env10, ctx = tctx)
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
  let s11 = stageGoal(g11, env11, ctx = tctx)
  echo "(((x==5) ∧ f(x)) ∨ ((x==6) ∧ g(x))): ", s11.kind, " (expected sgResidual, both kept)"
  if s11.kind == sgResidual and "6" in $s11.goal and "(g " in $s11.goal:
    echo "✓ Right branch not wrongly pruned: ", s11.goal
  else: echo "✗ Branch leaked bindings: ", (if s11.kind == sgResidual: $s11.goal else: $s11.kind)
  echo ""

  # Test: disjunction with a statically-true branch —
  # (x==5) ∨ (x==6): committing to the left (deterministic cut) would
  # drop the x=6 answer, which is unsound for dynamic x. The Done
  # branch is kept as a disjunct with its learned binding reified.
  let g11b = rgDisj(rgEq(ratom("__var_x"), rint(5)), rgEq(ratom("__var_x"), rint(6)))
  var env11b = initTable[string, RTerm]()
  let s11b = stageGoal(g11b, env11b, ctx = tctx)
  echo "((x==5) ∨ (x==6)): ", s11b.kind, " (expected sgResidual, both answers kept)"
  if s11b.kind == sgResidual and "5" in $s11b.goal and "6" in $s11b.goal:
    echo "✓ No deterministic commit: ", s11b.goal
  else: echo "✗ Expected sgResidual keeping both disjuncts"
  echo ""

  # Test: residual substitution — (v==suc(vn)) ∧ f(v): residual shows suc(vn)
  let g12 = rgConj(
    rgEq(ratom("__var_v"), rpair(ratom("suc"), rpair(ratom("__var_vn"), rnil()))),
    rgCall("f", @[ratom("__var_v")]))
  var env12 = initTable[string, RTerm]()
  let s12 = stageGoal(g12, env12, ctx = tctx)
  echo "((v==suc(vn)) ∧ f(v)): ", s12.kind, " (expected sgResidual with substitution)"
  if s12.kind == sgResidual and "(suc __var_vn)" in $s12.goal:
    echo "✓ Learned binding substituted into residual: ", s12.goal
  else: echo "✗ Substitution missing: ", (if s12.kind == sgResidual: $s12.goal else: $s12.kind)
  echo ""

  # Test: call specialization with fuel (issue #20, now partial deduction)
  # Define isZero(x) := (x == zero). Call isZero(suc(zero)) with fuel=1:
  # should specialize (x static), then prune (suc(zero) vs zero → Fail).
  var relEnv13 = initTable[string, RelDef]()
  relEnv13["isZero"] = RelDef(name: "isZero", params: @["x"], modes: @[mIn],
    body: rgEq(ratom("__var_x"), ratom("zero")))
  let g13 = rgCall("isZero", @[rpair(ratom("suc"), rpair(ratom("zero"), rnil()))])
  var env13 = initTable[string, RTerm]()
  var ctx13 = newSpecCtx(relEnv13, fuel = 1)
  let s13 = stageGoal(g13, env13, initHashSet[string](), ctx13)
  echo "isZero(suc(zero)) with fuel=1: ", s13.kind, " (expected sgFail, specialized then pruned)"
  if s13.kind == sgFail: echo "✓ Call specialized and pruned"
  else: echo "✗ Expected sgFail, got: ", (if s13.kind == sgResidual: $s13.goal else: $s13.kind)
  echo ""

  # Test: fuel exhaustion residualizes
  let g13b = rgCall("isZero", @[ratom("__var_y")])
  var env13b = initTable[string, RTerm]()
  var ctx13b = newSpecCtx(relEnv13, fuel = 0)
  let s13b = stageGoal(g13b, env13b, initHashSet[string](), ctx13b)
  echo "isZero(y) with fuel=0: ", s13b.kind, " (expected sgResidual, no specialization)"
  if s13b.kind == sgResidual: echo "✓ Fuel exhaustion residualizes"
  else: echo "✗ Expected sgResidual"
  echo ""
  echo "stageGoal rules work. Next: apply to evalo."
