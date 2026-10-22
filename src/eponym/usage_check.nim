## Usage checker for linear binders — Issue #64
##
## Post-elaboration pass that verifies quantitative usage:
## - q1 (linear) binders must be used exactly once
## - q0 (erased) binders must not be used
## - qOmega (unrestricted) binders are unchecked
##
## Walks the elaborated Term (which carries qty on tPi/tLam from the
## integration) with a stack of (qty, used) flags.

import eponym_init
import preterm  # for Quantity
import elab_prof  # Issue #55: phase timers
import strutils, tables

type
  UsageError* = object of CatchableError
  UsageCount* = enum
    ucZero, ucOnce, ucMany
  UsageProfile* = set[UsageCount]

proc usageThen*(left, right: UsageProfile): UsageProfile =
  ## Sequential composition: every left path is followed by every right path.
  ## Counts saturate at many because QTT distinguishes only 0, 1, and >1.
  for a in left:
    for b in right:
      result.incl UsageCount(min(2, ord(a) + ord(b)))

proc usageChoice*(branches: openArray[UsageProfile]): UsageProfile =
  ## Alternative composition: a runtime path takes one branch.
  for branch in branches:
    result = result + branch

proc satisfiesQuantity*(profile: UsageProfile, qty: Quantity): bool =
  case qty
  of q0: profile == {ucZero}
  of q1: profile == {ucOnce}
  of qOmega: true

proc usageCountSummary*(profile: UsageProfile): int =
  ## Conservative legacy summary used by diagnostics and quantity inference.
  ## A non-singleton profile is summarized as many; it must not infer q1.
  if profile == {ucZero}: 0
  elif profile == {ucOnce}: 1
  else: 2

proc usageProfileDescription*(profile: UsageProfile): string =
  if profile == {ucZero}: "0"
  elif profile == {ucOnce}: "1"
  elif profile == {ucMany}: "2 or more"
  else:
    var counts: seq[string] = @[]
    for count in profile:
      counts.add(if count == ucMany: "2+" else: $ord(count))
    counts.join(" or ")

type UsageChoiceExpansion = object
  found: bool
  condition: Term
  strictArgs: seq[Term]
  branches: seq[Term]

proc flattenApps(t: Term): tuple[head: Term, args: seq[Term]] =
  var revArgs: seq[Term] = @[]
  result.head = t
  while not result.head.isNil and result.head.kind == tApp:
    revArgs.add(result.head.arg)
    result.head = result.head.fn
  if revArgs.len > 0:
    for i in countdown(revArgs.high, 0):
      result.args.add(revArgs[i])

proc expandBranchEliminator(t: Term): UsageChoiceExpansion =
  ## Expose a checked, exhaustive binary eliminator applied to branch
  ## closures. This sees through transparent definitions (notably
  ## `ifThenElse`) and beta reduction, then uses the registered reduction
  ## rules to recover the alternatives. It only specializes complete binary
  ## eliminators with non-recursive constructors whose cases apply one of
  ## the method arguments to exactly its constructor fields. Other
  ## eliminators remain conservatively counted as ordinary applications.
  var (head, args) = flattenApps(t)
  # `ifThenElse` unfolds through four lambda binders before reaching Bool's
  # eliminator. Keep a small bound so recursive user definitions are not
  # normalized repeatedly while this analysis walks applications.
  var fuel = 12
  while fuel > 0:
    dec fuel
    if head.isNil: return
    if head.kind == tR and head.refIsDefn and not head.refVal.isNil and
        head.refVal.whnf.kind != wRed:
      if head.refVal.syn.isNil or head.refVal.syn == head: return
      let expanded = flattenApps(head.refVal.syn)
      head = expanded.head
      args = expanded.args & args
      continue
    if head.kind == tLam and args.len > 0:
      let body = subst(head.scope.bdy, 0, args[0])
      let expanded = flattenApps(body)
      head = expanded.head
      var remaining: seq[Term] = @[]
      if args.len > 1: remaining = args[1 .. ^1]
      args = expanded.args & remaining
      continue
    if head.kind != tR or head.refVal.isNil or
        head.refVal.whnf.kind != wRed:
      return

    let rule = redRuleInfo(head)
    if rule.nargs < 2 or args.len < rule.nargs or
        rule.cases.len != 2 or not redRuleIsComplete(head):
      return
    let arities = redRuleCaseArities(head)
    var selectedArgs: seq[int] = @[]
    var branchArgIndexes: seq[int] = @[]
    for ctorId, branchTemplate in rule.cases:
      let arity = arities.getOrDefault(ctorId, -1)
      if arity < 0 or redRuleCaseIsRecursive(head, ctorId) or
          branchTemplate.isNil:
        return
      let (methodHead, fieldArgs) = flattenApps(branchTemplate)
      if methodHead.kind != tV or fieldArgs.len != arity:
        return
      # Generated case templates apply the corresponding method to the
      # constructor's fields in declaration order. Requiring those exact
      # bound variables excludes recursive hypotheses and arbitrary
      # computations from the specialization.
      for i, fieldArg in fieldArgs:
        if fieldArg.kind != tV or fieldArg.idx != arity - 1 - i:
          return
      let methodSlot = methodHead.idx - arity
      let elimArgIndex = rule.nargs - 2 - methodSlot
      if elimArgIndex < 0 or elimArgIndex >= rule.nargs - 1 or
          args[elimArgIndex].kind != tLam:
        return
      if elimArgIndex notin selectedArgs:
        selectedArgs.add(elimArgIndex)
      branchArgIndexes.add(elimArgIndex)
    if selectedArgs.len != 2: return

    result.found = true
    result.condition = args[rule.nargs - 1]
    for i in 0 ..< rule.nargs - 1:
      if i notin selectedArgs:
        result.strictArgs.add(args[i])
    for elimArgIndex in branchArgIndexes:
      var branch = args[elimArgIndex]
      for i in rule.nargs ..< args.len:
        branch = tmApp(branch, args[i])
      result.branches.add(branch)
    return

# --- in-judgment quantity enforcement (Issue #66) ---------------------------
#
# The post-pass above runs after a whole declaration elaborates. For
# quantity-aware *typing judgments*, the elaborator also enforces binder
# quantities at each lambda, while the body is being checked. These helpers
# support that: countVarUses counts free occurrences of de Bruijn index 0
# (the innermost binder) in *term positions* of a body. Binder domains and
# other type annotations are not descended into: in QTT, types are checked
# with the all-0 context, so a type-level mention does not consume a
# linear variable and does not violate erasure. (The post-pass above walks
# domains too, with a known off-by-one: it attributes domain occurrences to
# the innermost binder. The in-judgment check uses correct depth tracking;
# the post-pass stays as a backstop.)

proc varUsageProfile*(tm: Term): UsageProfile =
  ## Possible saturated free-use counts for de Bruijn index 0 in term
  ## positions. `tm` is the body of a lambda; index 0 denotes that binder.
  proc go(t: Term, depth: int): UsageProfile =
    case t.kind
    of tV:
      if t.idx == depth: {ucOnce} else: {ucZero}
    of tLam, tPi, tSi:
      # dom is a type annotation: not a term position, skip it
      go(t.scope.bdy, depth + 1)
    of tApp:
      let choice = expandBranchEliminator(t)
      if choice.found:
        var safeToSplit = true
        for arg in choice.strictArgs:
          if go(arg, depth) != {ucZero}:
            safeToSplit = false
            break
        if safeToSplit:
          var branchProfiles: seq[UsageProfile] = @[]
          for branch in choice.branches:
            branchProfiles.add(go(branch, depth))
          usageThen(go(choice.condition, depth), usageChoice(branchProfiles))
        else:
          usageThen(go(t.fn, depth), go(t.arg, depth))
      else:
        usageThen(go(t.fn, depth), go(t.arg, depth))
    of tPair:
      usageThen(usageThen(go(t.pFst, depth), go(t.pSnd, depth)),
        go(t.pScope.bdy, depth + 1))
    of tFst, tSnd, tAbsurd:
      go(t.sub, depth)
    of tLet:
      # letTy is a type annotation: skip; val and body are term positions
      usageThen(go(t.letVal, depth), go(t.letScope.bdy, depth + 1))
    of tPrim:
      {ucZero}  # primTy is a type annotation; primOp carries no terms
    of tR, tC, tType, tMeta, tInt, tNatLit, tNatSing:
      {ucZero}
  if tm.isNil: {ucZero} else: go(tm, 0)

proc countVarUses*(tm: Term): int =
  ## Exact syntactic count retained for existing callers and diagnostics.
  proc go(t: Term, depth: int): int =
    case t.kind
    of tV:
      if t.idx == depth: 1 else: 0
    of tLam, tPi, tSi:
      go(t.scope.bdy, depth + 1)
    of tApp:
      go(t.fn, depth) + go(t.arg, depth)
    of tPair:
      go(t.pFst, depth) + go(t.pSnd, depth) + go(t.pScope.bdy, depth + 1)
    of tFst, tSnd, tAbsurd:
      go(t.sub, depth)
    of tLet:
      go(t.letVal, depth) + go(t.letScope.bdy, depth + 1)
    of tPrim:
      0
    of tR, tC, tType, tMeta, tInt, tNatLit, tNatSing:
      0
  if tm.isNil: 0 else: go(tm, 0)

proc hasUnresolvedMetas*(tm: Term): bool =
  ## True if `tm` mentions a tMeta anywhere (caller should have zonked first;
  ## a remaining meta means its solution isn't known yet).
  proc go(t: Term): bool =
    case t.kind
    of tMeta: true
    of tV, tR, tC, tType, tInt, tNatLit, tNatSing: false
    of tLam, tPi, tSi: go(t.dom) or go(t.scope.bdy)
    of tApp: go(t.fn) or go(t.arg)
    of tPair: go(t.pFst) or go(t.pSnd) or go(t.pScope.bdy)
    of tFst, tSnd, tAbsurd: go(t.sub)
    of tLet: go(t.letVal) or go(t.letTy) or go(t.letScope.bdy)
    of tPrim: go(t.primTy)
  go(tm)

proc collectUseLocsWalk(p: PreTerm, binder: PreTerm, stack: var seq[PreTerm],
                       acc: var seq[Loc]) =
  ## Walker for collectBinderUseLocs (Issue #84). Module-level so it can
  ## take the accumulator as a var parameter — a nested proc may not
  ## capture it.
  if p.isNil: return
  case p.kind
  of pkVar:
    var i = stack.high
    while i >= 0 and stack[i].name != p.name: dec i
    if i >= 0 and cast[pointer](stack[i]) == cast[pointer](binder):
      acc.add(p.loc)
  of pkLam:
    # c1 is the binder type annotation: not a term position, skip it
    stack.add(p); collectUseLocsWalk(p.c2, binder, stack, acc)
    discard stack.pop()
  of pkPi, pkSigma:
    # dom is a type annotation: skip; the codomain can carry term uses
    # (mirrors countVarUses, which descends into tPi/tSi scopes)
    stack.add(p); collectUseLocsWalk(p.c2, binder, stack, acc)
    discard stack.pop()
  of pkApp:
    collectUseLocsWalk(p.c1, binder, stack, acc)
    collectUseLocsWalk(p.c2, binder, stack, acc)
  of pkPair:
    collectUseLocsWalk(p.c1, binder, stack, acc)
    collectUseLocsWalk(p.c2, binder, stack, acc)
  of pkFst, pkSnd, pkProj:
    collectUseLocsWalk(p.c1, binder, stack, acc)
  of pkLet:
    collectUseLocsWalk(p.c2, binder, stack, acc)  # value: binder not in scope
    stack.add(p); collectUseLocsWalk(p.c3, binder, stack, acc)
    discard stack.pop()
  of pkAnn:
    collectUseLocsWalk(p.c1, binder, stack, acc)  # c2 is the type: skip
  of pkHole, pkDiscard, pkInt, pkBy, pkUniv, pkUnivN, pkUnitTy, pkUnitV, pkEmptyTy:
    discard

proc collectBinderUseLocs*(body: PreTerm, binder: PreTerm): seq[Loc] =
  ## Source locations where the variable bound by `binder` (a pkLam node)
  ## occurs in *term positions* of the surface `body` (Issue #84). Mirrors
  ## countVarUses: binder domains and type annotations are not term
  ## positions (in QTT, types are checked in the all-0 context), so they
  ## are not descended into. Shadowing is handled by binder-node identity:
  ## an occurrence resolves to the innermost binder node carrying its name,
  ## and only counts when that node is `binder` itself.
  result = @[]
  var stack: seq[PreTerm] = @[binder]  # the binder scopes over `body`
  collectUseLocsWalk(body, binder, stack, result)

proc checkUsage*(tm: Term): void =
  profilePhase(epUsage):
      ## Verify linear/erased usage in the elaborated term.
      ## Raises UsageError on violation.
      ##
      ## Post-elaboration backstop (Issue #64). The primary enforcement is
      ## in-judgment (elab.enforceBinderQty, Issue #66), which runs at each
      ## lambda during elaboration. This pass re-verifies every binder in the
      ## final term with the *same* term-position counting (countVarUses), so
      ## the two can never disagree. In particular, occurrences inside binder
      ## domains (type positions) are not uses: in QTT, types are checked in
      ## the all-0 context.
      proc verifyBinder(t: Term) =
        if t.qty == qOmega: return
        let profile = varUsageProfile(t.scope.bdy)
        let n = countVarUses(t.scope.bdy)
        case t.qty
        of q1:
          if profile == {ucZero}:
            raise newException(UsageError,
              "linear variable '" & t.scope.adv &
              "' not used (expected exactly once): a linear binder must be " &
              "used exactly once in the body")
          elif profile == {ucMany}:
            raise newException(UsageError,
              "linear variable '" & t.scope.adv & "' used " & $n &
              " times (expected exactly once): use the variable exactly " &
              "once in the body")
          elif not satisfiesQuantity(profile, q1):
            raise newException(UsageError,
              "linear variable '" & t.scope.adv & "' used " &
              usageProfileDescription(profile) &
              " time(s) (expected exactly once on every runtime path)")
        of q0:
          if not satisfiesQuantity(profile, q0):
            raise newException(UsageError,
              "erased variable '" & t.scope.adv &
              "' used in term position: erased (quantity-0) variables may " &
              "only be used in types")
        of qOmega: discard

      proc go(t: Term) =
        case t.kind
        of tV, tR, tC, tType, tMeta, tInt, tNatLit, tNatSing:
          discard # no binders
        of tLam:
          verifyBinder(t)
          go(t.dom)         # domains may nest binders; uses inside them are
          go(t.scope.bdy)   # type positions, not counted against this binder
        of tPi:
          # Pi binders are not usage-verified (Issue #88). A Pi type declares
          # the contract — linearity is enforced at the corresponding lambda
          # (enforceBinderQty, #66, lambdas only by design) and at
          # application sites (quantity-scaled argument contexts). The
          # codomain need not mention the binder: `Pi (1 x : A). B` is a
          # well-formed type. Verifying Pi binders here made Pi-types-as-terms
          # ill-formed depending on where they were written (a return-type
          # annotation passed, the same Pi computed in a body failed), which
          # blocks the Usage-indexed pattern (#88), whose computing function
          # builds Pi types with literal quantities as ordinary terms.
          # (tSi was already exempt for the same reason.)
          go(t.dom)
          go(t.scope.bdy)
        of tSi:
          # Sigma binders: not linear-checked (they're types, not values)
          go(t.dom)
          go(t.scope.bdy)
        of tApp:
          go(t.fn)
          go(t.arg)
        of tPair:
          go(t.pFst)
          go(t.pSnd)
          go(t.pScope.bdy)
        of tFst, tSnd, tAbsurd:
          go(t.sub)
        of tLet:
          go(t.letVal)
          go(t.letTy)
          go(t.letScope.bdy)
        of tPrim:
          go(t.primTy)

      go(tm)

when isMainModule:
  echo "usage checker module loaded"
