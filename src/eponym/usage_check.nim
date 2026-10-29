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
  UsageSummary = object
    profile: UsageProfile
    hasErasedUse: bool

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

proc usageThen(left, right: UsageSummary): UsageSummary =
  UsageSummary(profile: usageThen(left.profile, right.profile),
               hasErasedUse: left.hasErasedUse or right.hasErasedUse)

type UsageChoiceExpansion = object
  found: bool
  condition: Term
  strictArgs: seq[Term]
  branches: seq[Term]
  recursiveCounts: seq[int]
  unsupportedChoice: bool

proc flattenApps(t: Term): tuple[head: Term, args: seq[Term]]

type ArgumentUseKind = enum aukRuntime, aukType, aukErased

proc argumentUseKinds(t: Term): seq[ArgumentUseKind] =
  ## For a global or primitive call, recover arguments that are erased at
  ## runtime: universe-domain type arguments and q0 arguments. They do not
  ## consume the enclosing variable's runtime quantity.
  let (head, args) = flattenApps(t)
  if head.isNil or args.len == 0: return
  var ty: Term
  case head.kind
  of tR:
    if not head.refTyp.isNil: ty = head.refTyp.syn
  of tPrim: ty = head.primTy
  of tLam:
    # A direct lambda application has an explicit binder quantity in the
    # term. Its first argument can be classified even without a separate
    # type annotation; arguments to returned functions stay conservative.
    result.add(if head.qty == q0: aukErased else: aukRuntime)
    if args.len > 1:
      for _ in 1 ..< args.len: result.add(aukRuntime)
    return
  else: discard
  if ty.isNil: return
  for arg in args:
    while ty.kind == tLam:
      ty = ty.scope.bdy
    if ty.kind != tPi:
      result.add(aukRuntime)
      continue
    let domain = ty.dom
    result.add(if domain.kind == tType: aukType
               elif ty.qty == q0: aukErased
               else: aukRuntime)
    ty = subst(ty.scope.bdy, 0, arg)

proc termContainsRef(t: Term, refId: int): bool =
  if t.isNil: return false
  case t.kind
  of tR: t.refId == refId
  of tLam, tPi, tSi: termContainsRef(t.dom, refId) or
                     termContainsRef(t.scope.bdy, refId)
  of tApp: termContainsRef(t.fn, refId) or termContainsRef(t.arg, refId)
  of tPair: termContainsRef(t.pFst, refId) or termContainsRef(t.pSnd, refId) or
            termContainsRef(t.pScope.bdy, refId)
  of tFst, tSnd, tAbsurd: termContainsRef(t.sub, refId)
  of tLet: termContainsRef(t.letVal, refId) or
           termContainsRef(t.letTy, refId) or
           termContainsRef(t.letScope.bdy, refId)
  of tPrim: termContainsRef(t.primTy, refId)
  of tV, tC, tType, tMeta, tInt, tNatLit, tNatSing: false

proc containsVarAt(t: Term, target: int, depth: int): bool

proc isQttGroundType(t: Term): bool =
  if t.isNil: return false
  if t.kind == tR:
    if t.qttGroundType: return true
    if t.refIsDefn and not t.refVal.isNil and not t.refVal.syn.isNil:
      return isQttGroundType(t.refVal.syn)
  false

proc containsVarAt(t: Term, target: int, depth: int): bool =
  case t.kind
  of tV: t.idx == target + depth
  of tLam, tPi, tSi: containsVarAt(t.scope.bdy, target, depth + 1)
  of tApp: containsVarAt(t.fn, target, depth) or
           containsVarAt(t.arg, target, depth)
  of tPair: containsVarAt(t.pFst, target, depth) or
             containsVarAt(t.pSnd, target, depth) or
             containsVarAt(t.pScope.bdy, target, depth + 1)
  of tFst, tSnd, tAbsurd: containsVarAt(t.sub, target, depth)
  of tLet: containsVarAt(t.letVal, target, depth) or
           containsVarAt(t.letScope.bdy, target, depth + 1)
  of tPrim, tR, tC, tType, tMeta, tInt, tNatLit, tNatSing: false

proc isGeneratedRecursiveCall(t, elimHead: Term, rule: tuple[
    nargs, nParams: int, cases: Table[int, Term]], ctorArity: int,
    recursiveField: Term): bool =
  ## Recognize the first-order recursive hypothesis emitted for a direct
  ## recursive field of an unindexed data family. Its eliminator arguments
  ## are the same method/motive/parameter variables as the enclosing rule,
  ## followed by the recursive field itself.
  let (callHead, callArgs) = flattenApps(t)
  if callHead.isNil or callHead.kind != tR or
      callHead.refId != elimHead.refId or callArgs.len != rule.nargs:
    return false
  for i in 0 ..< rule.nargs - 1:
    let expected = ctorArity + rule.nargs - 2 - i
    if callArgs[i].kind != tV or callArgs[i].idx != expected:
      return false
  callArgs[^1].kind == tV and callArgs[^1].idx == recursiveField.idx

proc recursiveUsageChoice(branches: seq[UsageProfile],
                          recursiveCounts: seq[int]): UsageProfile =
  ## Compute the possible usage counts over all finite values of a
  ## first-order recursive datatype. Base constructors seed the profile;
  ## each recursive constructor adds its local use count to one profile for
  ## every recursive child. The saturated profile lattice has only three
  ## counts, so this monotone closure reaches a fixed point quickly.
  for i, count in recursiveCounts:
    if count == 0:
      result = usageChoice([result, branches[i]])
  if result == {}: return # no finite base constructor: caller falls back
  while true:
    var next = result
    for i, count in recursiveCounts:
      if count == 0: continue
      var children: UsageProfile = {ucZero}
      for _ in 0 ..< count:
        children = usageThen(children, result)
      next = usageChoice([next, usageThen(branches[i], children)])
    if next == result: return
    result = next

proc flattenApps(t: Term): tuple[head: Term, args: seq[Term]] =
  var revArgs: seq[Term] = @[]
  result.head = t
  while not result.head.isNil and result.head.kind == tApp:
    revArgs.add(result.head.arg)
    result.head = result.head.fn
  if revArgs.len > 0:
    for i in countdown(revArgs.high, 0):
      result.args.add(revArgs[i])

proc keepConservativeElimUse(choice: var UsageChoiceExpansion,
                             args: seq[Term], conditionIndex: int) =
  ## Even when recursive branch behavior is outside our summary, a complete
  ## registered eliminator consumes its scrutinee exactly once. Preserve that
  ## fact and remember the other arguments so any captured use remains
  ## conservative.
  choice.unsupportedChoice = true
  choice.condition = args[conditionIndex]
  for i, arg in args:
    if i != conditionIndex: choice.strictArgs.add(arg)

proc expandBranchEliminator(t: Term): UsageChoiceExpansion =
  ## Expose a checked, exhaustive finite eliminator applied to branch
  ## closures. This sees through transparent definitions (notably
  ## `ifThenElse`) and beta reduction, then uses the registered reduction
  ## rules to recover the alternatives. It specializes complete generated
  ## eliminators whose case templates apply a method to exactly their
  ## constructor fields and verified direct recursive hypotheses. Other
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
      if termContainsRef(head.refVal.syn, head.refId):
        result.unsupportedChoice = true
        return
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
        rule.cases.len == 0 or not redRuleIsComplete(head):
      result.unsupportedChoice = true
      return
    let arities = redRuleCaseArities(head)
    var hasRecursiveCases = false
    for ctorId in rule.cases.keys:
      if redRuleCaseRecursiveFields(head, ctorId).len > 0:
        hasRecursiveCases = true
        if not redRuleCaseRecursiveSupported(head, ctorId):
          result.keepConservativeElimUse(args, rule.nargs - 1)
          return
    if hasRecursiveCases:
      let motiveIndex = rule.nParams
      if motiveIndex >= rule.nargs - 1 or args[motiveIndex].kind != tLam:
        result.keepConservativeElimUse(args, rule.nargs - 1)
        return
    var selectedArgs: seq[int] = @[]
    var branchArgIndexes: seq[int] = @[]
    var recursiveCounts: seq[int] = @[]
    var allMethodArgs: seq[int] = @[]
    for ctorId, branchTemplate in rule.cases:
      let arity = arities.getOrDefault(ctorId, -1)
      let recursiveFields = redRuleCaseRecursiveFields(head, ctorId)
      if arity < 0 or
          (recursiveFields.len > 0 and
           not redRuleCaseRecursiveSupported(head, ctorId)) or
          branchTemplate.isNil:
        result.unsupportedChoice = true
        return
      let (methodHead, fieldArgs) = flattenApps(branchTemplate)
      if methodHead.kind != tV or
          fieldArgs.len != arity + recursiveFields.len:
        result.unsupportedChoice = true
        return
      # Generated case templates apply the corresponding method to each
      # constructor field in declaration order, inserting its recursive
      # hypothesis immediately after a recursive field. Exact variable and
      # recursive-call checks exclude arbitrary computations here.
      var argIndex = 0
      for fieldIndex in 0 ..< arity:
        let fieldArg = fieldArgs[argIndex]
        if fieldArg.kind != tV or fieldArg.idx != arity - 1 - fieldIndex:
          result.unsupportedChoice = true
          return
        inc argIndex
        if fieldIndex in recursiveFields:
          if not isGeneratedRecursiveCall(fieldArgs[argIndex], head, rule,
                                          arity, fieldArg):
            result.unsupportedChoice = true
            return
          inc argIndex
      if argIndex != fieldArgs.len:
        result.unsupportedChoice = true
        return
      let methodSlot = methodHead.idx - arity
      let elimArgIndex = rule.nargs - 2 - methodSlot
      if elimArgIndex < 0 or elimArgIndex >= rule.nargs - 1:
        result.unsupportedChoice = true
        return
      if elimArgIndex in allMethodArgs:
        result.unsupportedChoice = true
        return
      allMethodArgs.add(elimArgIndex)
      if args[elimArgIndex].kind == tLam:
        selectedArgs.add(elimArgIndex)
        branchArgIndexes.add(elimArgIndex)
      elif arity == 0 and recursiveFields.len == 0:
        # A nullary case's ground result is strict: it is evaluated before
        # the data eliminator selects a case. Keep it in strictArgs and use
        # a zero profile for that case's alternative slot.
        branchArgIndexes.add(-1)
      else:
        result.unsupportedChoice = true
        return
      recursiveCounts.add(recursiveFields.len)
    if allMethodArgs.len != rule.cases.len:
      result.unsupportedChoice = true
      return

    if hasRecursiveCases:
      let motiveIndex = rule.nParams
      if not isQttGroundType(args[motiveIndex].scope.bdy):
        # Keep the parts of an indexed recursive elimination whose usage is
        # still exact. The scrutinee is consumed once on every path; method
        # closures may run zero, one, or many times over a recursive value, so
        # captured uses in them remain conservative. This matters for a
        # linear Vec value: rejecting its one scrutinee use merely because the
        # dependent motive is outside the recursive summary would regress
        # valid explicitly-linear programs.
        result.keepConservativeElimUse(args, rule.nargs - 1)
        return
    var hasBaseCase = false
    for count in recursiveCounts:
      if count == 0: hasBaseCase = true
    if not hasBaseCase:
      result.unsupportedChoice = true
      return

    result.found = true
    result.condition = args[rule.nargs - 1]
    for i in 0 ..< rule.nargs - 1:
      if i notin selectedArgs:
        result.strictArgs.add(args[i])
    for elimArgIndex in branchArgIndexes:
      if elimArgIndex < 0:
        result.branches.add(nil)
        continue
      var branch = args[elimArgIndex]
      for i in rule.nargs ..< args.len:
        branch = tmApp(branch, args[i])
      result.branches.add(branch)
    result.recursiveCounts = recursiveCounts
    if hasRecursiveCases:
      for ctorId, caseTm in rule.cases:
        if redRuleCaseRecursiveFields(head, ctorId).len > 0 and
            not termContainsRef(caseTm, head.refId):
          result.unsupportedChoice = true
          result.found = false
          return
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

proc termContainsVarAt(t: Term, target: int, depth: int): bool =
  ## Term-position occurrence of de Bruijn index `target + depth`,
  ## skipping type positions (binder domains, let annotations).
  case t.kind
  of tV: t.idx == target + depth
  of tLam, tPi, tSi: termContainsVarAt(t.scope.bdy, target, depth + 1)
  of tApp: termContainsVarAt(t.fn, target, depth) or
           termContainsVarAt(t.arg, target, depth)
  of tPair: termContainsVarAt(t.pFst, target, depth) or
            termContainsVarAt(t.pSnd, target, depth) or
            termContainsVarAt(t.pScope.bdy, target, depth + 1)
  of tFst, tSnd, tAbsurd: termContainsVarAt(t.sub, target, depth)
  of tLet: termContainsVarAt(t.letVal, target, depth) or
           termContainsVarAt(t.letScope.bdy, target, depth + 1)
  of tPrim, tR, tC, tType, tMeta, tInt, tNatLit, tNatSing: false

proc occursUnderProjAt(t: Term, target: int, depth: int): bool =
  ## True if index `target + depth` occurs under an fst/snd projection
  ## in a *surviving* position of `t`: occurrences inside the value of
  ## a let whose variable is itself unused do not survive (the value
  ## is dropped with the let under substitution counting), so they do
  ## not count as projection uses. Used by the let-factor rule below.
  case t.kind
  of tV: false
  of tLam, tPi, tSi: occursUnderProjAt(t.scope.bdy, target, depth + 1)
  of tApp: occursUnderProjAt(t.fn, target, depth) or
           occursUnderProjAt(t.arg, target, depth)
  of tPair: occursUnderProjAt(t.pFst, target, depth) or
            occursUnderProjAt(t.pSnd, target, depth) or
            occursUnderProjAt(t.pScope.bdy, target, depth + 1)
  of tFst, tSnd: termContainsVarAt(t.sub, target, depth)
  of tAbsurd: occursUnderProjAt(t.sub, target, depth)
  of tLet:
    if termContainsVarAt(t.letScope.bdy, 0, 0):
      occursUnderProjAt(t.letVal, target, depth) or
        occursUnderProjAt(t.letScope.bdy, target, depth + 1)
    else:
      occursUnderProjAt(t.letScope.bdy, target, depth + 1)
  of tPrim, tR, tC, tType, tMeta, tInt, tNatLit, tNatSing: false

proc varUsageProfile*(tm: Term): UsageProfile =
  ## Possible saturated free-use counts for de Bruijn index 0 in term
  ## positions. `tm` is the body of a lambda; index 0 denotes that binder.
  ## Carry erased-argument use through the same walk so inference does not
  ## need to traverse the term a second time.
  proc go(t: Term, depth: int, scaledOnly, skipProj: bool): UsageSummary =
    case t.kind
    of tV:
      result.profile = if t.idx == depth: {ucOnce} else: {ucZero}
    of tLam, tPi, tSi:
      # dom is a type annotation: not a term position, skip it
      result = go(t.scope.bdy, depth + 1, scaledOnly, skipProj)
    of tApp:
      let choice = expandBranchEliminator(t)
      if choice.found:
        var strictUsage = UsageSummary(profile: {ucZero})
        for arg in choice.strictArgs:
          strictUsage = usageThen(strictUsage, go(arg, depth, scaledOnly, skipProj))
        var branchProfiles: seq[UsageProfile] = @[]
        var branchHasErasedUse = false
        for branch in choice.branches:
          if branch.isNil:
            branchProfiles.add({ucZero})
          else:
            let branchUsage = go(branch, depth, scaledOnly, skipProj)
            branchProfiles.add(branchUsage.profile)
            branchHasErasedUse = branchHasErasedUse or
              branchUsage.hasErasedUse
        let caseProfile = recursiveUsageChoice(branchProfiles,
          choice.recursiveCounts)
        if caseProfile == {}:
          result = usageThen(go(t.fn, depth, scaledOnly, skipProj), go(t.arg, depth, scaledOnly, skipProj))
        else:
          let conditionUsage = go(choice.condition, depth, scaledOnly, skipProj)
          result.profile = usageThen(
            usageThen(strictUsage.profile, conditionUsage.profile), caseProfile)
          result.hasErasedUse = strictUsage.hasErasedUse or
            conditionUsage.hasErasedUse or branchHasErasedUse
      elif t.fn.kind == tLam and t.arg.kind == tLam:
        # Generated Nim `if` lowers through the polymorphic `ifThenElse`
        # definition, whose two value arguments are lambda thunks. Applying
        # the selected thunk evaluates exactly one branch; analyze those
        # alternatives as a choice, not as two sequential argument uses.
        let left = go(t.fn.scope.bdy, depth + 1, scaledOnly, skipProj)
        let right = go(t.arg.scope.bdy, depth + 1, scaledOnly, skipProj)
        result.profile = usageChoice([left.profile, right.profile])
        result.hasErasedUse = left.hasErasedUse or right.hasErasedUse
      elif choice.unsupportedChoice:
        if not choice.condition.isNil:
          result = go(choice.condition, depth, scaledOnly, skipProj)
          var capturedByUnknownCase = false
          for arg in choice.strictArgs:
            if containsVarAt(arg, 0, depth):
              capturedByUnknownCase = true
          if capturedByUnknownCase:
            result.profile = usageThen(result.profile,
              {ucZero, ucOnce, ucMany})
        elif containsVarAt(t, 0, depth):
          result.profile = {ucZero, ucOnce, ucMany}
        else:
          result.profile = {ucZero}
      else:
        let useKinds = argumentUseKinds(t)
        if useKinds.len > 0:
          result.profile = {ucZero}
          # The flattened spine's function head and all value arguments
          # contribute; universe-domain arguments are erased type positions.
          let (head, args) = flattenApps(t)
          result = usageThen(result, go(head, depth, scaledOnly, skipProj))
          for i, arg in args:
            if i >= useKinds.len or useKinds[i] == aukRuntime:
              result = usageThen(result, go(arg, depth, scaledOnly, skipProj))
            elif useKinds[i] == aukErased and containsVarAt(arg, 0, depth):
              result.hasErasedUse = true
        else:
          result = usageThen(go(t.fn, depth, scaledOnly, skipProj), go(t.arg, depth, scaledOnly, skipProj))
    of tPair:
      result = usageThen(usageThen(go(t.pFst, depth, scaledOnly, skipProj), go(t.pSnd, depth, scaledOnly, skipProj)),
        go(t.pScope.bdy, depth + 1, scaledOnly, skipProj))
    of tFst, tSnd, tAbsurd:
      # In a projection-skipping factor walk, uses under a projection
      # are not counted here: they are handled by the projection-only
      # rule in the tLet case below.
      if skipProj and t.kind != tAbsurd:
        result.profile = {ucZero}
      else:
        result = go(t.sub, depth, scaledOnly, skipProj)
    of tLet:
      # letTy is a type annotation: skip; val and body are term positions.
      # Issue #484: a let is checked under BOTH counts, and the binder
      # passes only if both are exactly once (their union is {ucOnce}):
      # - Strict count (the old composition): the value evaluates once,
      #   so its uses count unconditionally. This keeps the session
      #   tests (15b/15e) rejecting: two lets each consuming the channel
      #   count twice even when one result is dropped.
      # - Scaled count (the QTT let rule): the value's context is scaled
      #   by the bound variable's use count in the body. This rejects
      #   drop and double use through a single let (29d/29e), which the
      #   strict count alone misses: the value's single use would
      #   otherwise mask the misuse of the bound intermediate.
      # A pure value (profile {ucZero} for the target) is unaffected by
      # either count, and an exactly-once-threaded let makes both counts
      # agree, so threaded clients (29-linear-ok) are unchanged. The
      # bound variable's use count feeding the scaled count is itself
      # a substitution count (scaledOnly walk), with projection-only
      # uses collapsed to one (see below): a pair-valued intermediate
      # used once per component must not multiply the value's uses,
      # even though its strict count is two or more.
      let valSummary = go(t.letVal, depth, scaledOnly, skipProj)
      let bodySummary = go(t.letScope.bdy, depth + 1, scaledOnly, skipProj)
      let strictProfile = usageThen(valSummary.profile,
        bodySummary.profile)
      # Bound-variable factor for the scaled count: two substitution
      # walks over the body. The total walk counts every use; the
      # projection-skipping walk counts only uses not under fst/snd.
      # A pair-valued intermediate used only via projections (the
      # Paxos/typestate pattern: fst for a reusable component, snd
      # once for the channel) counts once: projections split a pair
      # into components, so their total must not multiply the value's
      # uses. KNOWN LIMIT: this treats a pair atomically through lets,
      # so double-projection of the SAME component through a let
      # (e.g. (fst p, fst p) with p a pair holding a linear value)
      # counts once here; the strict count still rejects it when the
      # value itself mentions the binder twice, but a single-use pair
      # literal projected twice through a let is not caught. Tracking
      # that needs per-component paths, which this walk does not have.
      var totalSummary = go(t.letScope.bdy, 0, true, false)
      var nonProjSummary = go(t.letScope.bdy, 0, true, true)
      var letVarProfile: UsageProfile
      if skipProj:
        letVarProfile = nonProjSummary.profile
        if nonProjSummary.hasErasedUse:
          letVarProfile = {ucZero, ucOnce, ucMany}
      else:
        if nonProjSummary.profile == {ucZero}:
          letVarProfile = if containsVarAt(t.letScope.bdy, 0, 0): {ucOnce}
                          else: {ucZero}
        else:
          letVarProfile = totalSummary.profile
        if totalSummary.hasErasedUse:
          # An erased-argument use of the let variable is a discard, not
          # a non-use: the value is handed to a q0 parameter (the
          # checkErasedArg rule, which cannot see through the let
          # alias). Expanding here keeps the discard from masking a
          # second direct use of the same linear value, and keeps a
          # lone erased use from passing as "used once". Pure values
          # are unaffected: scaling a {ucZero} value profile by any
          # count stays {ucZero}.
          letVarProfile = {ucZero, ucOnce, ucMany}
      var scaled: UsageProfile = {}
      for k in letVarProfile:
        for m in valSummary.profile:
          scaled.incl UsageCount(min(2, ord(k) * ord(m)))
      let scaledProfile = usageThen(scaled, bodySummary.profile)
      # Enforcement (a binder check) needs both counts; the let-variable
      # factor walk above is itself a substitution count, so in scaled
      # mode the scaled profile alone is the result. Using the union
      # as the factor would overcount pair-valued intermediates, whose
      # two projections are legitimately two strict uses of one value
      # (the 29-linear-ok bracket: p via snd for close and fst for the
      # receipt is one substitution use, not two).
      if scaledOnly:
        result.profile = scaledProfile
      else:
        result.profile = strictProfile + scaledProfile
      # The let-variable walk's erased flag is about the let variable,
      # not the target: it is already accounted for by the expansion
      # above. Propagating it here would flag the target for an erased
      # use of an unrelated (e.g. pure) let-bound value.
      result.hasErasedUse = valSummary.hasErasedUse or
        bodySummary.hasErasedUse
    of tPrim:
      result.profile = {ucZero}  # annotation only; primOp carries no terms
    of tR, tC, tType, tMeta, tInt, tNatLit, tNatSing:
      result.profile = {ucZero}
  if tm.isNil: return {ucZero}
  let summary = go(tm, 0, false, false)
  result = summary.profile
  if result != {ucZero} and summary.hasErasedUse:
    # Keep inference conservative across nested applications and pairs. The
    # occurrence may be structurally separate from the runtime use, so a
    # local per-application adjustment would miss expressions such as
    # `pair (drop x) x`.
    result = {ucZero, ucOnce, ucMany}

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

proc checkUsage*(tm: Term, allowOpenHoles = false): void =
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
        # An open contextual hole may later use this binder. Hole-tolerant
        # elaboration must preserve that possibility for interactive proof
        # states (including linear and erased Pi binders); strict elaboration
        # rechecks the binder after the hole is filled.
        if allowOpenHoles and hasUnresolvedMetas(t.scope.bdy): return
        let profile = varUsageProfile(t.scope.bdy)
        let n = usageCountSummary(profile)
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
