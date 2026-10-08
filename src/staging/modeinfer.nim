## Mode inference for RelGoal (issue #27)
##
## modes.nim has the mode *checker* (syntactic, conservative: it rejects the
## real typeo/evalo annotations because `tm == zero` counts as "binding" an
## input). This module does Mercury-style mode *inference*: propagate the
## call-site binding pattern through fresh/==/conj/disj to compute
## per-subgoal input/output modes and verify the declared relation modes.
##
## Design guidance (issue #27, step 1):
## - Mercury (Somogyi et al.): modes map initial to final instantiation
##   states (in = ground>>ground, out = free>>ground); the compiler
##   schedules conjunctions left-to-right so each subgoal's inputs are
##   bound, and requires disjuncts to agree on outputs. We do the same
##   over RelGoal data: conjunction threads a bound set, disjunction takes
##   the intersection (bound on all success paths).
## - Staged miniKanren (Ballantyne/Sanna/Hemann/Byrd/Amin, PLDI 2025):
##   binding-time annotations decide per-argument static vs dynamic, and
##   `generate` specializes per static signature. Our per-subgoal ArgMode
##   (amIn/amOut/amMixed) is the same decision, computed from dataflow
##   instead of annotated by hand.
##
## Deliberate divergence from Mercury: an amOut or amMixed argument in a
## callee-mIn position is NOT an error. Partial deduction (stagegoal's
## memoized specialization, issue #19) handles any binding pattern via a
## per-signature specialization; the inference records it as a note
## ("fully-dynamic specialization") instead of rejecting it. typeo's app
## branch needs this: `typeo(a, d, ctx)` is called with d free.
##
## What the user must still annotate (acceptance criterion 3):
## - Primitive/engine relations called from RelGoal bodies (e.g. addo)
##   need declared modes in InferCtx.primModes — inference cannot see
##   through closures. An unknown callee is a hard error naming the
##   relation.
## - A param declared mOut that is not bound on all success paths is a
##   hard error (fix the body or weaken the mode to mGround).
## - setEq/branch constraints are not modeled (conservative: they bind
##   nothing); naked-single propagation through setEqo is future work.

import staging/relgoal
import staging/modes
import staging/stagegoal
import minikanren
import tables
import sets
import strutils

type
  ArgMode* = enum
    amIn     ## all vars in the arg are bound (static input at this point)
    amOut    ## no vars in the arg are bound (fresh output)
    amMixed  ## partially instantiated: some vars bound, some free

  CallSite* = object
    ## One rgCall encountered during propagation, with per-arg modes.
    relName*: string
    argModes*: seq[ArgMode]

  InferCtx* = ref object
    relDefs*: Table[string, RelDef]    ## relations defined as RelGoal data
    primModes*: Table[string, seq[Mode]] ## primitives: name -> modes (no body)

  InferResult* = object
    modes*: seq[Mode]        ## inferred per-param modes (entry = declared)
    callSites*: seq[CallSite] ## every rgCall, in propagation order
    errors*: seq[string]
    notes*: seq[string]
    noted: HashSet[string]   ## one-shot note keys (avoid spam)

proc newInferCtx*(): InferCtx =
  InferCtx(relDefs: initTable[string, RelDef](),
           primModes: initTable[string, seq[Mode]]())

proc defaultPrimModes*(): Table[string, seq[Mode]] =
  ## Modes for engine-level relations commonly called from RelGoal data.
  ## addo(a, b, c): a + b = c (rel_interp.nim); forward direction binds c.
  result = initTable[string, seq[Mode]]()
  result["addo"] = @[Mode.mIn, Mode.mIn, Mode.mOut]

proc noteOnce(res: var InferResult, key, msg: string) =
  if key notin res.noted:
    res.noted.incl(key)
    res.notes.add(msg)

proc argModeOf(t: RTerm, bound: HashSet[string]): ArgMode =
  let vs = varNamesIn(t)
  if vs.len == 0 or (vs - bound).len == 0: amIn
  elif (vs * bound).len == 0: amOut
  else: amMixed

proc groundUnder(t: RTerm, bound: HashSet[string]): bool =
  ## No placeholder vars outside `bound`: the specializer/engine treats
  ## t as known at this point.
  (varNamesIn(t) - bound).len == 0

proc calleeModes(ictx: InferCtx, name: string): tuple[found: bool, modes: seq[Mode]] =
  if name in ictx.relDefs: (true, ictx.relDefs[name].modes)
  elif name in ictx.primModes: (true, ictx.primModes[name])
  else: (false, @[])

proc propagate(rg: RelGoal, bound: var HashSet[string], ictx: InferCtx,
               res: var InferResult): bool =
  ## Thread the bound set through rg (Mercury-style scheduling).
  ## Returns false on hard error (details in res.errors).
  case rg.kind
  of rgFail, rgSucceed:
    true
  of rgEq:
    # Unification binds: if one side is ground under the current bound
    # set, the other side's vars become bound. Two free sides aliasing
    # each other bind nothing (conservative: aliasing isn't grounding).
    let lGround = groundUnder(rg.left, bound)
    let rGround = groundUnder(rg.right, bound)
    if lGround and not rGround:
      bound = bound + varNamesIn(rg.right)
    elif rGround and not lGround:
      bound = bound + varNamesIn(rg.left)
    true
  of rgNeq:
    true  # =/= never binds
  of rgConj:
    propagate(rg.leftG, bound, ictx, res) and
      propagate(rg.rightG, bound, ictx, res)
  of rgDisj:
    # Bound on all success paths = intersection (matches the checker's
    # boundVars for disjunction).
    var bL = bound
    var bR = bound
    let okL = propagate(rg.leftG, bL, ictx, res)
    let okR = propagate(rg.rightG, bR, ictx, res)
    bound = bL * bR
    okL and okR
  of rgFresh:
    let ph = "__var_" & rg.varName
    var bInner = bound
    bInner.excl(ph)  # fresh var starts free; shadows any outer same name
    let ok = propagate(rg.body, bInner, ictx, res)
    bInner.excl(ph)  # binder not visible outside
    bound = bInner   # bindings for outer vars flow out
    ok
  of rgCall:
    let (found, cm) = calleeModes(ictx, rg.relName)
    if not found:
      res.errors.add("unknown relation '" & rg.relName &
        "': declare its modes in InferCtx.primModes to analyze calls")
      return false
    if cm.len != rg.args.len:
      res.errors.add("arity mismatch for relation " & rg.relName &
        ": declared " & $cm.len & " params, called with " & $rg.args.len)
      return false
    var site = CallSite(relName: rg.relName, argModes: @[])
    # Callee param names for readable notes (data relations only).
    var calleeParams: seq[string] = @[]
    if rg.relName in ictx.relDefs:
      calleeParams = ictx.relDefs[rg.relName].params
    for i, a in rg.args:
      let am = argModeOf(a, bound)
      site.argModes.add(am)
      let pname = if i < calleeParams.len: calleeParams[i] else: "arg" & $i
      case cm[i]
      of mIn:
        # Partial deduction specializes per static signature, so a
        # dynamic arg here is fine — it gets its own specialization.
        # (Mercury-strict would reject; we record instead.)
        if am == amOut:
          res.notes.add(rg.relName & "." & pname &
            ": fully dynamic in mIn position — gets fully-dynamic specialization")
        elif am == amMixed:
          res.notes.add(rg.relName & "." & pname &
            ": partially static in mIn position — gets own specialization")
      of mOut:
        # The callee binds this argument: its vars join the bound set.
        for v in varNamesIn(a): bound.incl(v)
        if am == amMixed:
          noteOnce(res, "mixed-out-" & rg.relName & "-" & $i,
            "imprecision: " & rg.relName & " arg " & $i &
            " partially bound in mOut position; assuming the callee binds the rest")
      of mGround:
        discard
    res.callSites.add(site)
    true
  of rgSetEq:
    noteOnce(res, "seteq",
      "setEq constraints not modeled in binding propagation " &
      "(conservative: bind nothing; naked-single propagation is future work)")
    true
  of rgBranch:
    true  # branch annotations bind nothing

proc inferModes*(rd: RelDef, ictx: InferCtx): InferResult =
  ## Infer/verify modes for rd. Entry pattern = the declared modes:
  ## mIn params are bound at entry, mOut/mGround params are free.
  ## Returns inferred per-param modes (should equal rd.modes when the
  ## annotation is accurate), every nested call site with per-arg modes,
  ## and any errors/notes.
  result = InferResult(modes: @[], callSites: @[], errors: @[],
                       notes: @[], noted: initHashSet[string]())
  # Register self so recursive calls resolve.
  if rd.name notin ictx.relDefs:
    ictx.relDefs[rd.name] = rd
  var bound = initHashSet[string]()
  for i, p in rd.params:
    if rd.modes[i] == mIn:
      bound.incl("__var_" & p)
  if not propagate(rd.body, bound, ictx, result):
    return result
  result.modes = newSeq[Mode](rd.params.len)
  for i, p in rd.params:
    let ph = "__var_" & p
    case rd.modes[i]
    of mIn:
      result.modes[i] = mIn
    of mOut:
      if ph in bound:
        result.modes[i] = mOut
      else:
        result.modes[i] = mGround
        result.errors.add("param '" & p & "' declared mOut but not bound " &
          "on all success paths (fix the body or weaken to mGround)")
    of mGround:
      result.modes[i] = mGround
  # "Bound by body" lint: an mIn param the body would bind even when free
  # at call is really multi-directional (e.g. typeo's tm: the body binds
  # it, which is the synthesis direction of issue #9). Informative only.
  for i, p in rd.params:
    if rd.modes[i] == mIn:
      var b2 = initHashSet[string]()
      for j, q in rd.params:
        if j != i and rd.modes[j] == mIn:
          b2.incl("__var_" & q)
      var res2 = InferResult(modes: @[], callSites: @[], errors: @[],
                             notes: @[], noted: initHashSet[string]())
      discard propagate(rd.body, b2, ictx, res2)
      if ("__var_" & p) in b2:
        result.notes.add("param '" & p & "': bound by the body when free " &
          "at call — the relation also supports the output direction")

proc deriveDynamicVars*(rd: RelDef, staticParams: Table[string, RTerm],
                        ictx: InferCtx): HashSet[string] =
  ## Replace the manual dynamicVars annotation at specialization call
  ## sites: every param not statically known stays dynamic (staging must
  ## not bind it). Guarded by mode inference: unknown callees, unbound
  ## outputs, and static values for non-inputs are hard errors.
  let res = inferModes(rd, ictx)
  if res.errors.len > 0:
    raise newException(ValueError, "mode inference failed for '" & rd.name &
      "':\n  " & res.errors.join("\n  "))
  for p in staticParams.keys:
    let i = rd.params.find(p)
    if i < 0:
      raise newException(ValueError, "static param '" & p &
        "' is not a param of '" & rd.name & "'")
    if rd.modes[i] != mIn:
      raise newException(ValueError, "static value provided for non-input " &
        "param '" & p & "' of '" & rd.name & "' (mode " & $rd.modes[i] & ")")
  result = initHashSet[string]()
  for p in rd.params:
    if p notin staticParams:
      result.incl("__var_" & p)

proc specializeRelationAuto*(ctx: var SpecCtx, relName: string,
                             staticParams: Table[string, RTerm],
                             ictx: InferCtx): string =
  ## specializeRelation with mode inference deriving dynamicVars
  ## (issue #27, step 4): replaces the manual dynamicVars.incl(...) at
  ## call sites. Residuals must be identical to the manual version.
  let rd = ctx.relEnv[relName]
  let dyn = deriveDynamicVars(rd, staticParams, ictx)
  specializeRelation(ctx, relName, staticParams, dyn)

when isMainModule:
  import staging/stage_typeo
  import staging/stage_evalo

  echo "=== Mode inference (issue #27) ==="
  echo ""

  # --- evalo: call pattern [mIn, mOut] ---
  var ictxE = newInferCtx()
  let evaloDef = RelDef(name: "evalo", params: @["tm", "v"],
                        modes: @[mIn, mOut], body: evaloData())
  ictxE.relDefs["evalo"] = evaloDef
  ictxE.primModes = defaultPrimModes()
  let re = inferModes(evaloDef, ictxE)
  echo "evalo inferred modes: ", re.modes, " (declared: ", evaloDef.modes, ")"
  echo "  match: ", (re.modes == evaloDef.modes)
  echo "  errors: ", re.errors
  echo "  call sites:"
  for s in re.callSites:
    echo "    ", s.relName, " ", s.argModes
  echo "  notes:"
  for n in re.notes: echo "    - ", n
  echo ""

  # --- typeo: call pattern [mIn, mIn, mIn] ---
  var ictxT = newInferCtx()
  let typeoDef = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                        modes: @[mIn, mIn, mIn], body: typeoData())
  ictxT.relDefs["typeo"] = typeoDef
  let rt = inferModes(typeoDef, ictxT)
  echo "typeo inferred modes: ", rt.modes, " (declared: ", typeoDef.modes, ")"
  echo "  match: ", (rt.modes == typeoDef.modes)
  echo "  errors: ", rt.errors
  echo "  call sites:"
  for s in rt.callSites:
    echo "    ", s.relName, " ", s.argModes
  echo "  notes:"
  for n in rt.notes: echo "    - ", n
  echo ""

  # --- negative: unknown callee is a hard error ---
  var ictxB = newInferCtx()
  let badDef = RelDef(name: "bad", params: @["x"], modes: @[mIn],
                      body: rgCall("nope", @[ratom("__var_x")]))
  let rb = inferModes(badDef, ictxB)
  echo "unknown callee errors: ", rb.errors
  echo ""

  # --- negative: mOut not bound on all paths ---
  var ictxB2 = newInferCtx()
  let badDef2 = RelDef(name: "bad2", params: @["x", "y"],
                       modes: @[mIn, mOut],
                       body: rgDisj(rgEq(ratom("__var_y"), rint(1)),
                                    rgSucceed()))
  let rb2 = inferModes(badDef2, ictxB2)
  echo "unbound-output errors: ", rb2.errors
  echo ""

  let ok = re.errors.len == 0 and re.modes == evaloDef.modes and
           rt.errors.len == 0 and rt.modes == typeoDef.modes and
           rb.errors.len == 1 and rb2.errors.len == 1
  echo (if ok: "ALL INFERENCE CHECKS PASS" else: "INFERENCE CHECKS FAILED")
