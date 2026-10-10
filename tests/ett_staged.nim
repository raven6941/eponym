## Phase 2: ETT-specific staging rules (Sym[SVal])
##
## Builds on Layer 1 framework (staging/framework.nim).
## Provides Sym[SVal] instance: staging rules for ETT term formers.
##
## Key design:
## - SVal: staged ETT value. Three kinds:
##   - svStatic:    a Value known at staging time (closed, fully reduced).
##   - svStaticLam: a staging-time function SVal -> SVal. This is the
##     workhorse: applying it beta-reduces *at staging time*, which is
##     what makes specialization happen. cLam always produces these;
##     the host closure is staging-time code, not residual code.
##   - svDynamic:   residual ETTNode IR (only ETT formers appear here --
##     no staging machinery leaks into the residual).
## - cApp: svStaticLam applied to anything (static or dynamic) runs the
##   body now. Static vkLam applied to static arg reduces via the real
##   interpreter. Otherwise a residual enkApp node.
## - Residual evaluation: evalSVal interprets the ETTNode tree with the
##   real evalSym interpreter, so residual results are definitionally the
##   same values the unstaged interpreter produces.
##
## Hard questions (positions, cf. GH #17):
## - Metavariables: the ETT core has no metas (they live in elab.nim), so
##   there is nothing to reject at this layer. If a future staged
##   elaborator lifts open terms, the policy is: reject (error), since a
##   residual with holes is not a program.
## - Conversion: we beta-reduce when the function position is staging-time
##   known (svStaticLam, or static vkLam on a static arg). No full
##   normalization -- just enough reduction to enable specialization.
##   Residual neutrals stay stuck, exactly as in the interpreter.
## - Dependency: a type mentioning a dynamic value becomes a dynamic node
##   (enkPi/enkSigma keep the staged domain; the codomain family is staged
##   against a fresh dynamic variable). Types are residualized, not
##   computed -- specialization targets terms, and types follow.

import std/tables
import ett

# --- Residual IR nodes for ETT (the residual *code*; ETT formers only) ---

type
  ETTNodeKind* = enum
    enkVar,                       # dynamic variable (runtime input)
    enkTt, enkUnit, enkStar, enkEmpty,  # constants
    enkApp,                       # residual application
    enkLam, enkPi, enkSigma,       # binders (body staged against enkVar)
    enkPair,                      # pairing
    enkFst, enkSnd,               # projections
    enkAbsurd,                   # ex falso
    enkNat,                      # primitive nat literal (residual)
    enkPrim,                     # primitive operator application (residual)
    enkLet                       # let-inserted residual (effect escape hatch)

  SValKind* = enum svStatic, svStaticLam, svDynamic

  ETTNode* = ref object
    case kind*: ETTNodeKind
    of enkVar:
      varName*: string
    of enkApp:
      fn*, arg*: SVal
    of enkLam, enkPi, enkSigma:
      domNode*: SVal
      bindName*: string
      bodyNode*: proc(x: SVal): SVal
    of enkPair:
      fstN*, sndN*: SVal
    of enkFst, enkSnd, enkAbsurd:
      subN*: SVal
    of enkNat:
      natLitV*: int
    of enkPrim:
      opName*: string
      primArgs*: seq[SVal]
    of enkLet:
      letName*: string
      rhs*: SVal
      letBody*: proc(x: SVal): SVal
    of enkTt, enkUnit, enkStar, enkEmpty:
      discard

  SVal* = ref object
    ## Staged ETT value.
    case kind*: SValKind
    of svStatic:
      val*: Value                  # known at staging time
    of svStaticLam:
      body*: proc(x: SVal): SVal   # staging-time function
    of svDynamic:
      node*: ETTNode                # residual IR (ETT formers only)

var betaCount* = 0
  ## Staging-time beta-reductions performed. A measure of static work
  ## moved out of the residual.

var nameCounter = 0

proc freshVar*(hint: string): string =
  inc nameCounter
  hint & $nameCounter

proc staticVal*(v: Value): SVal =
  SVal(kind: svStatic, val: v)

proc dynamicVar*(name: string): SVal =
  ## A dynamic (runtime-known) variable: the residual input.
  SVal(kind: svDynamic, node: ETTNode(kind: enkVar, varName: name))

proc staticLam*(b: proc(x: SVal): SVal): SVal =
  SVal(kind: svStaticLam, body: b)

proc resetBetaCount*() =
  betaCount = 0

# --- Sym[SVal] instance: staging rules ---

proc stagedSym*(): Sym[SVal] =
  Sym[SVal](
    cStar: proc(): SVal = staticVal(Value(kind: vkStar)),
    cUnit: proc(): SVal = staticVal(Value(kind: vkUnit)),
    cTt: proc(): SVal = staticVal(Value(kind: vkTt)),
    cEmpty: proc(): SVal = staticVal(Value(kind: vkEmpty)),

    cPi: proc(dom: SVal, cod: proc(x: SVal): SVal): SVal =
      # Types are residualized: stage the family against a fresh dynamic
      # variable. The domain keeps its staging info (may stay static).
      let x = dynamicVar(freshVar("pi"))
      SVal(kind: svDynamic, node: ETTNode(kind: enkPi, domNode: dom,
        bindName: x.node.varName, bodyNode: cod)),

    cLam: proc(dom: SVal, body: proc(x: SVal): SVal): SVal =
      # Always a staging-time function: application beta-reduces now.
      # (The domain annotation is irrelevant for staging; it matters for
      # checking, which happens before staging.)
      staticLam(body),

    cApp: proc(f, a: SVal): SVal =
      # The key rule: staging-time beta-reduction.
      case f.kind
      of svStaticLam:
        inc betaCount
        f.body(a)
      of svStatic:
        if a.kind == svStatic and f.val.kind == vkLam:
          inc betaCount
          staticVal(f.val.body(a.val))
        else:
          SVal(kind: svDynamic,
            node: ETTNode(kind: enkApp, fn: f, arg: a))
      of svDynamic:
        SVal(kind: svDynamic, node: ETTNode(kind: enkApp, fn: f, arg: a)),

    cSigma: proc(dom: SVal, cod: proc(x: SVal): SVal): SVal =
      let x = dynamicVar(freshVar("sig"))
      SVal(kind: svDynamic, node: ETTNode(kind: enkSigma, domNode: dom,
        bindName: x.node.varName, bodyNode: cod)),

    cPair: proc(a, b: SVal): SVal =
      if a.kind == svStatic and b.kind == svStatic:
        staticVal(Value(kind: vkPair, fstV: a.val, sndV: b.val))
      else:
        SVal(kind: svDynamic, node: ETTNode(kind: enkPair, fstN: a, sndN: b)),

    cFst: proc(p: SVal): SVal =
      case p.kind
      of svStatic:
        if p.val.kind == vkPair: staticVal(p.val.fstV)
        else: SVal(kind: svDynamic, node: ETTNode(kind: enkFst, subN: p))
      of svDynamic:
        if p.node.kind == enkPair: p.node.fstN  # staging-time projection
        else: SVal(kind: svDynamic, node: ETTNode(kind: enkFst, subN: p))
      of svStaticLam:
        SVal(kind: svDynamic, node: ETTNode(kind: enkFst, subN: p)),

    cSnd: proc(p: SVal): SVal =
      case p.kind
      of svStatic:
        if p.val.kind == vkPair: staticVal(p.val.sndV)
        else: SVal(kind: svDynamic, node: ETTNode(kind: enkSnd, subN: p))
      of svDynamic:
        if p.node.kind == enkPair: p.node.sndN  # staging-time projection
        else: SVal(kind: svDynamic, node: ETTNode(kind: enkSnd, subN: p))
      of svStaticLam:
        SVal(kind: svDynamic, node: ETTNode(kind: enkSnd, subN: p)),

    cAbsurd: proc(z: SVal): SVal =
      SVal(kind: svDynamic, node: ETTNode(kind: enkAbsurd, subN: z)),
  )

# --- Online primitive operators (GH #79) ---
##
## Danvy's online extension of TDPE (BRICS RS-97-53; see
## notes/online-primitive-operators.org): each primitive-operator (δ-rule)
## call decides *at specialization time* whether to unfold or residualize,
## and the user programs both sides of the decision:
## - Default policy: all operands static → unfold via staticSem;
##   any dynamic operand → residualize the call. Binding times are
##   polyvariant for free — the same operator unfolds at one call site
##   and residualizes at another.
## - Unfold control (filters): a user predicate over the operands gating
##   unfold, à la Consel's filters in Schism. Demo: `pow` unfolds only
##   when the exponent is static (and small — a termination/size guard).
## - Residualize control (dynamic versions): algebraic simplifications
##   over residual syntax (`x + 0 → x`, `0 × y → 0`, `1 × y → y`).
##   Discarding a residual computation (`0 × y → 0`) is sound only for
##   pure operators — effectful ones take the escape hatch below.
## - Effect escape hatch: an operator flagged `effectful` (in a full
##   implementation this flag comes from an effect annotation on its
##   type) is unconditionally residualized and let-inserted, so its
##   call is named and ordered in the residual. Simplifications do not
##   fire on effectful calls.

type
  PrimOp* = object
    ## One primitive operator: its static semantics, its unfold gate,
    ## its residual-side rewrite rules, and its effect flag.
    name*: string
    arity*: int
    staticSem*: proc(args: seq[int]): int
      ## Unfold semantics: staging-time evaluation on static operands.
    filter*: proc(args: seq[SVal]): bool
      ## Unfold gate. Default: all operands static nats.
    simp*: proc(name: string, args: seq[SVal]): SVal
      ## Algebraic simplification over residual args; nil = no rule fires.
    effectful*: bool
      ## Escape hatch: always residualize + let-insert; skip simp.

var primUnfolds* = 0    ## unfold decisions taken
var primResiduals* = 0  ## residualize decisions taken
var primSimps* = 0      ## algebraic simplifications fired

proc resetPrimStats*() =
  primUnfolds = 0
  primResiduals = 0
  primSimps = 0

proc isStaticNat*(s: SVal): bool =
  s.kind == svStatic and s.val.kind == vkNat

proc natLit*(n: int): SVal =
  ## A static nat literal: known at staging time, no residual trace.
  staticVal(Value(kind: vkNat, natV: n))

proc defaultFilter*(args: seq[SVal]): bool =
  for a in args:
    if not isStaticNat(a): return false
  true

proc powFilter*(args: seq[SVal]): bool =
  ## Consel-style filter for `pow`: unfold only when the exponent is a
  ## static nat below the size guard (32). A static-but-huge exponent
  ## would blow up the residual; the user programs the policy.
  args.len == 2 and isStaticNat(args[1]) and args[1].val.natV < 32 and
    isStaticNat(args[0])

proc noSimp*(name: string, args: seq[SVal]): SVal = nil

proc arithSimp*(name: string, args: seq[SVal]): SVal =
  ## Algebraic simplifications over residual args (Danvy's dynamic
  ## versions). Sound for pure operators only: `0 × y → 0` discards a
  ## residual computation, which is safe iff y's computation is pure.
  if name == "add" and args.len == 2:
    if isStaticNat(args[1]) and args[1].val.natV == 0: return args[0]
    if isStaticNat(args[0]) and args[0].val.natV == 0: return args[1]
  elif name == "mul" and args.len == 2:
    if isStaticNat(args[0]) and args[0].val.natV == 0: return natLit(0)
    if isStaticNat(args[1]) and args[1].val.natV == 0: return natLit(0)
    if isStaticNat(args[0]) and args[0].val.natV == 1: return args[1]
    if isStaticNat(args[1]) and args[1].val.natV == 1: return args[0]
  nil

proc primNode(name: string, args: seq[SVal]): SVal =
  SVal(kind: svDynamic,
    node: ETTNode(kind: enkPrim, opName: name, primArgs: args))

proc letInsert*(s: SVal): SVal =
  ## Name a residual computation: `let x = s in x`. The residual keeps
  ## the call ordered and shared (the local counterpart of #61 genlet).
  if s.kind == svDynamic and s.node.kind == enkPrim:
    let nm = freshVar("p")
    SVal(kind: svDynamic,
      node: ETTNode(kind: enkLet, letName: nm, rhs: s,
        letBody: proc(v: SVal): SVal = v))
  else:
    s

proc applyPrim*(op: PrimOp, args: seq[SVal]): SVal =
  ## The online policy: decide unfold-vs-residualize per call, at
  ## specialization time.
  assert args.len == op.arity, "arity mismatch for primop " & op.name
  if op.effectful:
    # Escape hatch: name the call, keep it ordered; no simplification.
    inc primResiduals
    return letInsert(primNode(op.name, args))
  if op.filter(args):
    inc primUnfolds
    var ints = newSeq[int](args.len)
    for i, a in args: ints[i] = a.val.natV
    return natLit(op.staticSem(ints))
  inc primResiduals
  let simplified = op.simp(op.name, args)
  if simplified != nil:
    inc primSimps
    return simplified
  primNode(op.name, args)

proc applyPrimFixed*(op: PrimOp, args: seq[SVal]): SVal =
  ## The fixed offline policy (baseline for #79's benchmark): unfold iff
  ## all operands are static, else residualize — no filters, no
  ## algebraic simplification, no effect escape hatch.
  assert args.len == op.arity, "arity mismatch for primop " & op.name
  var allStatic = true
  for a in args:
    if not isStaticNat(a): allStatic = false
  if allStatic:
    var ints = newSeq[int](args.len)
    for i, a in args: ints[i] = a.val.natV
    return natLit(op.staticSem(ints))
  primNode(op.name, args)

proc powInt(base, exp: int): int =
  var r = 1
  for _ in 0 ..< exp: r *= base
  r

proc defaultPrimTable*(): Table[string, PrimOp] =
  result = initTable[string, PrimOp]()
  result["add"] = PrimOp(name: "add", arity: 2,
    staticSem: proc(a: seq[int]): int = a[0] + a[1],
    filter: defaultFilter, simp: arithSimp, effectful: false)
  result["mul"] = PrimOp(name: "mul", arity: 2,
    staticSem: proc(a: seq[int]): int = a[0] * a[1],
    filter: defaultFilter, simp: arithSimp, effectful: false)
  result["pow"] = PrimOp(name: "pow", arity: 2,
    staticSem: proc(a: seq[int]): int = powInt(a[0], a[1]),
    filter: powFilter, simp: noSimp, effectful: false)
  # Demo effectful operator: same value semantics as add, but the
  # effect flag models an effect-annotated type — always residualized
  # and let-inserted, never unfolded or simplified.
  result["traceAdd"] = PrimOp(name: "traceAdd", arity: 2,
    staticSem: proc(a: seq[int]): int = a[0] + a[1],
    filter: defaultFilter, simp: noSimp, effectful: true)

var primTable* = defaultPrimTable()
  ## The staged evaluator's primitive-operator table (per-operator static
  ## semantics + residual former + policy hooks).

# --- Residual evaluation: run the residual with the real interpreter ---

proc evalSVal*(s: SVal, env: Table[string, Value]): Value =
  ## Evaluate a staged value to a real Value. Static parts are already
  ## values; residual nodes are interpreted with evalSym, so the result
  ## is definitionally what the unstaged interpreter would produce.
  case s.kind
  of svStatic:
    s.val
  of svStaticLam:
    # Reify the staging-time function as a host closure over Values.
    let b = s.body
    let e = env
    Value(kind: vkLam, body: proc(x: Value): Value =
      evalSVal(b(staticVal(x)), e))
  of svDynamic:
    let n = s.node
    case n.kind
    of enkVar:
      env[n.varName]
    of enkTt: Value(kind: vkTt)
    of enkUnit: Value(kind: vkUnit)
    of enkStar: Value(kind: vkStar)
    of enkEmpty: Value(kind: vkEmpty)
    of enkApp:
      evalSym.cApp(evalSVal(n.fn, env), evalSVal(n.arg, env))
    of enkLam:
      let e = env
      let bn = n.bindName
      let bb = n.bodyNode
      Value(kind: vkLam, body: proc(x: Value): Value =
        var e2 = e
        e2[bn] = x
        evalSVal(bb(staticVal(x)), e2))
    of enkPi:
      let d = evalSVal(n.domNode, env)
      let e = env
      let bn = n.bindName
      let bb = n.bodyNode
      Value(kind: vkPi, dom: d, cod: proc(x: Value): Value =
        var e2 = e
        e2[bn] = x
        evalSVal(bb(staticVal(x)), e2))
    of enkSigma:
      let d = evalSVal(n.domNode, env)
      let e = env
      let bn = n.bindName
      let bb = n.bodyNode
      Value(kind: vkSigma, dom: d, cod: proc(x: Value): Value =
        var e2 = e
        e2[bn] = x
        evalSVal(bb(staticVal(x)), e2))
    of enkPair:
      evalSym.cPair(evalSVal(n.fstN, env), evalSVal(n.sndN, env))
    of enkFst:
      evalSym.cFst(evalSVal(n.subN, env))
    of enkSnd:
      evalSym.cSnd(evalSVal(n.subN, env))
    of enkAbsurd:
      evalSym.cAbsurd(evalSVal(n.subN, env))
    of enkNat:
      Value(kind: vkNat, natV: n.natLitV)
    of enkPrim:
      var ints = newSeq[int](n.primArgs.len)
      for i, a in n.primArgs:
        let v = evalSVal(a, env)
        if v.kind != vkNat:
          raise newException(ValueError,
            "residual primop '" & n.opName & "' applied to non-nat")
        ints[i] = v.natV
      let op = primTable[n.opName]
      Value(kind: vkNat, natV: op.staticSem(ints))
    of enkLet:
      let v = evalSVal(n.rhs, env)
      var e2 = env
      e2[n.letName] = v
      evalSVal(n.letBody(staticVal(v)), e2)

# --- Residual inspection: single recursive printer (distinct helper names
# avoid overload/tuple-`$` ambiguity) ---

proc ppSVal(s: SVal, depth: int): string
proc ppNode(n: ETTNode, depth: int): string =
  if depth > 8: return "..."
  case n.kind
  of enkVar: n.varName
  of enkTt: "<>"
  of enkUnit: "1"
  of enkStar: "*"
  of enkEmpty: "0"
  of enkApp: "(" & ppSVal(n.fn, depth+1) & " " & ppSVal(n.arg, depth+1) & ")"
  of enkLam: "(lam [" & n.bindName & "] " & ppSVal(n.bodyNode(dynamicVar(n.bindName)), depth+1) & ")"
  of enkPi: "(Pi [" & n.bindName & "] " & ppSVal(n.bodyNode(dynamicVar(n.bindName)), depth+1) & ")"
  of enkSigma: "(Sig [" & n.bindName & "] " & ppSVal(n.bodyNode(dynamicVar(n.bindName)), depth+1) & ")"
  of enkPair: "(pair " & ppSVal(n.fstN, depth+1) & " " & ppSVal(n.sndN, depth+1) & ")"
  of enkFst: "(fst " & ppSVal(n.subN, depth+1) & ")"
  of enkSnd: "(snd " & ppSVal(n.subN, depth+1) & ")"
  of enkAbsurd: "(absurd " & ppSVal(n.subN, depth+1) & ")"
  of enkNat: $n.natLitV
  of enkPrim:
    var s = "(" & n.opName
    for a in n.primArgs: s &= " " & ppSVal(a, depth+1)
    s & ")"
  of enkLet:
    "(let [" & n.letName & "] " & ppSVal(n.rhs, depth+1) & " " &
      ppSVal(n.letBody(dynamicVar(n.letName)), depth+1) & ")"

proc ppSVal(s: SVal, depth: int): string =
  if depth > 8: return "..."
  case s.kind
  of svStatic: "static(" & $s.val.kind & ")"
  of svStaticLam: "<slam>"
  of svDynamic: ppNode(s.node, depth)

proc `$`*(s: SVal): string = ppSVal(s, 0)

proc countNodes*(s: SVal): int =
  ## Count residual ETTNode nodes. Static parts contribute 0: they left
  ## no trace in the residual.
  case s.kind
  of svStatic: 0
  of svStaticLam: 0
  of svDynamic:
    let n = s.node
    case n.kind
    of enkVar, enkTt, enkUnit, enkStar, enkEmpty: 1
    of enkApp: 1 + countNodes(n.fn) + countNodes(n.arg)
    of enkLam, enkPi, enkSigma:
      1 + countNodes(n.domNode) + countNodes(n.bodyNode(dynamicVar(n.bindName)))
    of enkPair: 1 + countNodes(n.fstN) + countNodes(n.sndN)
    of enkFst, enkSnd, enkAbsurd: 1 + countNodes(n.subN)
    of enkNat: 1
    of enkPrim:
      var c = 1
      for a in n.primArgs: c += countNodes(a)
      c
    of enkLet:
      1 + countNodes(n.rhs) + countNodes(n.letBody(dynamicVar(n.letName)))

when isMainModule:
  echo "=== Phase 2: Sym[SVal] staging rules ==="
  echo "cApp beta-reduces staging-time functions (svStaticLam)."
  echo "cPair/cFst/cSnd fold when static; project through residual pairs."
  echo "evalSVal runs residuals with the real interpreter (evalSym)."
  echo "See stage_ett_demo.nim for the end-to-end validation."
