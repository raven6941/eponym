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
import preterm  # Quantity/q0/q1/qOmega (Issue #94: erasure-aware staging)

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

  SValKind* = enum svStatic, svStaticLam, svDynamic, svErased
    ## svErased (Issue #94): the staging-time stand-in for a 0-quantity-bound
    ## variable. It must never flow into residual code: every residual
    ## constructor rejects it loudly via checkNotErased.

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
      qty*: Quantity  # Issue #94: binder quantity; q0 term binders are
                      # dropped at residualization (enkLam). enkPi/enkSigma
                      # keep the binder (dependency may mention it; types
                      # are not runtime code).
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
      lamQty*: Quantity            # Issue #94: binder quantity
    of svDynamic:
      node*: ETTNode                # residual IR (ETT formers only)
    of svErased:
      discard                       # marker only; no payload

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

proc staticLam*(b: proc(x: SVal): SVal, qty = qOmega): SVal =
  SVal(kind: svStaticLam, body: b, lamQty: qty)

proc erasedSVal*(): SVal =
  ## The staging-time stand-in for a 0-quantity-bound variable (Issue #94).
  SVal(kind: svErased)

proc isErased*(s: SVal): bool =
  s.kind == svErased

proc checkNotErased(s: SVal, ctx: string) =
  ## Boundary check (Issue #94, step 3): an erased binder must never appear
  ## in residualized code. A violation means the quantity checker certified
  ## a variable absent at runtime that the staging-time program actually
  ## residualized — surfaced loudly, never silenced.
  if s.kind == svErased:
    raise newException(ValueError,
      "erasure violation (Issue #94): 0-quantity binder flows into " & ctx)

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
      checkNotErased(dom, "cPi domain")
      let x = dynamicVar(freshVar("pi"))
      SVal(kind: svDynamic, node: ETTNode(kind: enkPi, domNode: dom,
        bindName: x.node.varName, bodyNode: cod, qty: qOmega)),

    cLam: proc(dom: SVal, body: proc(x: SVal): SVal): SVal =
      # Always a staging-time function: application beta-reduces now.
      # (The domain annotation is irrelevant for staging; it matters for
      # checking, which happens before staging.)
      checkNotErased(dom, "cLam domain")
      staticLam(body),

    cApp: proc(f, a: SVal): SVal =
      # The key rule: staging-time beta-reduction.
      checkNotErased(f, "function position of cApp")
      case f.kind
      of svStaticLam:
        inc betaCount
        if f.lamQty == q0:
          # Erasure (Issue #94): the argument is dropped at staging time —
          # never staged, never residualized. The body runs against the
          # erased marker; any attempt to residualize it raises loudly.
          # (Sound for the pure core; an effectful #79 argument would lose
          # its effect — the elaborator must not pass those to q0 binders.)
          f.body(erasedSVal())
        else:
          f.body(a)
      of svStatic:
        if a.kind == svStatic and f.val.kind == vkLam:
          inc betaCount
          staticVal(f.val.body(a.val))
        else:
          checkNotErased(a, "residual application argument")
          SVal(kind: svDynamic,
            node: ETTNode(kind: enkApp, fn: f, arg: a))
      of svDynamic:
        if f.node.kind == enkLam:
          # Residual redex (Issue #94): beta-reduce at staging time (HOAS —
          # just supply the argument SVal). A q0 binder drops the argument
          # from the residual: the call-site half of the issue's step 2.
          inc betaCount
          if f.node.qty == q0:
            f.node.bodyNode(erasedSVal())
          else:
            checkNotErased(a, "residual application argument")
            f.node.bodyNode(a)
        else:
          checkNotErased(a, "residual application argument")
          SVal(kind: svDynamic,
            node: ETTNode(kind: enkApp, fn: f, arg: a))
      of svErased:
        raise newException(ValueError,
          "unreachable: erased function (checked above)"),

    cSigma: proc(dom: SVal, cod: proc(x: SVal): SVal): SVal =
      checkNotErased(dom, "cSigma domain")
      let x = dynamicVar(freshVar("sig"))
      SVal(kind: svDynamic, node: ETTNode(kind: enkSigma, domNode: dom,
        bindName: x.node.varName, bodyNode: cod, qty: qOmega)),

    cPair: proc(a, b: SVal): SVal =
      if a.kind == svStatic and b.kind == svStatic:
        staticVal(Value(kind: vkPair, fstV: a.val, sndV: b.val))
      else:
        checkNotErased(a, "cPair first component")
        checkNotErased(b, "cPair second component")
        SVal(kind: svDynamic, node: ETTNode(kind: enkPair, fstN: a, sndN: b)),

    cFst: proc(p: SVal): SVal =
      checkNotErased(p, "cFst")
      case p.kind
      of svStatic:
        if p.val.kind == vkPair: staticVal(p.val.fstV)
        else: SVal(kind: svDynamic, node: ETTNode(kind: enkFst, subN: p))
      of svDynamic:
        if p.node.kind == enkPair: p.node.fstN  # staging-time projection
        else: SVal(kind: svDynamic, node: ETTNode(kind: enkFst, subN: p))
      of svStaticLam:
        SVal(kind: svDynamic, node: ETTNode(kind: enkFst, subN: p))
      of svErased:
        raise newException(ValueError,
          "unreachable: erased value (checked above)"),

    cSnd: proc(p: SVal): SVal =
      checkNotErased(p, "cSnd")
      case p.kind
      of svStatic:
        if p.val.kind == vkPair: staticVal(p.val.sndV)
        else: SVal(kind: svDynamic, node: ETTNode(kind: enkSnd, subN: p))
      of svDynamic:
        if p.node.kind == enkPair: p.node.sndN  # staging-time projection
        else: SVal(kind: svDynamic, node: ETTNode(kind: enkSnd, subN: p))
      of svStaticLam:
        SVal(kind: svDynamic, node: ETTNode(kind: enkSnd, subN: p))
      of svErased:
        raise newException(ValueError,
          "unreachable: erased value (checked above)"),

    cAbsurd: proc(z: SVal): SVal =
      checkNotErased(z, "cAbsurd")
      SVal(kind: svDynamic, node: ETTNode(kind: enkAbsurd, subN: z)),
  )

# --- Quantity-annotated staging (Issue #94) ---
##
## Explicit binder quantities for the staged layer. The shared Sym[R]
## interface stays quantity-free; programs that want erasure use these
## staged-layer constructors directly ("behind annotations"; quantity
## inference is Issue #84).

proc cLamQ*(dom: SVal, qty: Quantity, body: proc(x: SVal): SVal): SVal =
  ## Quantity-annotated lambda. A q0 binder is erased: cApp drops the
  ## argument at staging time (staging it against the erased marker), and
  ## reifyLam drops the binder from the residual.
  checkNotErased(dom, "cLamQ domain")
  staticLam(body, qty)

proc cPiQ*(dom: SVal, qty: Quantity, cod: proc(x: SVal): SVal): SVal =
  ## Quantity-annotated Pi. The qty is recorded on the residual type node;
  ## the binder is KEPT even for q0: the codomain is a type and may mention
  ## the variable (dependency) — types are not runtime code, so erasure
  ## does not drop them. Term-level erasure is cLamQ/reifyLam.
  checkNotErased(dom, "cPiQ domain")
  let x = dynamicVar(freshVar("pi"))
  SVal(kind: svDynamic, node: ETTNode(kind: enkPi, domNode: dom,
    bindName: x.node.varName, bodyNode: cod, qty: qty))

proc cSigmaQ*(dom: SVal, qty: Quantity, cod: proc(x: SVal): SVal): SVal =
  ## Quantity-annotated Sigma (same policy as cPiQ).
  checkNotErased(dom, "cSigmaQ domain")
  let x = dynamicVar(freshVar("sig"))
  SVal(kind: svDynamic, node: ETTNode(kind: enkSigma, domNode: dom,
    bindName: x.node.varName, bodyNode: cod, qty: qty))

proc reifyLam*(s: SVal, dom: SVal): SVal =
  ## NbE-style reification: turn a staging-time function into a residual
  ## enkLam node. This is what makes enkLam — previously never produced —
  ## real: it is the residual a higher-order or unapplied staged function
  ## leaves behind. A q0 binder is dropped from the residual: the body is
  ## staged once, eagerly, against the erased marker (so a boundary
  ## violation raises here, at reification time), and the node carries no
  ## binder name.
  checkNotErased(dom, "reifyLam domain")
  checkNotErased(s, "reifyLam")
  case s.kind
  of svStaticLam:
    let q = s.lamQty
    let b = s.body
    if q == q0:
      let stagedBody = b(erasedSVal())  # raises loudly on misuse
      SVal(kind: svDynamic, node: ETTNode(kind: enkLam, domNode: dom,
        bindName: "", bodyNode: proc(x: SVal): SVal = stagedBody, qty: q))
    else:
      # bodyNode threads its argument: reification stages b against the
      # named variable, and a residual redex (cApp on this node) beta-
      # reduces by supplying the actual argument SVal.
      let nm = freshVar("lam")
      SVal(kind: svDynamic, node: ETTNode(kind: enkLam, domNode: dom,
        bindName: nm, bodyNode: b, qty: q))
  else:
    raise newException(ValueError,
      "reifyLam: expected a staging-time function (svStaticLam)")

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
  for a in args: checkNotErased(a, "primitive '" & name & "' argument")
  SVal(kind: svDynamic,
    node: ETTNode(kind: enkPrim, opName: name, primArgs: args))

proc letInsert*(s: SVal): SVal =
  ## Name a residual computation: `let x = s in x`. The residual keeps
  ## the call ordered and shared (the local counterpart of #61 genlet).
  checkNotErased(s, "letInsert")
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
    let q = s.lamQty
    if q == q0:
      # Erased binder (Issue #94): the residual closure takes no meaningful
      # argument; the body was already staged against the marker.
      Value(kind: vkLam, body: proc(x: Value): Value =
        evalSVal(b(erasedSVal()), e))
    else:
      Value(kind: vkLam, body: proc(x: Value): Value =
        evalSVal(b(staticVal(x)), e))
  of svErased:
    raise newException(ValueError,
      "erasure violation (Issue #94): erased value reached residual evaluation")
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
      if n.qty == q0:
        # Erased binder (Issue #94): no binder in the residual; the body
        # was staged against the marker. The closure ignores its argument.
        Value(kind: vkLam, body: proc(x: Value): Value =
          evalSVal(bb(erasedSVal()), e))
      else:
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
proc qtyTag(q: Quantity): string =
  ## Suffix showing the threaded binder quantity (Issue #94).
  case q
  of q0: ":q0"
  of q1: ":q1"
  of qOmega: ""
proc ppNode(n: ETTNode, depth: int): string =
  if depth > 8: return "..."
  case n.kind
  of enkVar: n.varName
  of enkTt: "<>"
  of enkUnit: "1"
  of enkStar: "*"
  of enkEmpty: "0"
  of enkApp: "(" & ppSVal(n.fn, depth+1) & " " & ppSVal(n.arg, depth+1) & ")"
  of enkLam:
    # A q0 binder is dropped from the residual: no binder name printed.
    let bnd = if n.qty == q0: "[]" else: "[" & n.bindName & "]"
    let argS = if n.qty == q0: erasedSVal() else: dynamicVar(n.bindName)
    "(lam" & qtyTag(n.qty) & " " & bnd & " " &
      ppSVal(n.bodyNode(argS), depth+1) & ")"
  of enkPi:
    "(Pi" & qtyTag(n.qty) & " [" & n.bindName & "] " &
      ppSVal(n.bodyNode(dynamicVar(n.bindName)), depth+1) & ")"
  of enkSigma:
    "(Sig" & qtyTag(n.qty) & " [" & n.bindName & "] " &
      ppSVal(n.bodyNode(dynamicVar(n.bindName)), depth+1) & ")"
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
  of svStaticLam: "<slam" & qtyTag(s.lamQty) & ">"
  of svErased:
    raise newException(ValueError,
      "erasure violation (Issue #94): erased value reached the printer")
  of svDynamic: ppNode(s.node, depth)

proc `$`*(s: SVal): string = ppSVal(s, 0)

proc countNodes*(s: SVal): int =
  ## Count residual ETTNode nodes. Static parts contribute 0: they left
  ## no trace in the residual.
  case s.kind
  of svStatic: 0
  of svStaticLam: 0
  of svErased:
    raise newException(ValueError,
      "erasure violation (Issue #94): erased value reached countNodes")
  of svDynamic:
    let n = s.node
    case n.kind
    of enkVar, enkTt, enkUnit, enkStar, enkEmpty: 1
    of enkApp: 1 + countNodes(n.fn) + countNodes(n.arg)
    of enkLam, enkPi, enkSigma:
      # A q0 enkLam body was staged against the marker and ignores its
      # argument; pass the marker (never counted — bodyNode drops it).
      let argS = if n.kind == enkLam and n.qty == q0: erasedSVal()
                 else: dynamicVar(n.bindName)
      1 + countNodes(n.domNode) + countNodes(n.bodyNode(argS))
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
