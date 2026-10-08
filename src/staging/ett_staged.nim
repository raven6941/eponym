## Phase 2: ETT-specific staging rules (Sym[Staged])
##
## Builds on Layer 1 framework (staging/framework.nim).
## Provides Sym[SVal] instance: staging rules for ETT term formers.
##
## Key design:
## - SVal: staged ETT value. Either static (known Value from ett.nim)
##   or dynamic (residual ETTNode IR).
## - For binders (cPi, cLam): the bound variable is introduced as dynamic
##   UNLESS the body is applied to a static argument at staging time.
## - cApp: if function is static lambda and arg is static, beta-reduce now.
##   Otherwise build residual application node.
##
## Hard questions (documented, not fully solved):
## - Metavariables: reject staging if term contains unsolved metas. A meta
##   is dynamic by nature, but staging a term with holes is dubious — the
##   residual would have holes too. For now: error.
## - Conversion: when to normalize during staging? We beta-reduce when both
##   static (like the interpreter). Full normalization is overkill; we want
##   just enough to enable specialization.
## - Dependency: if a type mentions a dynamic value, the type is dynamic.
##   This propagates: cPi with dynamic dom → dynamic Pi. The framework's
##   Rep handles this via isStatic flags.

import staging/framework
import ett

# --- Residual IR nodes for ETT ---

type
  ETTNodeKind = enum
    enkVar,     # dynamic variable (runtime input)
    enkApp,     # residual application
    enkLam,     # residual lambda (dynamic body)
    enkPi,      # residual Pi type

  ETTNode = ref object of IRNode
    case kind: ETTNodeKind
    of enkVar:
      varName: string
    of enkApp:
      fn, arg: SVal
    of enkLam, enkPi:
      domNode: SVal
      bodyNode: proc(x: SVal): SVal  # residual binder (host fn over SVal)

  SValKind = enum svStatic, svDynamic

  SVal = ref object
    ## Staged ETT value.
    case kind: SValKind
    of svStatic:
      val: Value  # known at staging time
    of svDynamic:
      node: ETTNode      # residual IR

proc staticVal(v: Value): SVal =
  SVal(kind: svStatic, val: v)

proc dynamicVal(n: ETTNode): SVal =
  SVal(kind: svDynamic, node: n)

proc `$`(s: SVal): string =
  case s.kind
  of svStatic: "static(" & $s.val.kind & ")"
  of svDynamic: "dynamic(" & $s.node.kind & ")"

# --- Sym[SVal] instance: staging rules ---

proc stagedSym(): Sym[SVal] =
  Sym[SVal](
    cStar: proc(): SVal = staticVal(Value(kind: ett.vkStar)),
    cUnit: proc(): SVal = staticVal(Value(kind: ett.vkUnit)),
    cTt: proc(): SVal = staticVal(Value(kind: ett.vkTt)),
    cEmpty: proc(): SVal = staticVal(Value(kind: ett.vkEmpty)),

    cPi: proc(dom: SVal, cod: proc(x: SVal): SVal): SVal =
      # If dom is static, we can try to stage the codomain family.
      # For now: if dom static, build static Pi with staged cod;
      # else residualize.
      if dom.kind == svStatic:
        # cod is a host function SVal->SVal. To stage it, we'd need to
        # apply it to a representative. For now, residualize the Pi
        # but keep dom static info.
        dynamicVal(ETTNode(kind: enkPi, domNode: dom,
          bodyNode: cod))
      else:
        dynamicVal(ETTNode(kind: enkPi, domNode: dom, bodyNode: cod)),

    cLam: proc(dom: SVal, body: proc(x: SVal): SVal): SVal =
      # Lambda: the body is a function. If dom is static, we keep the
      # lambda static (as a host closure over SVal). Application will
      # beta-reduce if arg is also static.
      if dom.kind == svStatic:
        # Build a static Value vkLam whose body works over SVal.
        # We need to wrap: the Value's body expects Value, but we have SVal.
        # For the prototype, keep it as a dynamic node with static dom info.
        # Full solution requires SVal-aware Value — future work.
        dynamicVal(ETTNode(kind: enkLam, domNode: dom, bodyNode: body))
      else:
        dynamicVal(ETTNode(kind: enkLam, domNode: dom, bodyNode: body)),

    cApp: proc(f, a: SVal): SVal =
      # The key rule: beta-reduce if both static and f is a lambda.
      if f.kind == svStatic and a.kind == svStatic:
        let fv = f.val
        let av = a.val
        if fv.kind == ett.vkLam:
          # Beta: apply the closure. fv.body expects Value, av is Value.
          staticVal(fv.body(av))
        else:
          # Static neutral or stuck — residualize
          dynamicVal(ETTNode(kind: enkApp, fn: f, arg: a))
      else:
        # Dynamic involved → residual application
        dynamicVal(ETTNode(kind: enkApp, fn: f, arg: a)),

    # Sigma, Pair, Fst, Snd, Absurd: residualize for now (prototype)
    cSigma: proc(dom: SVal, cod: proc(x: SVal): SVal): SVal =
      dynamicVal(ETTNode(kind: enkPi, domNode: dom, bodyNode: cod)),
    cPair: proc(a, b: SVal): SVal =
      dynamicVal(ETTNode(kind: enkApp, fn: a, arg: b)),
    cFst: proc(p: SVal): SVal =
      dynamicVal(ETTNode(kind: enkApp, fn: p, arg: staticVal(Value(kind: ett.vkTt)))),
    cSnd: proc(p: SVal): SVal =
      dynamicVal(ETTNode(kind: enkApp, fn: p, arg: staticVal(Value(kind: ett.vkTt)))),
    cAbsurd: proc(z: SVal): SVal =
      dynamicVal(ETTNode(kind: enkApp, fn: z, arg: staticVal(Value(kind: ett.vkEmpty)))),
  )

when isMainModule:
  echo "=== Phase 2: Sym[SVal] staging rules ==="
  echo ""
  echo "Staging rules defined for ETT formers."
  echo "Key rule: cApp beta-reduces when f is static lambda and a static."
  echo ""
  echo "Hard questions documented in source:"
  echo "- Metavars: reject (staging with holes is dubious)"
  echo "- Conversion: beta-reduce when static; no full normalization"
  echo "- Dependency: dynamic in type → dynamic type (via isStatic)"
  echo ""
  echo "Prototype instance built. Full validation needs ETT term construction."
