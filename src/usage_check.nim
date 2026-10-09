## Usage checker for linear binders — Issue #64
##
## Post-elaboration pass that verifies quantitative usage:
## - q1 (linear) binders must be used exactly once
## - q0 (erased) binders must not be used
## - qOmega (unrestricted) binders are unchecked
##
## Walks the elaborated Term (which carries qty on tPi/tLam from the
## integration) with a stack of (qty, used) flags.

import ett_init
import preterm  # for Quantity

type
  UsageError* = object of CatchableError
  BinderUsage* = object
    qty*: Quantity
    used*: bool

proc checkUsage*(tm: Term): void =
  ## Verify linear/erased usage in the elaborated term.
  ## Raises UsageError on violation.
  var stack: seq[BinderUsage] = @[]

  proc go(t: Term) =
    case t.kind
    of tV:
      let i = t.idx
      if i < 0 or i >= stack.len:
        raise newException(UsageError, "de Bruijn index out of bounds: " & $i)
      # stack is innermost-first, so index i is stack[i]
      case stack[i].qty
      of q0:
        raise newException(UsageError,
          "erased variable used (index " & $i & ")")
      of q1:
        if stack[i].used:
          raise newException(UsageError,
            "linear variable used more than once (index " & $i & ")")
        stack[i].used = true
      of qOmega:
        discard
    of tLam, tPi:
      # Push binder, check body, verify, pop
      stack.insert(BinderUsage(qty: t.qty, used: false), 0)
      go(t.dom)
      go(t.scope.bdy)
      let b = stack[0]
      if b.qty == q1 and not b.used:
        raise newException(UsageError,
          "linear variable not used (binder " & t.scope.adv & ")")
      stack.delete(0)
    of tSi:
      stack.insert(BinderUsage(qty: t.qty, used: false), 0)
      go(t.dom)
      go(t.scope.bdy)
      # Sigma binders: not linear-checked (they're types, not values)
      stack.delete(0)
    of tApp:
      go(t.fn)
      go(t.arg)
    of tPair:
      go(t.pFst)
      go(t.pSnd)
    of tFst, tSnd:
      go(t.sub)
    of tLet:
      go(t.letVal)
      stack.insert(BinderUsage(qty: qOmega, used: false), 0)
      go(t.letScope.bdy)
      stack.delete(0)
    of tR, tC, tMeta, tInt, tPrim, tAbsurd:
      discard # no binders, no vars
    # Note: tSi handled above; tC is constant

  go(tm)

when isMainModule:
  echo "usage checker module loaded"
