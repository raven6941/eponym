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

type
  UsageError* = object of CatchableError

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

proc countVarUses*(tm: Term): int =
  ## Count free occurrences of de Bruijn index 0 in term positions.
  ## `tm` is the body of a lambda; index 0 denotes the bound variable.
  proc go(t: Term, depth: int): int =
    case t.kind
    of tV:
      if t.idx == depth: 1 else: 0
    of tLam, tPi, tSi:
      # dom is a type annotation: not a term position, skip it
      go(t.scope.bdy, depth + 1)
    of tApp:
      go(t.fn, depth) + go(t.arg, depth)
    of tPair:
      go(t.pFst, depth) + go(t.pSnd, depth) + go(t.pScope.bdy, depth + 1)
    of tFst, tSnd, tAbsurd:
      go(t.sub, depth)
    of tLet:
      # letTy is a type annotation: skip; val and body are term positions
      go(t.letVal, depth) + go(t.letScope.bdy, depth + 1)
    of tPrim:
      0  # primTy is a type annotation; primOp carries no terms
    of tR, tC, tType, tMeta, tInt, tNatLit, tNatSing:
      0
  go(tm, 0)

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
        let n = countVarUses(t.scope.bdy)
        case t.qty
        of q1:
          if n == 0:
            raise newException(UsageError,
              "linear variable '" & t.scope.adv &
              "' not used (expected exactly once): a linear binder must be " &
              "used exactly once in the body")
          elif n > 1:
            raise newException(UsageError,
              "linear variable '" & t.scope.adv & "' used " & $n &
              " times (expected exactly once): use the variable exactly " &
              "once in the body")
        of q0:
          if n > 0:
            raise newException(UsageError,
              "erased variable '" & t.scope.adv &
              "' used in term position: erased (quantity-0) variables may " &
              "only be used in types")
        of qOmega: discard

      proc go(t: Term) =
        case t.kind
        of tV, tR, tC, tType, tMeta, tInt, tNatLit, tNatSing:
          discard # no binders
        of tLam, tPi:
          verifyBinder(t)
          go(t.dom)         # domains may nest binders; uses inside them are
          go(t.scope.bdy)   # type positions, not counted against this binder
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
