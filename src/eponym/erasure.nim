## Core QTT erasure (Issue #328).
##
## This first runtime pass removes the *computation supplied* to q0
## applications while preserving the binder/application shape expected by
## the existing interpreter and host-call ABI. The checked q0 binder cannot
## inspect its argument in computational position, so a canonical unit
## witness is observationally equivalent there. A later backend can lower
## that preserved shape to an ABI with the q0 binder removed entirely.

import std/[sequtils, tables]
import eponym_init
import preterm # Quantity
import usage_check

proc eraseQ0Arguments*(tm: Term): Term =
  ## Erase checked, closed core terms. This operation is intended after
  ## elaboration/zonking and quantity checking. It preserves runtime binder
  ## arity, but replaces every q0 application argument with unit, so the
  ## supplied computation (including proof construction) is not evaluated.
  ##
  ## The traversal opens binders with fresh neutrals to recover the checked
  ## function type at applications. It fails loudly if the core term is not
  ## sufficiently typed for that recovery.
  checkUsage(tm)
  var supply = Supply()
  let bindings = initTable[int, Value]()

  proc walk(t: Term, env: seq[Value]): Term =
    case t.kind
    of tV, tR, tC, tType, tInt, tPrim, tNatLit, tNatSing:
      t
    of tMeta:
      raise newException(ValueError,
        "cannot erase a term with unresolved metavariable ?m" & $t.metaId)
    of tLam, tPi, tSi:
      let dom = walk(t.dom, env)
      let domTy = evalWithBindings(t.dom, env, bindings)
      let x = freshPara(supply, domTy)
      mkBinder(t.kind, dom,
        Scope(adv: t.scope.adv, bdy: walk(t.scope.bdy, @[x] & env)),
        t.impl, t.qty, t.peg)
    of tApp:
      let f = walk(t.fn, env)
      let closedFn = substSpine(t.fn, env.mapIt(it.syn))
      let fnTy = infer(supply, closedFn)
      if fnTy.whnf.kind != wPi:
        raise newException(ValueError,
          "cannot erase application whose checked function type is not Pi")
      let arg = if fnTy.whnfPiQty == q0: tmC(cVoid) else: walk(t.arg, env)
      tmApp(f, arg)
    of tPair:
      let a = walk(t.pFst, env)
      let b = walk(t.pSnd, env)
      # pScope is the pair's type annotation, not a runtime component.
      tmPair(a, b, t.pScope.adv, t.pScope.bdy)
    of tFst: tmFst(walk(t.sub, env))
    of tSnd: tmSnd(walk(t.sub, env))
    of tAbsurd: tmAbsurd(walk(t.sub, env))
    of tLet:
      let value = walk(t.letVal, env)
      let x = evalWithBindings(value, env, bindings)
      tmLet(value, t.letTy, t.letScope.adv,
        walk(t.letScope.bdy, @[x] & env))

  walk(tm, @[])
