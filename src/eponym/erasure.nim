## Core QTT erasure (Issue #328).
##
## This first runtime pass removes the *computation supplied* to q0
## applications while preserving the binder/application shape expected by
## the existing interpreter and host-call ABI. The checked q0 binder cannot
## inspect its argument in computational position, so a canonical unit
## witness is observationally equivalent there. A later backend can lower
## that preserved shape to an ABI with the q0 binder removed entirely.

import std/[sequtils, tables, sets]
import eponym_init
import preterm # Quantity
import usage_check

proc reserveTermRefIds(supply: var Supply, term: Term,
                       seenRefs: var Table[int, bool]) =
  ## Keep inference-local neutral parameters above every global/reference ID
  ## carried by the checked syntax. Otherwise opening a binder can give a
  ## local neutral the same identity as a constructor in an eliminator rule;
  ## `fireRed` can then mistake the neutral for that constructor.
  if term.isNil: return
  case term.kind
  of tR:
    reserveFreshIdsThrough(supply, term.refId)
    if term.refId in seenRefs: return
    seenRefs[term.refId] = true
    if not term.refTyp.isNil:
      reserveTermRefIds(supply, term.refTyp.syn, seenRefs)
    if not term.refVal.isNil:
      reserveTermRefIds(supply, term.refVal.syn, seenRefs)
      if term.refVal.whnfKind == wRed:
        let info = redRuleInfo(term)
        for ctorId, ruleTerm in info.cases:
          reserveFreshIdsThrough(supply, ctorId)
          reserveTermRefIds(supply, ruleTerm, seenRefs)
  of tPi, tSi, tLam:
    reserveTermRefIds(supply, term.dom, seenRefs)
    reserveTermRefIds(supply, term.scope.bdy, seenRefs)
  of tPair:
    reserveTermRefIds(supply, term.pFst, seenRefs)
    reserveTermRefIds(supply, term.pSnd, seenRefs)
    reserveTermRefIds(supply, term.pScope.bdy, seenRefs)
  of tApp:
    reserveTermRefIds(supply, term.fn, seenRefs)
    reserveTermRefIds(supply, term.arg, seenRefs)
  of tFst, tSnd, tAbsurd:
    reserveTermRefIds(supply, term.sub, seenRefs)
  of tLet:
    reserveTermRefIds(supply, term.letVal, seenRefs)
    reserveTermRefIds(supply, term.letTy, seenRefs)
    reserveTermRefIds(supply, term.letScope.bdy, seenRefs)
  of tMeta:
    for arg in term.metaSpine:
      reserveTermRefIds(supply, arg, seenRefs)
  of tPrim:
    reserveTermRefIds(supply, term.primTy, seenRefs)
  of tV, tC, tInt, tNatLit, tNatSing, tType:
    discard

proc eraseQ0ArgumentsPreserving*(tm: Term,
                                preserveQ0Apps: HashSet[int]): Term =
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
  var seenRefs = initTable[int, bool]()
  reserveTermRefIds(supply, tm, seenRefs)
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
      var head = t.fn
      while head.kind == tApp: head = head.fn
      let headRefId = if head.kind == tR: head.refId else: -1
      let preserveTypeArgument = fnTy.whnfPiQty == q0 and
        headRefId in preserveQ0Apps
      let arg = if fnTy.whnfPiQty == q0 and not preserveTypeArgument:
        tmC(cVoid)
      else:
        walk(t.arg, env)
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

proc eraseQ0Arguments*(tm: Term): Term =
  eraseQ0ArgumentsPreserving(tm, initHashSet[int]())
