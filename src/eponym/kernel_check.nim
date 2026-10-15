#===============================================================================
# kernel_check.nim -- Independent minimal kernel checker (Issue #62, v2: #156).
#
# Value category: (d) improved certainty about "proved"/certified conclusions.
#
# LCF-style: a small, deliberately independent implementation of the core
# typing judgments re-checks every elaborated core term. The direct
# elaborator (elab.nim) and the finally-tagless core (eponym.nim) are the
# untrusted producers; this kernel is the auditor.
#
# Design (see decisions.org entries for #62 and #156):
# - SHARED: the Term syntax (eponym_init.Term) -- it is the artifact being
#   audited, so the kernel must read the same representation. The cached
#   Value fields (refTyp, refVal) inside tR nodes are treated as UNTRUSTED
#   hints and never consulted; only the kernel's own tables below are used.
# - INDEPENDENT: everything else is re-implemented from scratch --
#   capture-avoiding substitution, a fresh weak-head evaluator (no NbE,
#   no Values, no RedRule registry), type-directed conversion with eta,
#   and the bidirectional check/infer rules. No import of eponym.nim or
#   elab.nim checking code.
# - DATA, NOT LOGIC: the harness hands the kernel elaborator-produced
#   *data* -- definition bodies, iota rule tables (contractum templates),
#   and the refIds of zero/suc/Int -- exactly as it already hands over
#   definition bodies. The kernel's *judgments* about that data are fresh:
#   iota is re-implemented (kwhnfElim), and every iota rule is validated
#   against the motive derived from the eliminator's own Pi type
#   (validateElimRules) -- the check elabRedDecl skips ("the rule is
#   trusted, like an axiom").
#
# Fragment status (v2): the pure ETT fragment plus --
#   eliminator iota (independently re-implemented + motive-validated),
#   tNatLit (kernel's own suc^n(zero) expansion, Issue #93),
#   tInt/tPrim (kernel axiom: primops are binary Int operations, Exp 11).
# NOT covered: metavariables (tMeta raises -- the zonk invariant must hold
# before kernel checking).
# A term outside the fragment raises KernelError("out of kernel fragment"),
# never a silent pass: absence of a rule is a failure, not an acceptance.
#===============================================================================

import tables
import strutils
import preterm       # Quantity (q0/q1/qOmega) for binder construction
import eponym_init  # Term syntax only; none of its judgments or Values

type
  KernelError* = object of CatchableError

  KGEntry* = object
    ## A global known to the kernel. `ty` is the declared type (syntax);
    ## `def` is the definition body (nil for postulates and constructors,
    ## which the kernel treats as neutrals). `isElim`/`elimNargs` mark
    ## data eliminators (from `elim` declarations).
    ty*: Term
    def*: Term
    isElim*: bool
    elimNargs*: int

  KElimCase* = object
    ## One iota rule: the contractum template Term (elaborator-produced
    ## data, in the context [elim args except scrutinee, ctor tele args],
    ## innermost-first) plus whether it passed the kernel's independent
    ## motive check. A rule that fails validation with a *fragment* error
    ## is marked invalid (not auditable: iota use raises a fragment error,
    ## so dependent definitions SKIP honestly); a rule that fails with a
    ## genuine error is an audit disagreement and aborts validation.
    tmpl*: Term
    valid*: bool

  KElimRuleSet* = object
    nParams*: int   ## leading ctor-spine args that are elim params, not tele vars
    cases*: Table[int, KElimCase]  ## constructor refId -> rule

  KernelGlobals* = object
    entries*: Table[int, KGEntry]
    elimRules*: Table[int, KElimRuleSet]  ## eliminator refId -> rule set
    natZeroId*: int  ## refId of the Nat `zero` constructor, -1 if unknown
    natSucId*: int   ## refId of the Nat `suc` constructor, -1 if unknown
    natTypeId*: int  ## refId of the Nat datatype itself, -1 if unknown
                     ## (Issue #74: singleton base rule tNatSing(k) <: Nat)
    intId*: int      ## refId of the `Int` postulate, -1 if unknown

proc initKernelGlobals*(): KernelGlobals =
  KernelGlobals(entries: initTable[int, KGEntry](),
                elimRules: initTable[int, KElimRuleSet](),
                natZeroId: -1, natSucId: -1, natTypeId: -1, intId: -1)

proc kerr(msg: string): ref KernelError =
  newException(KernelError, msg)

proc isFragmentViolation*(e: ref KernelError): bool =
  # All fragment-exclusion errors share the "out of kernel fragment" prefix
  # (tMeta, unregistered zero/suc/Int, unvalidatable iota rules); everything
  # else is a genuine rejection by the kernel.
  e.msg.startsWith("out of kernel fragment")

proc kref(id: int): Term =
  ## A kernel-built global reference (cached Value fields left nil:
  ## the kernel never consults them).
  Term(kind: tR, refId: id, refTyp: nil, refIsDefn: false, refVal: nil)

proc kv(idx: int): Term =
  Term(kind: tV, idx: idx)

# --- de Bruijn plumbing (fresh implementation) -------------------------------

proc kshift(tm: Term, cutoff, amt: int): Term =
  ## Shift free indices >= cutoff by amt.
  case tm.kind
  of tV:
    if tm.idx >= cutoff: Term(kind: tV, idx: tm.idx + amt)
    else: tm
  of tR, tC, tInt, tNatLit, tNatSing:
    tm
  of tMeta:
    raise kerr("out of kernel fragment: tMeta in kernel term (zonk invariant violated)")
  of tPi:
    Term(kind: tPi, dom: kshift(tm.dom, cutoff, amt),
         scope: Scope(adv: tm.scope.adv, bdy: kshift(tm.scope.bdy, cutoff+1, amt)),
         impl: tm.impl, erased: tm.erased, qty: tm.qty)
  of tSi:
    Term(kind: tSi, dom: kshift(tm.dom, cutoff, amt),
         scope: Scope(adv: tm.scope.adv, bdy: kshift(tm.scope.bdy, cutoff+1, amt)),
         impl: tm.impl, erased: tm.erased, qty: tm.qty)
  of tLam:
    Term(kind: tLam, dom: kshift(tm.dom, cutoff, amt),
         scope: Scope(adv: tm.scope.adv, bdy: kshift(tm.scope.bdy, cutoff+1, amt)),
         impl: tm.impl, erased: tm.erased, qty: tm.qty)
  of tPair:
    Term(kind: tPair, pFst: kshift(tm.pFst, cutoff, amt),
         pSnd: kshift(tm.pSnd, cutoff, amt),
         pScope: Scope(adv: tm.pScope.adv, bdy: kshift(tm.pScope.bdy, cutoff+1, amt)))
  of tApp:
    Term(kind: tApp, fn: kshift(tm.fn, cutoff, amt), arg: kshift(tm.arg, cutoff, amt))
  of tFst:
    Term(kind: tFst, sub: kshift(tm.sub, cutoff, amt))
  of tSnd:
    Term(kind: tSnd, sub: kshift(tm.sub, cutoff, amt))
  of tAbsurd:
    Term(kind: tAbsurd, sub: kshift(tm.sub, cutoff, amt))
  of tLet:
    Term(kind: tLet, letVal: kshift(tm.letVal, cutoff, amt),
         letTy: kshift(tm.letTy, cutoff, amt),
         letScope: Scope(adv: tm.letScope.adv, bdy: kshift(tm.letScope.bdy, cutoff+1, amt)))
  of tPrim:
    Term(kind: tPrim, primOp: tm.primOp, primTy: kshift(tm.primTy, cutoff, amt))

proc ksubst(tm: Term, s: Term, cutoff: int, shrink: static bool = true): Term =
  ## Substitute `s` (already shifted for depth `cutoff`) for index `cutoff`.
  ## With shrink=true (beta-like), indices above `cutoff` are decremented:
  ## the result lives one binder shallower. With shrink=false the depth is
  ## unchanged (check-mode lambda/pair/snd: the context the body is checked
  ## in has the same outer binders at the same indices).
  case tm.kind
  of tV:
    if tm.idx == cutoff: s
    elif tm.idx > cutoff:
      when shrink: Term(kind: tV, idx: tm.idx - 1)
      else: tm
    else: tm
  of tR, tC, tInt, tNatLit, tNatSing:
    tm
  of tMeta:
    raise kerr("out of kernel fragment: tMeta in kernel term (zonk invariant violated)")
  of tPi:
    Term(kind: tPi, dom: ksubst(tm.dom, s, cutoff, shrink),
         scope: Scope(adv: tm.scope.adv,
                      bdy: ksubst(tm.scope.bdy, kshift(s, 0, 1), cutoff+1, shrink)),
         impl: tm.impl, erased: tm.erased, qty: tm.qty)
  of tSi:
    Term(kind: tSi, dom: ksubst(tm.dom, s, cutoff, shrink),
         scope: Scope(adv: tm.scope.adv,
                      bdy: ksubst(tm.scope.bdy, kshift(s, 0, 1), cutoff+1, shrink)),
         impl: tm.impl, erased: tm.erased, qty: tm.qty)
  of tLam:
    Term(kind: tLam, dom: ksubst(tm.dom, s, cutoff, shrink),
         scope: Scope(adv: tm.scope.adv,
                      bdy: ksubst(tm.scope.bdy, kshift(s, 0, 1), cutoff+1, shrink)),
         impl: tm.impl, erased: tm.erased, qty: tm.qty)
  of tPair:
    Term(kind: tPair, pFst: ksubst(tm.pFst, s, cutoff, shrink),
         pSnd: ksubst(tm.pSnd, s, cutoff),
         pScope: Scope(adv: tm.pScope.adv,
                       bdy: ksubst(tm.pScope.bdy, kshift(s, 0, 1), cutoff+1, shrink)))
  of tApp:
    Term(kind: tApp, fn: ksubst(tm.fn, s, cutoff, shrink), arg: ksubst(tm.arg, s, cutoff, shrink))
  of tFst:
    Term(kind: tFst, sub: ksubst(tm.sub, s, cutoff, shrink))
  of tSnd:
    Term(kind: tSnd, sub: ksubst(tm.sub, s, cutoff, shrink))
  of tAbsurd:
    Term(kind: tAbsurd, sub: ksubst(tm.sub, s, cutoff, shrink))
  of tLet:
    Term(kind: tLet, letVal: ksubst(tm.letVal, s, cutoff, shrink),
         letTy: ksubst(tm.letTy, s, cutoff, shrink),
         letScope: Scope(adv: tm.letScope.adv,
                         bdy: ksubst(tm.letScope.bdy, kshift(s, 0, 1), cutoff+1, shrink)))
  of tPrim:
    Term(kind: tPrim, primOp: tm.primOp,
         primTy: ksubst(tm.primTy, s, cutoff, shrink))

proc kinst(bdy: Term, arg: Term): Term =
  ## Instantiate the body of a scope with `arg` (index 0); the result lives
  ## one binder shallower (beta-like).
  ksubst(bdy, arg, 0)

proc ksubstKeep(bdy: Term, s: Term): Term =
  ## Substitute `s` for index 0 without changing the depth: outer binders
  ## keep their indices. For check-mode lambda only, where the context the
  ## body is checked in gains an entry for the bound variable at the same
  ## depth the codomain was written. Pair components and snd-projection
  ## eliminate the sigma binder with no replacement, so they use the
  ## beta-like `kinst` instead (regression test below: dependent pairSwap).
  ksubst(bdy, s, 0, shrink = false)

proc ksubstSpine(tm: Term, reps: seq[Term]): Term =
  ## Parallel substitution: reps[j] replaces de Bruijn index j; every
  ## replacement lives in the target (shallower) context. Binders are
  ## eliminated outside-in so earlier substitutions never disturb the
  ## indices of later ones.
  result = tm
  for j in countdown(reps.high, 0):
    result = ksubst(result, kshift(reps[j], 0, j), j, shrink = true)

proc ksynEq(a, b: Term): bool =
  ## Syntactic (non-reducing) term equality, for the iota rule's
  ## param-matching check during validation.
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of tV: a.idx == b.idx
  of tR: a.refId == b.refId
  of tC: a.c == b.c
  of tInt: a.intVal == b.intVal
  of tNatLit: a.natLitVal == b.natLitVal
  of tNatSing: a.natSingVal == b.natSingVal
  of tPrim: a.primOp == b.primOp
  of tPi, tSi, tLam:
    ksynEq(a.dom, b.dom) and ksynEq(a.scope.bdy, b.scope.bdy)
  of tPair:
    ksynEq(a.pFst, b.pFst) and ksynEq(a.pSnd, b.pSnd) and
      ksynEq(a.pScope.bdy, b.pScope.bdy)
  of tApp: ksynEq(a.fn, b.fn) and ksynEq(a.arg, b.arg)
  of tFst, tSnd, tAbsurd: ksynEq(a.sub, b.sub)
  of tLet:
    ksynEq(a.letVal, b.letVal) and ksynEq(a.letTy, b.letTy) and
      ksynEq(a.letScope.bdy, b.letScope.bdy)
  of tMeta: a.metaId == b.metaId

proc splitSpine(t: Term): tuple[head: Term, args: seq[Term]] =
  ## Flatten an application spine: head-first, args in function order.
  var h = t
  var rev: seq[Term] = @[]
  while h.kind == tApp:
    rev.add(h.arg)
    h = h.fn
  var args: seq[Term] = @[]
  for i in countdown(rev.high, 0): args.add(rev[i])
  (h, args)

proc rebuildSpine(head: Term, args: seq[Term]): Term =
  result = head
  for a in args: result = Term(kind: tApp, fn: result, arg: a)

# --- weak-head evaluation (fresh; beta + delta + pair/let + iota + primops) --

proc kwhnf(tm: Term, g: KernelGlobals, depth: int = 0): Term
  ## forward declaration (mutual recursion with kwhnfElim/kwhnfPrim)

proc kExpandNatLit(n: int, g: KernelGlobals): Term =
  ## Issue #93: the kernel's own literal expansion. tNatLit(n) is
  ## definitionally suc^n(zero), built from the kernel's own globals --
  ## the same semantics as the elaborator's expandNatLit, re-implemented.
  result = kref(g.natZeroId)
  for _ in 1 .. n:
    result = Term(kind: tApp, fn: kref(g.natSucId), arg: result)

proc kwhnfElim(fh: Term, args: seq[Term], g: KernelGlobals,
               depth: int): tuple[res: Term, fired: bool] =
  ## Issue #156: the kernel's own iota. `args` is the function-order spine
  ## of an application headed by the eliminator `fh`. Returns (whnf, fired):
  ## when a rule fires the result is the instantiated template (the caller
  ## continues reducing); otherwise the result is already a neutral spine.
  let e = g.entries[fh.refId]
  if args.len < e.elimNargs:
    return (rebuildSpine(fh, args), false)  # under-applied: neutral
  let n = e.elimNargs
  let scrut = kwhnf(args[n-1], g, depth+1)
  let (sh, sargs) = splitSpine(scrut)
  var acc: Term
  var fired = false
  if sh.kind == tR and g.elimRules.hasKey(fh.refId) and
      g.elimRules[fh.refId].cases.hasKey(sh.refId):
    let cs = g.elimRules[fh.refId].cases[sh.refId]
    if not cs.valid:
      raise kerr("out of kernel fragment: iota rule for eliminator " &
        $fh.refId & " on constructor " & $sh.refId & " did not validate")
    let nParams = g.elimRules[fh.refId].nParams
    if sargs.len < nParams:
      raise kerr("out of kernel fragment: iota scrutinee spine shorter than nParams")
    # The template's context is innermost-first:
    # [ctor tele args (m), elim args except scrutinee (nargs-1)].
    var reps: seq[Term] = @[]
    for i in countdown(sargs.high, nParams): reps.add(sargs[i])
    for i in countdown(n - 2, 0): reps.add(args[i])
    acc = ksubstSpine(cs.tmpl, reps)
    fired = true
  else:
    # Stuck on a neutral (or unknown) scrutinee: neutral, mirroring the
    # elaborator's fireRed neutral case. The scrutinee is kept whnf'd;
    # the remaining args are untouched (as in the v1 neutral case).
    acc = rebuildSpine(fh, args[0 ..< n-1] & @[scrut])
  for i in n ..< args.len:
    if fired:
      acc = kwhnf(Term(kind: tApp, fn: acc, arg: args[i]), g, depth+1)
    else:
      acc = Term(kind: tApp, fn: acc, arg: args[i])
  (acc, fired)

proc kwhnfPrim(fh: Term, args: seq[Term], g: KernelGlobals,
               depth: int): tuple[res: Term, fired: bool] =
  ## Issue #156 / Experiment 11: the kernel's own primop semantics.
  ## A fully-applied primop fires on literal args (host arithmetic);
  ## otherwise (or under-applied) it stays neutral.
  if args.len < 2:
    return (rebuildSpine(fh, args), false)
  let a0 = kwhnf(args[0], g, depth+1)
  let a1 = kwhnf(args[1], g, depth+1)
  if a0.kind == tInt and a1.kind == tInt:
    let r = case fh.primOp
      of opAdd: a0.intVal + a1.intVal
      of opSub: a0.intVal - a1.intVal
      of opMul: a0.intVal * a1.intVal
    var acc = Term(kind: tInt, intVal: r)
    for i in 2 ..< args.len:  # over-applied: ill-typed, but stay total
      acc = kwhnf(Term(kind: tApp, fn: acc, arg: args[i]), g, depth+1)
    (acc, true)
  else:
    var acc = rebuildSpine(fh, @[a0, a1])
    for i in 2 ..< args.len:
      acc = Term(kind: tApp, fn: acc, arg: args[i])
    (acc, false)

proc kwhnf(tm: Term, g: KernelGlobals, depth: int = 0): Term =
  if depth > 500: raise kerr("kernel whnf depth exceeded (cyclic definition?)")
  var t = tm
  var fuel = 4_000_000  # insurance against a diverging rule; issue #36 keeps
                        # elaborator-accepted rules structurally recursive
  while true:
    dec fuel
    if fuel <= 0:
      raise kerr("out of kernel fragment: reduction did not terminate")
    case t.kind
    of tApp:
      let (hh, hargs) = splitSpine(t)
      let fh = kwhnf(hh, g, depth+1)
      if fh.kind == tLam:
        var acc = kinst(fh.scope.bdy, hargs[0])
        for i in 1 ..< hargs.len:
          acc = Term(kind: tApp, fn: acc, arg: hargs[i])
        t = acc
      elif fh.kind == tR and g.entries.hasKey(fh.refId) and
          g.entries[fh.refId].isElim:
        let (res, fired) = kwhnfElim(fh, hargs, g, depth)
        if fired: t = res
        else: return res
      elif fh.kind == tPrim:
        let (res, fired) = kwhnfPrim(fh, hargs, g, depth)
        if fired: t = res
        else: return res
      else:
        var acc = fh
        for a in hargs: acc = Term(kind: tApp, fn: acc, arg: a)
        return acc
    of tR:
      if g.entries.hasKey(t.refId):
        let e = g.entries[t.refId]
        if e.def != nil:
          t = e.def
        else:
          return t
      else:
        return t
    of tFst:
      let s = kwhnf(t.sub, g, depth+1)
      if s.kind == tPair: t = s.pFst
      else: return Term(kind: tFst, sub: s)
    of tSnd:
      let s = kwhnf(t.sub, g, depth+1)
      if s.kind == tPair: t = ksubstKeep(s.pScope.bdy, s.pFst)
      else: return Term(kind: tSnd, sub: s)
    of tLet:
      t = kinst(t.letScope.bdy, t.letVal)
    of tMeta:
      raise kerr("out of kernel fragment: tMeta in kernel term (zonk invariant violated)")
    of tInt:
      return t
    of tNatLit:
      # Issue #93: definitionally suc^n(zero); expand with the kernel's
      # own constructors (independently of the elaborator's expandNatLit).
      if g.natZeroId < 0 or g.natSucId < 0 or
          not g.entries.hasKey(g.natZeroId) or not g.entries.hasKey(g.natSucId):
        raise kerr("out of kernel fragment: tNatLit literal " &
          "(no Nat constructors registered)")
      t = kExpandNatLit(t.natLitVal, g)
    of tPrim:
      return t
    else:
      return t

# --- conversion (type-directed, eta for functions) ---------------------------

proc kconv(a, b: Term, g: KernelGlobals, depth: int = 0): bool =
  if depth > 200: raise kerr("conversion depth exceeded")
  let wa = kwhnf(a, g)
  let wb = kwhnf(b, g)
  if wa.kind == tLam and wb.kind != tLam:
    # eta: lam x. b =?= n  <=>  b =?= n x, with n shifted under the binder
    return kconv(wa.scope.bdy,
                 Term(kind: tApp, fn: kshift(wb, 0, 1),
                      arg: Term(kind: tV, idx: 0)), g, depth+1)
  if wb.kind == tLam and wa.kind != tLam:
    return kconv(Term(kind: tApp, fn: kshift(wa, 0, 1),
                      arg: Term(kind: tV, idx: 0)),
                 wb.scope.bdy, g, depth+1)
  if wa.kind != wb.kind: return false
  case wa.kind
  of tV: return wa.idx == wb.idx
  of tC: return wa.c == wb.c
  of tR: return wa.refId == wb.refId
  of tInt: return wa.intVal == wb.intVal
  of tNatSing: return wa.natSingVal == wb.natSingVal  # Issue #74
  of tPrim:
    # primTy is validated at infer time against the kernel's axiom;
    # compare it too, defensively (nil-safe: the elaborator always sets it).
    wa.primOp == wb.primOp and
      (wa.primTy.isNil or wb.primTy.isNil or
        kconv(wa.primTy, wb.primTy, g, depth+1))
  of tPi, tSi:
    # domains and codomains under the same binder compare directly
    kconv(wa.dom, wb.dom, g, depth+1) and
      kconv(wa.scope.bdy, wb.scope.bdy, g, depth+1)
  of tLam:
    kconv(wa.scope.bdy, wb.scope.bdy, g, depth+1)
  of tPair:
    kconv(wa.pFst, wb.pFst, g, depth+1) and
      kconv(wa.pScope.bdy, wb.pScope.bdy, g, depth+1)
  of tApp:
    kconv(wa.fn, wb.fn, g, depth+1) and kconv(wa.arg, wb.arg, g, depth+1)
  of tFst, tSnd, tAbsurd:
    kconv(wa.sub, wb.sub, g, depth+1)
  of tLet:
    kconv(wa.letVal, wb.letVal, g, depth+1) and
      kconv(wa.letTy, wb.letTy, g, depth+1) and
      kconv(wa.letScope.bdy, wb.letScope.bdy, g, depth+1)
  else:
    raise kerr("conversion: unexpected whnf kind " & $wa.kind)

# --- bidirectional typing ----------------------------------------------------

type KCtx* = seq[Term]  # innermost-first types

proc kInfer(tm: Term, ctx: KCtx, g: KernelGlobals): Term
proc kCheck(tm: Term, ty: Term, ctx: KCtx, g: KernelGlobals)

proc kInfer(tm: Term, ctx: KCtx, g: KernelGlobals): Term =
  let star = Term(kind: tC, c: cStar)
  case tm.kind
  of tV:
    if tm.idx < 0 or tm.idx >= ctx.len:
      raise kerr("unbound de Bruijn index " & $tm.idx)
    kshift(ctx[tm.idx], 0, tm.idx + 1)
  of tR:
    if not g.entries.hasKey(tm.refId):
      raise kerr("unknown global refId " & $tm.refId)
    g.entries[tm.refId].ty
  of tC:
    # ? : ?, 1 : ?, O : ? -- but the unit value <> : 1 (elab: pkUnitV).
    if tm.c == cVoid: Term(kind: tC, c: cOne)
    else: star
  of tPi, tSi:
    kCheck(tm.dom, star, ctx, g)
    kCheck(tm.scope.bdy, star, tm.dom & ctx, g)
    star
  of tApp:
    let fty = kwhnf(kInfer(tm.fn, ctx, g), g)
    if fty.kind != tPi:
      raise kerr("application of non-function")
    kCheck(tm.arg, fty.dom, ctx, g)
    kinst(fty.scope.bdy, tm.arg)
  of tFst:
    let sty = kwhnf(kInfer(tm.sub, ctx, g), g)
    if sty.kind != tSi: raise kerr("fst of non-pair")
    sty.dom
  of tSnd:
    let sty = kwhnf(kInfer(tm.sub, ctx, g), g)
    if sty.kind != tSi: raise kerr("snd of non-pair")
    # The sigma binder is eliminated with no replacement in the context,
    # so outer indices decrement: beta-like kinst, NOT ksubstKeep
    # (ksubstKeep is only for check-mode lambda, where the context gains
    # an entry for the bound variable at the same depth).
    kinst(sty.scope.bdy, Term(kind: tFst, sub: tm.sub))
  of tAbsurd:
    # in infer mode the result type is unknown; kernel requires check mode
    raise kerr("tAbsurd requires check mode (result type unknown)")
  of tLam:
    # Elaborated lambdas always carry their domain annotation (the
    # elaborator fills it even for unannotated surface lambdas, via a
    # zonked metavar), so synthesis is sound: check the domain is a type,
    # infer the body under it, and form the Pi. Needed e.g. after
    # let-substitution exposes a lambda in infer position (05-id-universe).
    kCheck(tm.dom, star, ctx, g)
    let bty = kInfer(tm.scope.bdy, tm.dom & ctx, g)
    Term(kind: tPi, dom: tm.dom, scope: Scope(bdy: bty),
         impl: tm.impl, erased: tm.erased, qty: tm.qty)
  of tPair:
    # Non-dependent synthesis (mirrors the elaborator's cPair limitation:
    # infer gives Sigma(A, _. B) with B independent of the first component).
    # Check mode (kCheck) still handles the dependent case via the expected
    # Sigma type.
    let aTy = kInfer(tm.pFst, ctx, g)
    let bTy = kInfer(tm.pSnd, ctx, g)
    Term(kind: tSi, dom: aTy, scope: Scope(bdy: kshift(bTy, 0, 1)),
         impl: false, erased: false, qty: qOmega)
  of tLet:
    kCheck(tm.letTy, star, ctx, g)
    kCheck(tm.letVal, tm.letTy, ctx, g)
    kInfer(kinst(tm.letScope.bdy, tm.letVal), ctx, g)
  of tMeta:
    raise kerr("out of kernel fragment: tMeta in kernel term (zonk invariant violated)")
  of tInt:
    # Experiment 11: a primitive integer literal has the postulated Int type.
    if g.intId < 0 or not g.entries.hasKey(g.intId):
      raise kerr("out of kernel fragment: tInt literal (no Int registered)")
    kref(g.intId)
  of tPrim:
    # Experiment 11: axiom-style. The kernel *knows* primops are binary
    # Int operations; the elaborator's claimed primTy is verified against
    # the kernel's own axiom type rather than trusted.
    if g.intId < 0 or not g.entries.hasKey(g.intId):
      raise kerr("out of kernel fragment: tPrim (no Int registered)")
    let intTy = kref(g.intId)
    let axiomTy = Term(kind: tPi, dom: intTy,
      scope: Scope(bdy: Term(kind: tPi, dom: kshift(intTy, 0, 1),
        scope: Scope(bdy: kshift(intTy, 0, 2)),
        impl: false, erased: false, qty: qOmega)),
      impl: false, erased: false, qty: qOmega)
    if tm.primTy.isNil or not kconv(tm.primTy, axiomTy, g):
      raise kerr("tPrim type does not match the kernel's primop axiom " &
        "(Int -> Int -> Int)")
    axiomTy
  of tNatLit:
    # Issue #93: definitionally suc^n(zero); infer the expansion's type
    # with the kernel's own constructors.
    if g.natZeroId < 0 or g.natSucId < 0:
      raise kerr("out of kernel fragment: tNatLit literal " &
        "(no Nat constructors registered)")
    kInfer(kExpandNatLit(tm.natLitVal, g), ctx, g)
  of tNatSing:
    # Issue #74: a singleton is a type; its type is ?.
    star

proc ksubsumes(inf, exp: Term, g: KernelGlobals): bool =
  ## Issue #74: audit-kernel twin of eponym_init.subsumes — definitional
  ## subsumption (inf <: exp): singleton base rule, covariant through Pi
  ## codomains and Sigma components, definitional equality elsewhere.
  ## Open codomains are compared under the same de Bruijn convention on
  ## both sides (one binder each), which ksynEq handles structurally.
  let wi = kwhnf(inf, g)
  let we = kwhnf(exp, g)
  if wi.kind == tNatSing:
    if g.natTypeId >= 0 and we.kind == tR and we.refId == g.natTypeId:
      return true
    # else fall through to definitional equality below
  if wi.kind == tPi and we.kind == tPi:
    if not kconv(wi.dom, we.dom, g): return false  # domains invariant
    return ksubsumes(wi.scope.bdy, we.scope.bdy, g)
  if wi.kind == tSi and we.kind == tSi:
    if not kconv(wi.dom, we.dom, g): return false
    return ksubsumes(wi.scope.bdy, we.scope.bdy, g)
  kconv(inf, exp, g)

proc kCheck(tm: Term, ty: Term, ctx: KCtx, g: KernelGlobals) =
  let wty = kwhnf(ty, g)
  case tm.kind
  of tLam:
    if wty.kind != tPi:
      raise kerr("lambda checked against non-Pi")
    kCheck(tm.scope.bdy, ksubstKeep(wty.scope.bdy, Term(kind: tV, idx: 0)),
           wty.dom & ctx, g)
  of tPair:
    if wty.kind != tSi:
      raise kerr("pair checked against non-Sigma")
    kCheck(tm.pFst, wty.dom, ctx, g)
    # Beta-like instantiation: the sigma binder is eliminated, so outer
    # indices decrement (kinst, not ksubstKeep -- cf. the tSnd case above).
    kCheck(tm.pSnd, kinst(wty.scope.bdy, tm.pFst), ctx, g)
  of tAbsurd:
    let sty = kwhnf(kInfer(tm.sub, ctx, g), g)
    if sty.kind != tC or sty.c != cVoid:
      raise kerr("absurd requires a proof of O")
  of tNatLit:
    # Issue #74: a literal checks against a singleton type iff the values
    # match; against any other type it must have the inferred (Nat) type.
    if wty.kind == tNatSing:
      if tm.natLitVal != wty.natSingVal:
        raise kerr("nat literal " & $tm.natLitVal &
          " does not inhabit singleton type " & $wty.natSingVal)
    elif not ksubsumes(kInfer(tm, ctx, g), ty, g):
      raise kerr("type mismatch")
  else:
    let inferred = kInfer(tm, ctx, g)
    if not ksubsumes(inferred, ty, g):
      raise kerr("type mismatch")

# --- iota rule validation: the motive check ----------------------------------
#
# elabRedDecl elaborates each `red` contractum in inference mode only --
# "the rule is trusted, like an axiom". The kernel does not trust it:
# for every (eliminator, constructor) rule it derives the expected type
# from the eliminator's own Pi type (motive/cases/indices discovered from
# the kernel's globals) and checks the template against it.
#
# Template context (innermost-first), for an eliminator with `nargs`
# arguments and a constructor with `nParams` params + `m` tele args:
#   [w_m .. w_1, a_{nargs-1} .. a_1]
# where a_i are the eliminator args (a_nargs is the scrutinee) and w_j the
# constructor tele args. tIdxE/tIdxW compute these de Bruijn indices.

proc tIdxE(nargs, m, a: int): int = m + (nargs - 1 - a)  # elim arg a (1-based)
proc tIdxW(m, w: int): int = m - w                      # tele arg w (1-based)

proc validateOneRule(g: KernelGlobals, elimId, nargs: int, aTys: seq[Term],
                     resTy: Term, nParams, ctorId: int, tmpl: Term) =
  ## Check one contractum template against the motive instance. Raises
  ## non-fragment KernelError when the rule is ill-typed (an audit
  ## disagreement to triage); raises fragment KernelError when the rule's
  ## shape cannot be discovered (not auditable -> SKIP).
  if not g.entries.hasKey(ctorId):
    raise kerr("iota validation: unknown constructor refId " & $ctorId)
  var cDoms: seq[Term] = @[]
  var ccur = g.entries[ctorId].ty
  while ccur.kind == tPi:
    cDoms.add(ccur.dom)
    ccur = ccur.scope.bdy
  let cRes = ccur
  if cDoms.len < nParams:
    raise kerr("out of kernel fragment: iota rule has more params " &
      "than the constructor takes")
  let m = cDoms.len - nParams
  # Template context types, innermost-first: [T_m .. T_1, A'_{nargs-1} .. A'_1].
  # Each is first built in the full template context, then shifted down by
  # (i+1): the kernel's KCtx convention needs ctx[i] written outside the i
  # innermost binders (kInfer(V(i)) shifts it back up by i+1).
  var ctxTysFull: seq[Term] = @[]
  for j in countdown(m, 1):
    var reps: seq[Term] = @[]
    for l in 0 ..< nParams + j - 1:
      let d = nParams + j - 1 - l  # index l <-> d_d (1-based)
      reps.add(if d <= nParams: kv(tIdxE(nargs, m, d))
               else: kv(tIdxW(m, d - nParams)))
    ctxTysFull.add(ksubstSpine(cDoms[nParams + j - 1], reps))
  for i in countdown(nargs - 1, 1):
    var reps: seq[Term] = @[]
    for l in 0 ..< i - 1:
      reps.add(kv(tIdxE(nargs, m, i - 1 - l)))  # index l <-> a_{i-1-l}
    ctxTysFull.add(ksubstSpine(aTys[i - 1], reps))
  var ctxTys: seq[Term] = @[]
  for i in 0 ..< ctxTysFull.len:
    ctxTys.add(kshift(ctxTysFull[i], 0, -(i + 1)))
  # Index discovery: the scrutinee type A_nargs is the family applied to
  # (params.., index vars..); the constructor's return type is the family
  # applied to (params.., index exprs..). The leading params must match
  # syntactically; each trailing index var maps to its index expression.
  var repsA: seq[Term] = @[]
  for l in 0 ..< nargs - 1:
    repsA.add(kv(tIdxE(nargs, m, nargs - 1 - l)))
  let (famH, sArgs) = splitSpine(kwhnf(ksubstSpine(aTys[nargs - 1], repsA), g))
  var repsC: seq[Term] = @[]
  for l in 0 ..< cDoms.len:
    let d = cDoms.len - l  # index l <-> d_d
    repsC.add(if d <= nParams: kv(tIdxE(nargs, m, d))
              else: kv(tIdxW(m, d - nParams)))
  let (famH2, rArgs) = splitSpine(kwhnf(ksubstSpine(cRes, repsC), g))
  var indexSubst = initTable[int, Term]()  # elim arg position -> index expr
  if famH.kind == tR and famH2.kind == tR and famH.refId == famH2.refId:
    if sArgs.len != rArgs.len:
      raise kerr("out of kernel fragment: iota rule family spine length mismatch")
    if sArgs.len < nParams:
      raise kerr("out of kernel fragment: iota rule has fewer family " &
        "arguments than params")
    for p in 1 .. nParams:
      if not ksynEq(sArgs[p-1], kv(tIdxE(nargs, m, p))):
        raise kerr("out of kernel fragment: iota rule param mismatch")
    for j in nParams + 1 .. sArgs.len:
      let sa = sArgs[j-1]
      if sa.kind != tV or sa.idx < m or sa.idx > m + nargs - 2:
        raise kerr("out of kernel fragment: cannot discover index " &
          "structure of iota rule")
      indexSubst[m + nargs - 1 - sa.idx] = rArgs[j-1]  # invert tIdxE
  elif famH.kind == tV:
    discard  # motive-headed eliminator (hand-written `elim`): no indices
  else:
    raise kerr("out of kernel fragment: iota rule scrutinee type has " &
      "an unexpected head")
  # Expected type: resTy with the scrutinee replaced by the constructor
  # spine and each index var replaced by its index expression.
  var scrutArgs: seq[Term] = @[]
  for p in 1 .. nParams: scrutArgs.add(kv(tIdxE(nargs, m, p)))
  for w in 1 .. m: scrutArgs.add(kv(tIdxW(m, w)))
  var repsB: seq[Term] = @[rebuildSpine(kref(ctorId), scrutArgs)]
  for l in 1 ..< nargs:  # index l <-> a_{nargs-l}
    let a = nargs - l
    repsB.add(if indexSubst.hasKey(a): indexSubst[a]
              else: kv(tIdxE(nargs, m, a)))
  let expectedTy = ksubstSpine(resTy, repsB)
  try:
    kCheck(tmpl, expectedTy, ctxTys, g)
  except KernelError as err:
    if isFragmentViolation(err): raise err
    raise kerr("iota rule for eliminator " & $elimId & " on constructor " &
      $ctorId & " ill-typed against the motive: " & err.msg)

proc validateElimRules*(g: var KernelGlobals) =
  ## Issue #156: validate every iota rule against its motive before the
  ## audit uses it. Rules failing with a fragment error are marked invalid
  ## (their use raises a fragment error -> honest SKIP); genuine failures
  ## propagate as audit disagreements.
  var elimIds: seq[int] = @[]
  for k in g.elimRules.keys: elimIds.add(k)
  for elimId in elimIds:
    if not g.entries.hasKey(elimId):
      raise kerr("iota validation: unknown eliminator refId " & $elimId)
    let e = g.entries[elimId]
    var aTys: seq[Term] = @[]
    var cur = e.ty
    while cur.kind == tPi:
      aTys.add(cur.dom)
      cur = cur.scope.bdy
    if aTys.len != e.elimNargs:
      raise kerr("iota validation: eliminator " & $elimId &
        " type is not a Pi spine of length " & $e.elimNargs)
    let resTy = cur
    var rules = g.elimRules[elimId]
    var ctorIds: seq[int] = @[]
    for k in rules.cases.keys: ctorIds.add(k)
    for ctorId in ctorIds:
      try:
        validateOneRule(g, elimId, e.elimNargs, aTys, resTy,
                        rules.nParams, ctorId, rules.cases[ctorId].tmpl)
        rules.cases[ctorId].valid = true
      except KernelError as err:
        if isFragmentViolation(err):
          rules.cases[ctorId].valid = false
        else:
          raise err
    g.elimRules[elimId] = rules

# --- public API --------------------------------------------------------------

proc kernelCheck*(tm: Term, ty: Term, g: KernelGlobals): bool =
  ## Returns true iff `tm` checks against `ty` in the kernel.
  ## Ill-typed input returns false. Fragment violations (tMeta,
  ## unregistered zero/suc/Int, unvalidatable iota rules) are re-raised so
  ## callers can distinguish "not yet auditable" from "rejected".
  try:
    kCheck(tm, ty, @[], g)
    true
  except KernelError as e:
    if isFragmentViolation(e): raise e
    false

proc kernelCheckDef*(name: string, tm, ty: Term, g: KernelGlobals): bool =
  ## Audit one elaborated definition: the type must itself be well-formed
  ## (?-inhabited) and the term must check against it.
  try:
    kCheck(ty, Term(kind: tC, c: cStar), @[], g)
  except KernelError as e:
    if isFragmentViolation(e): raise e
    return false
  kernelCheck(tm, ty, g)

when isMainModule:
  # --- self-tests: the kernel audits hand-built core terms ------------------
  let star = Term(kind: tC, c: cStar)
  proc pi(dom, cod: Term): Term =
    Term(kind: tPi, dom: dom, scope: Scope(bdy: cod),
         impl: false, erased: false, qty: qOmega)
  proc lam(bdy: Term): Term =
    Term(kind: tLam, dom: star, scope: Scope(bdy: bdy),
         impl: false, erased: false, qty: qOmega)
  proc app(f, a: Term): Term = Term(kind: tApp, fn: f, arg: a)
  proc vv(i: int): Term = Term(kind: tV, idx: i)

  var g = initKernelGlobals()
  # id : (A : ?) -> A -> A ; body returns the last argument
  let idTy = pi(star, pi(vv(0), pi(vv(1), vv(2))))
  let idTm = lam(lam(lam(vv(0))))
  assert kernelCheck(idTm, idTy, g), "id should check"
  # ill-typed: body returns A (the type) instead of a term of type A
  let badTm = lam(lam(lam(vv(2))))
  assert not kernelCheck(badTm, idTy, g), "bad id should be rejected"
  # eta: lam x. id x =?= id
  assert kconv(lam(app(idTm, vv(0))), idTm, g), "eta should hold"
  # non-dependent pair against Sigma
  let siTy = Term(kind: tSi, dom: star, scope: Scope(bdy: star),
                  impl: false, erased: false, qty: qOmega)
  let pairTm = Term(kind: tPair, pFst: star, pSnd: star,
                    pScope: Scope(bdy: star))
  assert kernelCheck(pairTm, siTy, g), "pair should check"
  # unbound variable rejected
  assert not kernelCheck(vv(3), star, g), "unbound var should be rejected"
  # application of non-function rejected
  assert not kernelCheck(app(star, star), star, g), "app of non-fn rejected"
  # fst/snd
  let fstTm = Term(kind: tFst, sub: pairTm)
  assert kernelCheck(fstTm, star, g), "fst should check"
  # kernelCheckDef enforces type well-formedness too
  assert kernelCheckDef("id", idTm, idTy, g), "kernelCheckDef accepts id"
  assert not kernelCheckDef("bad", badTm, idTy, g), "kernelCheckDef rejects bad"
  # definitions delta-unfold: d := id, applied, still checks
  g.entries[7] = KGEntry(ty: idTy, def: idTm)
  let dRef = Term(kind: tR, refId: 7, refTyp: nil, refIsDefn: true, refVal: nil)
  assert kernelCheck(app(app(app(dRef, star), star), star), star, g),
    "defined reference should unfold and check"
  # dependent pair elimination (regression: sigma-binder elimination must
  # decrement outer indices -- kinst, not ksubstKeep):
  # (A B : ?) (p : Sig (u : A). B) |- (snd p, fst p) : Sig (v : B). A
  let siAB = Term(kind: tSi, dom: vv(1), scope: Scope(bdy: vv(1)),
                  impl: false, erased: false, qty: qOmega)   # at depth 2
  let siBA = Term(kind: tSi, dom: vv(1), scope: Scope(bdy: vv(3)),
                  impl: false, erased: false, qty: qOmega)   # at depth 3
  let swapTy =
    Term(kind: tPi, dom: star, scope: Scope(bdy:
      Term(kind: tPi, dom: star, scope: Scope(bdy:
        Term(kind: tPi, dom: siAB, scope: Scope(bdy: siBA),
             impl: false, erased: false, qty: qOmega)),
        impl: false, erased: false, qty: qOmega)),
      impl: false, erased: false, qty: qOmega)
  let swapTm = lam(lam(Term(kind: tLam, dom: siAB,
    scope: Scope(bdy: Term(kind: tPair,
      pFst: Term(kind: tSnd, sub: vv(0)),
      pSnd: Term(kind: tFst, sub: vv(0)),
      pScope: Scope(bdy: star))),
    impl: false, erased: false, qty: qOmega)))
  assert kernelCheck(swapTm, swapTy, g), "dependent pairSwap should check"

  # --- Issue #156 self-tests: iota, nat literals, primops -------------------
  # A miniature Nat: postulate Nat/zero/suc + hand-written natElim.
  let natId = 100; let zeroId = 101; let sucId = 102; let elimId = 103
  let natTy = star
  g.entries[natId] = KGEntry(ty: natTy, def: nil)
  g.entries[zeroId] = KGEntry(ty: kref(natId), def: nil)
  g.entries[sucId] = KGEntry(ty: pi(kref(natId), kref(natId)), def: nil)
  g.natZeroId = zeroId; g.natSucId = sucId
  # natElim : Pi (C : Nat -> ?) (z : C zero)
  #             (s : Pi (n : Nat). C n -> C (suc n)) (n : Nat). C n
  let cVar = vv(3)  # C, from inside the body (depth 4)
  let elimTy =
    pi(pi(kref(natId), star),                       # C : Nat -> ?
      pi(app(vv(0), kref(zeroId)),                   # z : C zero
        pi(pi(kref(natId),                           # s : Pi (n:Nat). C n -> C (suc n)
              pi(app(vv(2), vv(0)),
                app(vv(3), app(kref(sucId), vv(1))))),
          pi(kref(natId), app(vv(3), vv(0))))))      # (n:Nat). C n
  g.entries[elimId] = KGEntry(ty: elimTy, def: nil,
                              isElim: true, elimNargs: 4)
  # Templates in context [elim args C z s, tele args], innermost-first.
  # zero rule: `red natElim C z s zero = z`; template ctx [s,z,C]: z = V(1).
  # suc rule: `red natElim C z s (suc n) = s n (natElim C z s n)`;
  #   template ctx [n,s,z,C]: n=V(0), s=V(1), z=V(2), C=V(3).
  let elimRef = kref(elimId)
  let zeroTmpl = vv(1)
  let sucTmpl = app(app(vv(1), vv(0)),
                    app(app(app(app(elimRef, vv(3)), vv(2)), vv(1)), vv(0)))
  var ncases = initTable[int, KElimCase]()
  ncases[zeroId] = KElimCase(tmpl: zeroTmpl, valid: false)
  ncases[sucId] = KElimCase(tmpl: sucTmpl, valid: false)
  g.elimRules[elimId] = KElimRuleSet(nParams: 0, cases: ncases)
  validateElimRules(g)  # the motive check must accept both rules
  assert g.elimRules[elimId].cases[zeroId].valid, "zero rule should validate"
  assert g.elimRules[elimId].cases[sucId].valid, "suc rule should validate"
  # A bad rule (wrong contractum) must be caught by the motive check.
  var bcases = initTable[int, KElimCase]()
  bcases[zeroId] = KElimCase(tmpl: vv(0), valid: false)  # `s` : wrong type
  g.elimRules[elimId] = KElimRuleSet(nParams: 0, cases: bcases)
  var caught = false
  try:
    validateElimRules(g)
  except KernelError as e:
    caught = not isFragmentViolation(e)
  assert caught, "ill-typed iota rule must be a genuine disagreement"
  g.elimRules[elimId] = KElimRuleSet(nParams: 0, cases: ncases)
  validateElimRules(g)
  # iota fires: natElim C z s (suc (suc zero)) computes.
  # add2 : Nat -> Nat := lam n. natElim (lam _. Nat) zero
  #                              (lam p. lam ih. suc ih) n
  let motive = lam(kref(natId))
  let stepFn = lam(lam(app(kref(sucId), vv(0))))
  let elimApp = app(app(app(app(elimRef, motive), kref(zeroId)), stepFn), vv(0))
  let add2 = lam(elimApp)
  let two = app(kref(sucId), app(kref(sucId), kref(zeroId)))
  assert kconv(app(add2, two), two, g), "iota should compute add2 2 = 2"
  # stuck on neutral scrutinee: stays neutral, still checks
  let nVarTy = kref(natId)
  assert kernelCheck(add2, pi(nVarTy, nVarTy), g),
    "elim on neutral scrutinee should check"
  # tNatLit: definitionally suc^n(zero)
  assert kconv(Term(kind: tNatLit, natLitVal: 2), two, g),
    "tNatLit 2 should equal suc (suc zero)"
  assert kconv(kInfer(Term(kind: tNatLit, natLitVal: 2), @[], g),
               kref(natId), g), "tNatLit 2 should infer Nat"
  # Issue #74: singleton types. The kernel self-test globals register
  # natId above; point natTypeId at it for the subsumption base rule.
  g.natTypeId = natId
  let sing2 = Term(kind: tNatSing, natSingVal: 2)
  let sing3 = Term(kind: tNatSing, natSingVal: 3)
  assert kconv(kInfer(sing2, @[], g), star, g),
    "tNatSing 2 should infer ?"
  kCheck(Term(kind: tNatLit, natLitVal: 2), sing2, @[], g)
  var singMismatch = false
  try:
    kCheck(Term(kind: tNatLit, natLitVal: 3), sing2, @[], g)
  except KernelError:
    singMismatch = true
  assert singMismatch, "tNatLit 3 must not check against singleton 2"
  assert ksubsumes(sing2, kref(natId), g),
    "tNatSing 2 should subsume to Nat"
  assert ksubsumes(sing2, sing2, g), "tNatSing 2 should subsume to itself"
  assert not ksubsumes(sing2, sing3, g),
    "tNatSing 2 must not subsume to tNatSing 3"
  assert not ksubsumes(kref(natId), sing2, g),
    "Nat must not subsume to tNatSing 2"
  # Pi covariance: (d:2) -> 2 subsumes to (d:2) -> Nat.
  assert ksubsumes(pi(sing2, sing2), pi(sing2, kref(natId)), g),
    "Pi codomain should be covariant in the singleton rule"
  # tInt/tPrim: kernel axiom Int -> Int -> Int; fires on literals
  let intId = 200
  g.entries[intId] = KGEntry(ty: star, def: nil)
  g.intId = intId
  let intTy = kref(intId)
  let primTy = pi(intTy, pi(kshift(intTy, 0, 1), kshift(intTy, 0, 2)))
  let addPrim = Term(kind: tPrim, primOp: opAdd, primTy: primTy)
  assert ksynEq(kInfer(addPrim, @[], g), primTy), "primop infers its axiom type"
  assert kconv(app(app(addPrim, Term(kind: tInt, intVal: 20)),
                   Term(kind: tInt, intVal: 22)),
               Term(kind: tInt, intVal: 42), g),
    "addInt 20 22 should compute to 42"
  # stuck primop stays neutral and compares structurally
  let xTy = intTy
  let stuckT = lam(app(app(addPrim, Term(kind: tInt, intVal: 1)), vv(0)))
  assert kernelCheck(stuckT, pi(xTy, xTy), g),
    "primop on neutral arg should check"
  assert not kconv(app(app(addPrim, Term(kind: tInt, intVal: 1)),
                       Term(kind: tInt, intVal: 2)),
                   Term(kind: tInt, intVal: 4), g),
    "addInt 1 2 should not equal 4"
  echo "all kernel self-tests passed"
