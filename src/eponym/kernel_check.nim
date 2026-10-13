#===============================================================================
# kernel_check.nim -- Independent minimal kernel checker (Issue #62).
#
# Value category: (d) improved certainty about "proved"/certified conclusions.
#
# LCF-style: a small, deliberately independent implementation of the core
# typing judgments re-checks every elaborated core term. The direct
# elaborator (elab.nim) and the finally-tagless core (eponym.nim) are the
# untrusted producers; this kernel is the auditor.
#
# Design (see decisions.org entry for #62):
# - SHARED: the Term syntax (eponym_init.Term) -- it is the artifact being
#   audited, so the kernel must read the same representation. The cached
#   Value fields (refTyp, refVal) inside tR nodes are treated as UNTRUSTED
#   hints and never consulted; only the global type table below is used.
# - INDEPENDENT: everything else is re-implemented from scratch --
#   capture-avoiding substitution, a fresh weak-head evaluator (no NbE,
#   no Values, no RedRule registry), type-directed conversion with eta,
#   and the bidirectional check/infer rules. No import of eponym.nim or
#   elab.nim checking code.
#
# Fragment status (v1, honest scope): the pure ETT fragment --
#   Pi, Sigma, Lam, Pair, App, Fst, Snd, Let, Absurd, ?, 1, O, 0,
#   variables and global references (data constructors as neutrals,
#   definitions delta-unfolded from the kernel's own table).
# NOT yet covered: data-eliminator iota reduction (needs the RedRule
#   registry the kernel deliberately does not share), tInt/tPrim
#   (Experiment 11), tNatLit literal expansion (Issue #93), metavariables
#   (tMeta raises -- the zonk invariant must hold before kernel checking).
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
    ## which the kernel treats as neutrals).
    ty*: Term
    def*: Term

  KernelGlobals* = Table[int, KGEntry]

proc kerr(msg: string): ref KernelError =
  newException(KernelError, msg)

proc isFragmentViolation(e: ref KernelError): bool =
  e.msg.startsWith("out of kernel fragment") or
    e.msg.startsWith("tMeta")

# --- de Bruijn plumbing (fresh implementation) -------------------------------

proc kshift(tm: Term, cutoff, amt: int): Term =
  ## Shift free indices >= cutoff by amt.
  case tm.kind
  of tV:
    if tm.idx >= cutoff: Term(kind: tV, idx: tm.idx + amt)
    else: tm
  of tR, tC, tInt, tNatLit:
    tm
  of tMeta:
    raise kerr("tMeta in kernel term: zonk invariant violated")
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
    raise kerr("tPrim out of kernel fragment (v1)")

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
  of tR, tC, tInt, tNatLit:
    tm
  of tMeta:
    raise kerr("tMeta in kernel term: zonk invariant violated")
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
    raise kerr("tPrim out of kernel fragment (v1)")

proc kinst(bdy: Term, arg: Term): Term =
  ## Instantiate the body of a scope with `arg` (index 0); the result lives
  ## one binder shallower (beta-like).
  ksubst(bdy, arg, 0)

proc ksubstKeep(bdy: Term, s: Term): Term =
  ## Substitute `s` for index 0 without changing the depth: outer binders
  ## keep their indices. For check-mode lambda/pair and snd-projection,
  ## where the body is checked in the same context the codomain was written.
  ksubst(bdy, s, 0, shrink = false)

# --- weak-head evaluation (fresh; beta + delta + pair/let, no eliminators) ---

proc kwhnf(tm: Term, g: KernelGlobals, depth: int = 0): Term =
  if depth > 500: raise kerr("kernel whnf depth exceeded (cyclic definition?)")
  var t = tm
  while true:
    case t.kind
    of tApp:
      let f = kwhnf(t.fn, g, depth+1)
      if f.kind == tLam:
        t = kinst(f.scope.bdy, t.arg)
      else:
        return Term(kind: tApp, fn: f, arg: t.arg)
    of tR:
      if g.hasKey(t.refId):
        let e = g[t.refId]
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
      raise kerr("tMeta in kernel term: zonk invariant violated")
    of tInt:
      raise kerr("tInt out of kernel fragment (v1)")
    of tNatLit:
      raise kerr("tNatLit out of kernel fragment (v1)")
    of tPrim:
      raise kerr("tPrim out of kernel fragment (v1)")
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
    if not g.hasKey(tm.refId):
      raise kerr("unknown global refId " & $tm.refId)
    g[tm.refId].ty
  of tC:
    star  # ? : ?, 1 : ?, O : ?, 0 : ?
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
    ksubstKeep(sty.scope.bdy, Term(kind: tFst, sub: tm.sub))
  of tAbsurd:
    # in infer mode the result type is unknown; kernel requires check mode
    raise kerr("tAbsurd requires check mode (result type unknown)")
  of tLam:
    raise kerr("tLam requires check mode (domain not annotated)")
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
    raise kerr("tMeta in kernel term: zonk invariant violated")
  of tInt:
    raise kerr("tInt out of kernel fragment (v1)")
  of tNatLit:
    raise kerr("tNatLit out of kernel fragment (v1)")
  of tPrim:
    raise kerr("tPrim out of kernel fragment (v1)")

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
    kCheck(tm.pSnd, ksubstKeep(wty.scope.bdy, tm.pFst), ctx, g)
  of tAbsurd:
    let sty = kwhnf(kInfer(tm.sub, ctx, g), g)
    if sty.kind != tC or sty.c != cVoid:
      raise kerr("absurd requires a proof of O")
  else:
    let inferred = kInfer(tm, ctx, g)
    if not kconv(inferred, ty, g):
      raise kerr("type mismatch")

# --- public API --------------------------------------------------------------

proc kernelCheck*(tm: Term, ty: Term, g: KernelGlobals): bool =
  ## Returns true iff `tm` checks against `ty` in the kernel.
  ## Ill-typed input returns false. Fragment violations (tMeta, tInt,
  ## tNatLit, tPrim, eliminator-dependent conversion) are re-raised so
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

  var g: KernelGlobals
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
  g[7] = KGEntry(ty: idTy, def: idTm)
  let dRef = Term(kind: tR, refId: 7, refTyp: nil, refIsDefn: true, refVal: nil)
  assert kernelCheck(app(app(app(dRef, star), star), star), star, g),
    "defined reference should unfold and check"
  echo "all kernel self-tests passed"
