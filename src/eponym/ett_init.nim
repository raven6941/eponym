#===============================================================================
# ett_init.nim -- ETT with an *initial* encoding (concrete first-order AST),
# for comparison with the finally-tagless ett.nim.
#
# This follows Chapman, Altenkirch & McBride, "Epigram Reloaded" §§6.4-6.7 far
# more directly than ett.nim does:
#   §6.4  Term is a datatype with de Bruijn indices (V Int); free variables
#         are R nodes carrying their type (and value, for definitions).
#   §6.6  Values glue syntax to weak-head normal forms; evaluation threads an
#         explicit environment. Scopes become host functions (Value -> Value).
#   §6.5  infer / synth / check work on closed terms: going under a binder
#         instantiates the scope with a fresh parameter (R node).
#   §6.7  areEqual is type-directed: proof-irrelevance for 1 and O,
#         eta for Pi/Sigma, structural comparison of neutral spines.
#
# Because terms are just records, there is no pretty-printing interpretation
# to write: `$` dumps the AST and that *is* the view.
#
# Simplifications vs the paper: fresh names come from a global counter rather
# than the Checking monad's root-name threading; the reference's cached info
# lives directly in the R node instead of a separate Reference table.
#===============================================================================

import sequtils
import tables
import hashes
import preterm  # for Quantity (Issue #64)

type
  Const* = enum cStar, cOne, cVoid, cZero   # ?  1  hi  O
  PrimOp* = enum opAdd, opSub, opMul  # primitive Int operations (Exp 11)
  TermKind* = enum
    tR, tV, tPi, tSi, tLam, tPair, tApp, tFst, tSnd, tAbsurd, tC, tLet,
    tMeta, tInt, tPrim, tNatLit
    ## tMeta: an elaborator metavariable (Experiment 3). The core never
    ## assigns or evaluates them: the elaborator zonks (substitutes all
    ## solutions) before calling check/infer, and every core operation
    ## raises on tMeta as a safety net if the invariant is violated.
    ## tPi/tSi/tLam carry `impl`: implicit-binder metadata written by
    ## the elaborator and preserved (but never interpreted) by the core.
    ## tInt: a primitive integer literal (Experiment 11).
    ## tPrim: a primitive Int operation (Experiment 11).
    ## tNatLit: a primitive Nat literal (Issue #93). Definitionally equal
    ##   to suc^n(zero); the elaborator always emits this form for numerals
    ##   (O(1) construction), and conversion expands literals when comparing
    ##   against hand-written suc-chains (see defaultConv in elab.nim).
  WhnfKind* = enum wRef, wPi, wSi, wLam, wPair, wConst, wRed, wInt, wPrim,
                     wNatLit
  ## wInt: a primitive integer value (Experiment 11).
  ## wNatLit: a primitive Nat literal value (Issue #93); definitionally
  ## suc^n(zero). Compared by int equality; hand-written suc-chains
  ## evaluate to wRef spines and are handled by the elaborator's
  ## literal-expansion fallback in defaultConv.
  ## wPrim: a primitive operation (addInt, subInt, mulInt) accumulating
  ## args; fires when fully applied to wInt args (Experiment 11).
  ## A registered reduction rule (Experiment 4): an eliminator applied to
  ## `nargs` arguments (last = scrutinee) reduces according to `cases`
  ## when the scrutinee's head is a registered constructor. Each case maps
  ## a constructor refId to a contractum *template*: a Term in the context
  ## [elim args except scrutinee (nargs-1 vars), ctor args (m vars)].
  RedRule = object
    nargs: int
    cases: Table[int, Term]
    nParams: int  # leading scrutinee spine args that are (already-bound)
                  # params, not fresh ctor vars (Experiment 5: data)
  ElimVKind = enum eApp, eFst, eSnd, eAbsurd
  Scope* = object
    adv*: string   # display hint, as in the paper's Scope
    bdy*: Term
  Term* = ref object
    case kind*: TermKind
    of tR:
      refId*: int
      refTyp*: Value
      refIsDefn*: bool
      refVal*: Value
    of tV:
      idx*: int
    of tPi, tSi, tLam:
      dom*: Term
      scope*: Scope
      impl*: bool
      erased*: bool  # Experiment 9: QTT-lite 0-quantity (erased at runtime)
      qty*: Quantity # Issue #64: binder quantity (q0/q1/qOmega)
    of tMeta:
      metaId*: int
      metaSpine*: seq[Term]  # innermost-first; one entry per creation-var
    of tPair:
      pFst*, pSnd*: Term
      pScope*: Scope
    of tApp:
      fn*, arg*: Term
    of tFst, tSnd, tAbsurd:
      sub*: Term
    of tC:
      c*: Const
    of tLet:
      letVal*, letTy*: Term
      letScope*: Scope
    of tInt:
      intVal*: int
    of tNatLit:
      natLitVal*: int
    of tPrim:
      primOp*: PrimOp
      primTy*: Term  # the Pi type (Int -> Int -> Int), for infer
  ElimV = object
    case kind: ElimVKind
    of eApp:
      arg: Value
    else:
      discard
  ScoVal = object
    syn: Scope
    fn: proc(x: Value): Value
  Whnf* = ref object
    case kind*: WhnfKind
    of wRef:
      refId: int
      spine: seq[ElimV]
    of wPi, wSi:
      dom: Value
      tscope: ScoVal
      qty: Quantity  # Issue #66: binder quantity, compared by conversion
    of wLam:
      lscope: ScoVal
    of wPair:
      fstV, sndV: Value
    of wConst:
      c: Const
    of wRed:
      ## an eliminator with registered reduction rules, accumulating args
      elimId: int
      rule: RedRule
      args: seq[Value]   # accumulated so far (function position order)
    of wInt:
      intVal*: int
    of wNatLit:
      natLitVal*: int
    of wPrim:
      op: PrimOp
      pargs: seq[Value]  # accumulated so far (function position order)
  Value* = ref object
    syn*: Term   # the syntax, glued (§6.6) -- makes instantiation easy
    whnf*: Whnf

## --- constructors ------------------------------------------------------------

proc mkR(id: int, typ: Value, isDefn: bool, dval: Value): Term =
  Term(kind: tR, refId: id, refTyp: typ, refIsDefn: isDefn, refVal: dval)

proc vv*(i: int): Term = Term(kind: tV, idx: i)

proc tmPi*(dom: Term, adv: string, bdy: Term, impl = false, erased = false,
           qty = qOmega): Term =
  Term(kind: tPi, dom: dom, scope: Scope(adv: adv, bdy: bdy), impl: impl,
       erased: erased, qty: qty)
proc tmSi*(dom: Term, adv: string, bdy: Term, impl = false, erased = false,
           qty = qOmega): Term =
  Term(kind: tSi, dom: dom, scope: Scope(adv: adv, bdy: bdy), impl: impl,
       erased: erased, qty: qty)
proc tmLam*(dom: Term, adv: string, bdy: Term, impl = false, erased = false,
            qty = qOmega): Term =
  Term(kind: tLam, dom: dom, scope: Scope(adv: adv, bdy: bdy), impl: impl,
       erased: erased, qty: qty)
proc tmMeta*(id: int, spine: seq[Term]): Term =
  Term(kind: tMeta, metaId: id, metaSpine: spine)

proc mkBinder*(k: TermKind, dom: Term, sc: Scope, impl: bool, qty = qOmega): Term =
  case k
  of tPi: tmPi(dom, sc.adv, sc.bdy, impl, false, qty)
  of tSi: tmSi(dom, sc.adv, sc.bdy, impl, false, qty)
  of tLam: tmLam(dom, sc.adv, sc.bdy, impl, false, qty)
  else: raise newException(ValueError, "mkBinder: not a binder")

proc tmPair*(fstT, sndT: Term, adv: string, ranBdy: Term): Term =
  Term(kind: tPair, pFst: fstT, pSnd: sndT, pScope: Scope(adv: adv, bdy: ranBdy))
proc tmApp*(f, a: Term): Term = Term(kind: tApp, fn: f, arg: a)
proc tmFst*(s: Term): Term = Term(kind: tFst, sub: s)
proc tmSnd*(s: Term): Term = Term(kind: tSnd, sub: s)
proc tmAbsurd*(z: Term): Term = Term(kind: tAbsurd, sub: z)
proc tmLet*(v, ty: Term, adv: string, bdy: Term): Term =
  Term(kind: tLet, letVal: v, letTy: ty, letScope: Scope(adv: adv, bdy: bdy))
proc tmC*(c: Const): Term = Term(kind: tC, c: c)
proc tmInt*(n: int): Term = Term(kind: tInt, intVal: n)
proc tmNatLit*(n: int): Term = Term(kind: tNatLit, natLitVal: n)
proc tmPrim*(op: PrimOp, ty: Term): Term = Term(kind: tPrim, primOp: op, primTy: ty)

proc tStar(): Term = Term(kind: tC, c: cStar)
proc tOne(): Term = Term(kind: tC, c: cOne)
proc tTt(): Term = Term(kind: tC, c: cVoid)
proc tZero(): Term = Term(kind: tC, c: cZero)

## --- viewing the records (this replaces the pretty-printer) -----------------

proc `$`(c: Const): string =
  case c
  of cStar: "?"
  of cOne: "1"
  of cVoid: "hi"
  of cZero: "O"

proc `$`*(t: Term): string  # forward (mutual with Scope)

proc `$`(s: Scope): string = s.adv & ". " & $s.bdy

proc `$`*(t: Term): string =
  if t == nil: return "<nil>"
  case t.kind
  of tR: "R" & $t.refId
  of tV: "V" & $t.idx
  of tC: $t.c
  of tInt: $t.intVal
  of tNatLit: $t.natLitVal
  of tPrim: $t.primOp
  of tPi: (if t.impl: "Pi{" else: "Pi(") & $t.dom & ", " & $t.scope & ")"
  of tSi: (if t.impl: "Si{" else: "Si(") & $t.dom & ", " & $t.scope & ")"
  of tLam: (if t.impl: "L{" else: "L(") & $t.dom & ", " & $t.scope & ")"
  of tMeta: "?m" & $t.metaId
  of tPair: "P(" & $t.pFst & ", " & $t.pSnd & ", " & $t.pScope & ")"
  of tApp: "(" & $t.fn & " :$ A " & $t.arg & ")"
  of tFst: "(" & $t.sub & " :$ P0)"
  of tSnd: "(" & $t.sub & " :$ P1)"
  of tAbsurd: "(" & $t.sub & " :$ OE)"
  of tLet: "Let(" & $t.letVal & " : " & $t.letTy & ", " & $t.letScope & ")"

proc hashTerm*(t: Term): Hash =
  ## Experiment 47: structural hash of a Term, for O(1)-int memo keys in
  ## the conversion cache. Mirrors the `$` rendering's notion of identity
  ## (refId for tR, idx for tV) but with integer arithmetic instead of
  ## string building — the key render on every conversion goal was
  ## costing nearly as much as the NbE it skipped (#41 benchmark).
  ## `impl`/`erased` are folded in even though `$` omits `erased`:
  ## distinguishing more is sound (it can only turn hits into misses).
  if t == nil: return hash(0x9E3779B9)
  result = hash(t.kind.ord)
  case t.kind
  of tR: result = result !& hash(t.refId)
  of tV: result = result !& hash(t.idx)
  of tC: result = result !& hash(t.c.ord)
  of tInt: result = result !& hash(t.intVal)
  of tNatLit: result = result !& hash(t.natLitVal)
  of tPrim:
    result = result !& hash(t.primOp.ord)
    result = result !& hashTerm(t.primTy)
  of tPi, tSi, tLam:
    result = result !& hash(if t.impl: 1 else: 0)
    result = result !& hash(if t.erased: 1 else: 0)
    result = result !& hash(t.scope.adv)
    result = result !& hashTerm(t.dom)
    result = result !& hashTerm(t.scope.bdy)
  of tMeta:
    result = result !& hash(t.metaId)
    for s in t.metaSpine: result = result !& hashTerm(s)
  of tPair:
    result = result !& hashTerm(t.pFst)
    result = result !& hashTerm(t.pSnd)
    result = result !& hash(t.pScope.adv)
    result = result !& hashTerm(t.pScope.bdy)
  of tApp:
    result = result !& hashTerm(t.fn)
    result = result !& hashTerm(t.arg)
  of tFst, tSnd, tAbsurd:
    result = result !& hashTerm(t.sub)
  of tLet:
    result = result !& hashTerm(t.letVal)
    result = result !& hashTerm(t.letTy)
    result = result !& hash(t.letScope.adv)
    result = result !& hashTerm(t.letScope.bdy)
  result = !$result

## --- fresh parameters / definitions ------------------------------------------
## The supply is threaded explicitly (the paper's Checking-monad threading)
## rather than held in a global: the Nim VM cannot capture module-level state,
## so compile-time checking via macros needs the supply as a parameter. This
## also makes the core reentrant.

type Supply* = object
  n: int

proc freshId*(s: var Supply): int =
  inc s.n
  s.n

proc newDefRef*(s: var Supply, typ, val: Value): Term =
  ## A closed definition reference for the elaborator's global scope:
  ## earlier elaborated defs become R nodes later defs can mention.
  mkR(freshId(s), typ, true, val)

proc whnfKind*(v: Value): WhnfKind = v.whnf.kind
proc whnfRefId*(v: Value): int = v.whnf.refId
proc whnfSpineLen*(v: Value): int = v.whnf.spine.len
proc whnfSpineArg*(v: Value, i: int): Value = v.whnf.spine[i].arg

proc newPostulateRef*(s: var Supply, typ: Value): Term =
  ## Experiment 4: a parameter-like global (type former or constructor).
  ## Never unfolds; stays neutral.
  mkR(freshId(s), typ, false, nil)

proc newRedRef*(s: var Supply, typ: Value, nargs: int): Term =
  ## Experiment 4: an eliminator reference whose value is a registered
  ## reduction rule. `red` declarations add cases to the rule table.
  let id = freshId(s)
  let r = mkR(id, typ, true, nil)
  r.refVal = Value(syn: r,
    whnf: Whnf(kind: wRed, elimId: id,
               rule: RedRule(nargs: nargs, cases: initTable[int, Term]()),
               args: newSeq[Value]()))
  r

proc attachRedCase*(elim: Term, ctorId: int, tmpl: Term, nParams = 0) =
  ## Experiment 4: register one constructor case on an eliminator.
  ## Raises on duplicates (overlapping rules would break confluence).
  ## nParams (Experiment 5): leading scrutinee spine args that are
  ## already-bound params, not fresh ctor vars.
  let w = elim.refVal.whnf
  if w.kind != wRed:
    raise newException(ValueError, "not an eliminator reference")
  if ctorId in w.rule.cases:
    raise newException(ValueError, "duplicate reduction rule for constructor")
  w.rule.cases[ctorId] = tmpl
  if w.rule.nParams == 0:
    w.rule.nParams = nParams
  elif w.rule.nParams != nParams:
    raise newException(ValueError, "inconsistent param count in reduction rules")

proc redNargs*(elim: Term): int =
  ## number of arguments (incl. scrutinee) the eliminator takes
  elim.refVal.whnf.rule.nargs

proc freshPara*(s: var Supply, ty: Value): Value =
  ## vpara: a fresh neutral parameter of the given type.
  ## Exported for the elaborator's conversion check (Experiment 5b):
  ## free variables become neutral parameters so open
  ## terms can be evaluated. The type may be nil — conversion never
  ## inspects a parameter's type, only its identity.
  let id = freshId(s)
  Value(syn: mkR(id, ty, false, nil),
        whnf: Whnf(kind: wRef, refId: id, spine: newSeq[ElimV]()))

proc freshDefn(s: var Supply, v, ty: Value): Value =
  ## vdefn: a fresh reference carrying a local definition
  let id = freshId(s)
  Value(syn: mkR(id, ty, true, v),
        whnf: Whnf(kind: wRef, refId: id, spine: newSeq[ElimV]()))

## --- substitution, instantiation, abstraction (§6.4.1) -----------------------

proc weaken*(t: Term): Term  # forward (used by subst)

proc subst*(t: Term, depth: int, s: Term): Term =
  ## Substitute s for V depth; drop indices above depth. s may be open: it
  ## is weakened on going under binders. (The old contract said "closed s";
  ## Experiment 3 instantiates Pi/Sigma codomains with open elaborated
  ## arguments, so the substitute is weakened like any other free term.)
  ## Exported for the elaborator.
  case t.kind
  of tV:
    if t.idx == depth: s
    elif t.idx > depth: vv(t.idx - 1)
    else: t
  of tR, tC, tInt, tPrim, tNatLit: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(subst(it, depth, s)))
  of tPi, tSi, tLam:
    mkBinder(t.kind, subst(t.dom, depth, s),
             Scope(adv: t.scope.adv,
                   bdy: subst(t.scope.bdy, depth + 1, weaken(s))),
             t.impl, t.qty)
  of tPair:
    tmPair(subst(t.pFst, depth, s), subst(t.pSnd, depth, s),
           t.pScope.adv, subst(t.pScope.bdy, depth + 1, weaken(s)))
  of tApp: tmApp(subst(t.fn, depth, s), subst(t.arg, depth, s))
  of tFst: tmFst(subst(t.sub, depth, s))
  of tSnd: tmSnd(subst(t.sub, depth, s))
  of tAbsurd: tmAbsurd(subst(t.sub, depth, s))
  of tLet:
    tmLet(subst(t.letVal, depth, s), subst(t.letTy, depth, s),
          t.letScope.adv, subst(t.letScope.bdy, depth + 1, weaken(s)))

proc instantiate(sc: Scope, v: Value): Term =
  ## sc // v : instantiate the bound variable with (the syntax of) v
  subst(sc.bdy, 0, v.syn)

proc absGo(t: Term, id: int, depth: int): Term =
  ## abstract R id as V depth
  case t.kind
  of tR:
    if t.refId == id: vv(depth) else: t
  of tV:
    if t.idx >= depth: vv(t.idx + 1) else: t
  of tC, tInt, tPrim, tNatLit: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(absGo(it, id, depth)))
  of tPi, tSi, tLam:
    mkBinder(t.kind, absGo(t.dom, id, depth),
             Scope(adv: t.scope.adv, bdy: absGo(t.scope.bdy, id, depth + 1)),
             t.impl, t.qty)
  of tPair:
    tmPair(absGo(t.pFst, id, depth), absGo(t.pSnd, id, depth),
           t.pScope.adv, absGo(t.pScope.bdy, id, depth + 1))
  of tApp: tmApp(absGo(t.fn, id, depth), absGo(t.arg, id, depth))
  of tFst: tmFst(absGo(t.sub, id, depth))
  of tSnd: tmSnd(absGo(t.sub, id, depth))
  of tAbsurd: tmAbsurd(absGo(t.sub, id, depth))
  of tLet:
    tmLet(absGo(t.letVal, id, depth), absGo(t.letTy, id, depth),
          t.letScope.adv, absGo(t.letScope.bdy, id, depth + 1))

proc abstractR(id: int, adv: string, t: Term): Scope =
  ## (id, adv) \\ t : bind the free variable R id
  Scope(adv: adv, bdy: absGo(t, id, 0))

proc substEnv(t: Term, env: seq[Value], depth: int): Term =
  ## close t by substituting env values' syntax for V depth..
  case t.kind
  of tV:
    let j = t.idx
    if j < depth: t
    elif j < depth + env.len: env[j - depth].syn
    else: vv(j - env.len)
  of tR, tC, tInt, tPrim, tNatLit: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(substEnv(it, env, depth)))
  of tPi, tSi, tLam:
    mkBinder(t.kind, substEnv(t.dom, env, depth),
             Scope(adv: t.scope.adv, bdy: substEnv(t.scope.bdy, env, depth + 1)),
             t.impl, t.qty)
  of tPair:
    tmPair(substEnv(t.pFst, env, depth), substEnv(t.pSnd, env, depth),
           t.pScope.adv, substEnv(t.pScope.bdy, env, depth + 1))
  of tApp: tmApp(substEnv(t.fn, env, depth), substEnv(t.arg, env, depth))
  of tFst: tmFst(substEnv(t.sub, env, depth))
  of tSnd: tmSnd(substEnv(t.sub, env, depth))
  of tAbsurd: tmAbsurd(substEnv(t.sub, env, depth))
  of tLet:
    tmLet(substEnv(t.letVal, env, depth), substEnv(t.letTy, env, depth),
          t.letScope.adv, substEnv(t.letScope.bdy, env, depth + 1))

proc envAdd(env: seq[Value], v: Value): seq[Value] =
  # Prepend: env[0] is always the *innermost* binding, so V i = env[i].
  # (Appending would require indexing from the back in tV/substEnv.)
  @[v] & env

proc weakenAt(t: Term, depth: int): Term =
  ## shift free de Bruijn indices >= depth up by one
  case t.kind
  of tV:
    if t.idx >= depth: vv(t.idx + 1) else: t
  of tR, tC, tInt, tPrim, tNatLit: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(weakenAt(it, depth)))
  of tPi, tSi, tLam:
    mkBinder(t.kind, weakenAt(t.dom, depth),
             Scope(adv: t.scope.adv, bdy: weakenAt(t.scope.bdy, depth + 1)),
             t.impl, t.qty)
  of tPair:
    tmPair(weakenAt(t.pFst, depth), weakenAt(t.pSnd, depth),
           t.pScope.adv, weakenAt(t.pScope.bdy, depth + 1))
  of tApp: tmApp(weakenAt(t.fn, depth), weakenAt(t.arg, depth))
  of tFst: tmFst(weakenAt(t.sub, depth))
  of tSnd: tmSnd(weakenAt(t.sub, depth))
  of tAbsurd: tmAbsurd(weakenAt(t.sub, depth))
  of tLet:
    tmLet(weakenAt(t.letVal, depth), weakenAt(t.letTy, depth),
          t.letScope.adv, weakenAt(t.letScope.bdy, depth + 1))

proc weaken*(t: Term): Term =
  ## shift all free de Bruijn indices up by one (Experiment 3: eta-expansion
  ## in the unifier)
  weakenAt(t, 0)

proc substSpine*(t: Term, spine: seq[Term]): Term =
  ## Substitute spine[i] for V i all at once; drop indices >= spine.len.
  ## (Experiment 3: instantiating a solved metavariable's solution with the
  ## occurrence spine.)
  case t.kind
  of tV:
    if t.idx < spine.len: spine[t.idx]
    else: vv(t.idx - spine.len)
  of tR, tC, tInt, tPrim, tNatLit: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(substSpine(it, spine)))
  of tPi, tSi, tLam:
    let sp = @[vv(0)] & spine.mapIt(weaken(it))
    mkBinder(t.kind, substSpine(t.dom, spine),
             Scope(adv: t.scope.adv, bdy: substSpine(t.scope.bdy, sp)),
             t.impl, t.qty)
  of tPair:
    let sp = @[vv(0)] & spine.mapIt(weaken(it))
    tmPair(substSpine(t.pFst, spine), substSpine(t.pSnd, spine),
           t.pScope.adv, substSpine(t.pScope.bdy, sp))
  of tApp: tmApp(substSpine(t.fn, spine), substSpine(t.arg, spine))
  of tFst: tmFst(substSpine(t.sub, spine))
  of tSnd: tmSnd(substSpine(t.sub, spine))
  of tAbsurd: tmAbsurd(substSpine(t.sub, spine))
  of tLet:
    let sp = @[vv(0)] & spine.mapIt(weaken(it))
    tmLet(substSpine(t.letVal, spine), substSpine(t.letTy, spine),
          t.letScope.adv, substSpine(t.letScope.bdy, sp))

## --- evaluation (§6.6) -------------------------------------------------------

proc eval*(t: Term, env: seq[Value]): Value  # forward

proc evalScope(sc: Scope, env: seq[Value]): ScoVal =
  ScoVal(syn: Scope(adv: sc.adv, bdy: substEnv(sc.bdy, env, 1)),
         fn: proc(x: Value): Value = eval(sc.bdy, envAdd(env, x)))

proc fireRed(elimId: int, rule: RedRule, args: seq[Value]): Whnf =
  ## Experiment 4: try to fire a registered reduction rule. `args` has
  ## length rule.nargs (last = scrutinee), in application order.
  let scrut = args[^1]
  if scrut.whnf.kind == wRef and scrut.whnf.refId in rule.cases:
    var cargs: seq[Term] = @[]
    # Skip the leading params (Experiment 5); only fresh ctor vars
    # become substitution arguments.
    for i in rule.nParams ..< scrut.whnf.spine.len:
      let e = scrut.whnf.spine[i]
      if e.kind != eApp:  # projections on the scrutinee: stay neutral
        return Whnf(kind: wRef, refId: elimId,
                    spine: args.mapIt(ElimV(kind: eApp, arg: it)))
      cargs.add(e.arg.syn)
    # The template's context is innermost-first: [ctor vars, elim vars].
    # substSpine maps V(i) -> spine[i], so the spine must be innermost-first:
    # ctor args reversed, then elim args (excluding scrutinee) reversed.
    var spine: seq[Term] = @[]
    for i in countdown(cargs.high, 0):
      spine.add(cargs[i])
    for i in countdown(args.high - 1, 0):
      spine.add(args[i].syn)
    let inst = substSpine(rule.cases[scrut.whnf.refId], spine)
    return eval(inst, @[]).whnf
  # fully applied but the scrutinee is not constructor-headed: neutral
  Whnf(kind: wRef, refId: elimId, spine: args.mapIt(ElimV(kind: eApp, arg: it)))

proc applyWhnf*(f, a: Value): Whnf =
  ## the computational half of $$ for application
  case f.whnf.kind
  of wLam: f.whnf.lscope.fn(a).whnf       # beta, by host application
  of wRed:                                # Experiment 4: registered eliminator
    let args2 = f.whnf.args & @[a]
    if args2.len == f.whnf.rule.nargs:
      fireRed(f.whnf.elimId, f.whnf.rule, args2)
    elif args2.len < f.whnf.rule.nargs:
      Whnf(kind: wRed, elimId: f.whnf.elimId, rule: f.whnf.rule, args: args2)
    else:
      raise newException(ValueError, "eliminator applied to too many arguments")
  of wPrim:                               # Experiment 11: primitive Int op
    let args2 = f.whnf.pargs & @[a]
    if args2.len == 2:
      if args2[0].whnf.kind == wInt and args2[1].whnf.kind == wInt:
        let x = args2[0].whnf.intVal
        let y = args2[1].whnf.intVal
        let r = case f.whnf.op
          of opAdd: x + y
          of opSub: x - y
          of opMul: x * y
        Whnf(kind: wInt, intVal: r)
      else:
        # neutral: stuck on non-literal args
        Whnf(kind: wPrim, op: f.whnf.op, pargs: args2)
    elif args2.len < 2:
      Whnf(kind: wPrim, op: f.whnf.op, pargs: args2)
    else:
      raise newException(ValueError, "primitive op applied to too many arguments")
  of wRef:                                # inert: grow the spine
    Whnf(kind: wRef, refId: f.whnf.refId,
         spine: f.whnf.spine & @[ElimV(kind: eApp, arg: a)])
  else: raise newException(ValueError, "stuck application")

proc vApp(f, a: Value): Value =
  Value(syn: tmApp(f.syn, a.syn), whnf: applyWhnf(f, a))

proc projWhnf(p: Value, wantFst: bool): Whnf =
  case p.whnf.kind
  of wPair: (if wantFst: p.whnf.fstV else: p.whnf.sndV).whnf
  of wRef:
    Whnf(kind: wRef, refId: p.whnf.refId,
         spine: p.whnf.spine & @[ElimV(kind: if wantFst: eFst else: eSnd)])
  else: raise newException(ValueError, "stuck projection")

proc vFst(p: Value): Value =
  Value(syn: tmFst(p.syn), whnf: projWhnf(p, true))
proc vSnd(p: Value): Value =
  Value(syn: tmSnd(p.syn), whnf: projWhnf(p, false))

proc vAbsurdV(z: Value): Value =
  case z.whnf.kind
  of wRef:
    Value(syn: tmAbsurd(z.syn),
          whnf: Whnf(kind: wRef, refId: z.whnf.refId,
                     spine: z.whnf.spine & @[ElimV(kind: eAbsurd)]))
  else: raise newException(ValueError, "absurd of canonical empty (impossible)")

proc evalWhnf(t: Term, env: seq[Value]): Whnf =
  case t.kind
  of tR:
    if t.refIsDefn: t.refVal.whnf   # unfold definitions; syn keeps the R node
    else: Whnf(kind: wRef, refId: t.refId, spine: newSeq[ElimV]())
  of tV: env[t.idx].whnf
  of tC: Whnf(kind: wConst, c: t.c)
  of tInt: Whnf(kind: wInt, intVal: t.intVal)
  of tNatLit: Whnf(kind: wNatLit, natLitVal: t.natLitVal)
  of tPrim: Whnf(kind: wPrim, op: t.primOp, pargs: @[])
  of tPi: Whnf(kind: wPi, dom: eval(t.dom, env), tscope: evalScope(t.scope, env), qty: t.qty)
  of tSi: Whnf(kind: wSi, dom: eval(t.dom, env), tscope: evalScope(t.scope, env), qty: t.qty)
  of tLam: Whnf(kind: wLam, lscope: evalScope(t.scope, env))
  of tPair: Whnf(kind: wPair, fstV: eval(t.pFst, env), sndV: eval(t.pSnd, env))
  of tApp: applyWhnf(eval(t.fn, env), eval(t.arg, env))
  of tFst: projWhnf(eval(t.sub, env), true)
  of tSnd: projWhnf(eval(t.sub, env), false)
  of tAbsurd: vAbsurdV(eval(t.sub, env)).whnf
  of tLet: evalWhnf(t.letScope.bdy, envAdd(env, eval(t.letVal, env)))
  of tMeta:
    # The elaborator zonks (substitutes all solutions) before any core
    # operation; reaching here means the invariant was violated.
    raise newException(ValueError,
      "cannot evaluate open metavariable ?m" & $t.metaId)

proc eval*(t: Term, env: seq[Value]): Value =
  ## eval t γ = close t γ ⇓ whnv t γ  (paper §6.6)
  Value(syn: substEnv(t, env, 0), whnf: evalWhnf(t, env))

## --- smart value constructors (§6.5) ------------------------------------------

proc vStar*(): Value =
  Value(syn: tStar(), whnf: Whnf(kind: wConst, c: cStar))
proc vOne(): Value =
  Value(syn: tOne(), whnf: Whnf(kind: wConst, c: cOne))

proc vInt*(n: int): Value =
  Value(syn: tmInt(n), whnf: Whnf(kind: wInt, intVal: n))

proc vPrim*(op: PrimOp, ty: Term): Value =
  ## A primitive Int operation, accumulating args (Experiment 11).
  Value(syn: tmPrim(op, ty), whnf: Whnf(kind: wPrim, op: op, pargs: @[]))

proc vPi(dom: Value, sc: ScoVal, qty = qOmega): Value =
  Value(syn: tmPi(dom.syn, sc.syn.adv, sc.syn.bdy, false, false, qty),
        whnf: Whnf(kind: wPi, dom: dom, tscope: sc, qty: qty))
proc vSi(dom: Value, sc: ScoVal, qty = qOmega): Value =
  Value(syn: tmSi(dom.syn, sc.syn.adv, sc.syn.bdy, false, false, qty),
        whnf: Whnf(kind: wSi, dom: dom, tscope: sc, qty: qty))

proc vAbsurd(): Value =
  eval(tmPi(tStar(), "T", vv(0)), @[])   # Pi(T:? ). T, as in the paper

## --- the typechecker (§§6.5, 6.7) ----------------------------------------------

proc infer(s: var Supply, t: Term): Value
proc check*(s: var Supply, ty: Value, t: Term): Value
proc synth(s: var Supply, t: Term): tuple[val: Value, typ: Value]
proc areEqual*(s: var Supply, ty, a, b: Value)
proc structuralEq(s: var Supply, a, b: Value)
proc isPi(v: Value): tuple[dom: Value, sc: ScoVal]
proc isSi(v: Value): tuple[dom: Value, sc: ScoVal]
proc isZero(v: Value)

proc isPi(v: Value): tuple[dom: Value, sc: ScoVal] =
  if v.whnf.kind == wPi: (v.whnf.dom, v.whnf.tscope)
  else: raise newException(ValueError, "not a Pi type: " & $v.syn)

proc isSi(v: Value): tuple[dom: Value, sc: ScoVal] =
  if v.whnf.kind == wSi: (v.whnf.dom, v.whnf.tscope)
  else: raise newException(ValueError, "not a Sigma type: " & $v.syn)

proc isZero(v: Value) =
  if not (v.whnf.kind == wConst and v.whnf.c == cZero):
    raise newException(ValueError, "not the empty type: " & $v.syn)

proc synth(s: var Supply, t: Term): tuple[val: Value, typ: Value] =
  let ty = infer(s, t)
  (eval(t, @[]), ty)

proc check*(s: var Supply, ty: Value, t: Term): Value =
  # Experiment 11: primitives are trusted from the elaborator; the
  # elaborator already assigned the correct type (Int or Int->Int->Int).
  if t.kind == tInt or t.kind == tPrim or t.kind == tNatLit:
    return eval(t, @[])
  let r = synth(s, t)
  areEqual(s, vStar(), ty, r.typ)
  r.val

proc structuralEq(s: var Supply, a, b: Value) =
  ## structural equality on weak-head forms, with eta for lambdas vs neutrals
  if a.whnf.kind != b.whnf.kind:
    if a.whnf.kind == wLam and b.whnf.kind == wRef:
      let x = freshPara(s, nil)
      structuralEq(s, a.whnf.lscope.fn(x), vApp(b, x))
      return
    if a.whnf.kind == wRef and b.whnf.kind == wLam:
      let x = freshPara(s, nil)
      structuralEq(s, vApp(a, x), b.whnf.lscope.fn(x))
      return
    raise newException(ValueError, "mismatch: " & $a.syn & " vs " & $b.syn)
  case a.whnf.kind
  of wConst:
    if a.whnf.c != b.whnf.c:
      raise newException(ValueError, "constant mismatch")
  of wPi, wSi:
    if a.whnf.qty != b.whnf.qty:
      raise newException(ValueError, "quantity mismatch: " & $a.whnf.qty &
        " vs " & $b.whnf.qty)  # Issue #66: Pi/Sigma binder quantities are
                               # part of the type; (1 x : A) -> B is not
                               # convertible with (ω x : A) -> B
    structuralEq(s, a.whnf.dom, b.whnf.dom)
    let x = freshPara(s, a.whnf.dom)
    structuralEq(s, a.whnf.tscope.fn(x), b.whnf.tscope.fn(x))
  of wLam:
    let x = freshPara(s, nil)
    structuralEq(s, a.whnf.lscope.fn(x), b.whnf.lscope.fn(x))
  of wPair:
    structuralEq(s, a.whnf.fstV, b.whnf.fstV)
    structuralEq(s, a.whnf.sndV, b.whnf.sndV)
  of wRef:
    if a.whnf.refId != b.whnf.refId or a.whnf.spine.len != b.whnf.spine.len:
      raise newException(ValueError, "neutral mismatch")
    for i in 0 ..< a.whnf.spine.len:
      let ea = a.whnf.spine[i]
      let eb = b.whnf.spine[i]
      if ea.kind != eb.kind:
        raise newException(ValueError, "spine mismatch")
      if ea.kind == eApp:
        structuralEq(s, ea.arg, eb.arg)
  of wRed:
    ## partially applied eliminators: same eliminator, same accumulated args
    ## (fully applied stuck eliminators are rebuilt as wRef by applyWhnf)
    if a.whnf.elimId != b.whnf.elimId or a.whnf.args.len != b.whnf.args.len:
      raise newException(ValueError, "eliminator mismatch")
    for i in 0 ..< a.whnf.args.len:
      structuralEq(s, a.whnf.args[i], b.whnf.args[i])
  of wInt:
    if a.whnf.intVal != b.whnf.intVal:
      raise newException(ValueError, "integer mismatch")
  of wNatLit:
    if a.whnf.natLitVal != b.whnf.natLitVal:
      raise newException(ValueError, "nat literal mismatch")
  of wPrim:
    if a.whnf.op != b.whnf.op or a.whnf.pargs.len != b.whnf.pargs.len:
      raise newException(ValueError, "primitive op mismatch")
    for i in 0 ..< a.whnf.pargs.len:
      structuralEq(s, a.whnf.pargs[i], b.whnf.pargs[i])

proc areEqual*(s: var Supply, ty, a, b: Value) =
  ## type-directed conversion (§6.7). Exported for the elaborator's
  ## conversion check (Experiment 5b); raises ValueError
  ## on mismatch, like the rest of the core.
  case ty.whnf.kind
  of wConst:
    let c = ty.whnf.c
    if c == cOne or c == cZero:
      return  # proof-irrelevant: no need to look
    structuralEq(s, a, b)
  of wPi:
    let x = freshPara(s, ty.whnf.dom)
    areEqual(s, ty.whnf.tscope.fn(x), vApp(a, x), vApp(b, x))
  of wSi:
    areEqual(s, ty.whnf.dom, vFst(a), vFst(b))
    areEqual(s, ty.whnf.tscope.fn(vFst(a)), vSnd(a), vSnd(b))
  else:
    structuralEq(s, a, b)

proc infer(s: var Supply, t: Term): Value =
  ## infer implements the typing rules of Fig. 6.2, syntax-directed (§6.5.1).
  ## Terms are always closed here: binders are instantiated with fresh
  ## parameters on entry, so the V case never arises.
  case t.kind
  of tR: t.refTyp
  of tV:
    raise newException(ValueError, "bound variable escaped into infer")
  of tC:
    case t.c
    of cStar: vStar()
    of cOne: vStar()
    of cVoid: vOne()
    of cZero: vStar()
  of tInt:
    raise newException(ValueError,
      "cannot infer type of integer literal (elaborator must assign Int type)")
  of tNatLit:
    raise newException(ValueError,
      "cannot infer type of nat literal (elaborator must assign Nat type)")
  of tPrim:
    eval(t.primTy, @[])
  of tPi, tSi:
    let domV = check(s, vStar(), t.dom)
    let x = freshPara(s, domV)
    discard check(s, vStar(), instantiate(t.scope, x))
    vStar()
  of tLam:
    let domV = check(s, vStar(), t.dom)
    let x = freshPara(s, domV)
    let ranV = infer(s, instantiate(t.scope, x))
    let asc = abstractR(x.syn.refId, t.scope.adv, ranV.syn)
    vPi(domV, ScoVal(syn: asc,
                     fn: proc(v: Value): Value = eval(asc.bdy, @[v])), t.qty)
  of tApp:
    let fty = infer(s, t.fn)
    let (dom, sc) = isPi(fty)
    let av = check(s, dom, t.arg)
    sc.fn(av)
  of tPair:
    let pScope = t.pScope
    let pSnd = t.pSnd
    let r = synth(s, t.pFst)
    let x = freshPara(s, r.typ)
    discard check(s, vStar(), instantiate(pScope, x))
    let rsc = ScoVal(syn: pScope,
                     fn: proc(v: Value): Value = eval(pScope.bdy, @[v]))
    discard check(s, rsc.fn(r.val), pSnd)
    vSi(r.typ, rsc)
  of tFst:
    let (dom, _) = isSi(infer(s, t.sub))
    dom
  of tSnd:
    let r = synth(s, t.sub)
    let (_, sc) = isSi(r.typ)
    sc.fn(vFst(r.val))
  of tAbsurd:
    isZero(infer(s, t.sub))
    vAbsurd()
  of tMeta:
    raise newException(ValueError,
      "metavariable ?m" & $t.metaId & " escaped into core inference")
  of tLet:
    let styv = check(s, vStar(), t.letTy)
    let sv = check(s, styv, t.letVal)
    let x = freshDefn(s, sv, styv)
    let ttyv = infer(s, instantiate(t.letScope, x))
    let asc = abstractR(x.syn.refId, t.letScope.adv, ttyv.syn)
    ScoVal(syn: asc, fn: proc(v: Value): Value = eval(asc.bdy, @[v])).fn(sv)

## --- examples (the paper's twice, plus friends) --------------------------------
## Written directly as ASTs -- compare with the HOAS versions in ett.nim.

# twice : Pi(X:? ). (X -> X) -> X -> X      (paper §6.4)
let twiceT = tmLam(tStar(), "X",
               tmLam(tmPi(vv(0), "x", vv(1)), "f",
                tmLam(vv(1), "x",
                 tmApp(vv(1), tmApp(vv(1), vv(0))))))

# polyId : Pi(X:? ). X -> X
let polyIdT = tmLam(tStar(), "X", tmLam(vv(0), "x", vv(0)))

# const : Pi(A:? ). Pi(B:? ). A -> B -> A
let constT = tmLam(tStar(), "A",
               tmLam(tStar(), "B",
                tmLam(vv(1), "a",
                 tmLam(vv(2), "b", vv(1)))))

let sig11T = tmSi(tOne(), "_", tOne())   # Sigma(_:1). 1

# pairSwap : Pi(p: Sigma(_:1). 1). Sigma(_:1). 1
let pairSwapT = tmLam(sig11T, "p",
                   tmPair(tmFst(vv(0)), tmSnd(vv(0)), "_", tOne()))

# let x = <> : 1 in x
let letT = tmLet(tTt(), tOne(), "x", vv(0))

## --- tests --------------------------------------------------------------------

when isMainModule:
  var tcSupply = Supply()  # explicit fresh-name supply (no globals)
  echo "--- records (the AST is the view) ---"
  echo "twice    : ", $twiceT
  echo "pairSwap : ", $pairSwapT

  echo "--- evaluation tests ---"
  proc isVoid(v: Value): bool =
    v.whnf.kind == wConst and v.whnf.c == cVoid

  # twice 1 (λx:1. x) <> ==> <>
  let e1 = eval(tmApp(tmApp(tmApp(twiceT, tOne()),
                            tmLam(tOne(), "x", vv(0))), tTt()), @[])
  assert isVoid(e1)
  echo "ok: twice 1 (λx:1. x) <> ==> hi"

  # polyId 1 <> ==> <>
  let e2 = eval(tmApp(tmApp(polyIdT, tOne()), tTt()), @[])
  assert isVoid(e2)
  echo "ok: polyId 1 <> ==> hi"

  # const 1 1 <> <> ==> <>
  let e3 = eval(tmApp(tmApp(tmApp(tmApp(constT, tOne()), tOne()), tTt()), tTt()), @[])
  assert isVoid(e3)
  echo "ok: const 1 1 <> <> ==> hi"

  # fst/snd of <tt;tt>
  let pr = tmPair(tTt(), tTt(), "_", tOne())
  assert isVoid(eval(tmFst(pr), @[]))
  assert isVoid(eval(tmSnd(pr), @[]))
  echo "ok: fst/snd of <hi;hi>"

  # pairSwap <tt;tt> ==> <tt;tt>
  let e5 = eval(tmApp(pairSwapT, pr), @[])
  assert isVoid(vFst(e5)) and isVoid(vSnd(e5))
  echo "ok: pairSwap <hi;hi>"

  # let x = <> : 1 in x ==> <>
  assert isVoid(eval(letT, @[]))
  echo "ok: let x = <> : 1 in x ==> hi"

  # Pi(x:1). 1 evaluates to a Pi value
  let ty = eval(tmPi(tOne(), "x", tOne()), @[])
  assert ty.whnf.kind == wPi
  echo "ok: Pi(x:1). 1 evaluates to a Pi value"

  echo "--- typechecker tests ---"

  # twice checks; inferred type matches Pi(X:? ). (X->X) -> X->X
  let twTy = infer(tcSupply, twiceT)
  echo "twice : ", $twTy.syn
  let arrX = tmPi(vv(0), "x", vv(1))
  let expTwTyT = tmPi(tStar(), "X", tmPi(arrX, "f", tmPi(vv(1), "x", vv(2))))
  areEqual(tcSupply, vStar(), twTy, eval(expTwTyT, @[]))
  echo "ok: twice checks"

  # polyId 1 <> : 1
  let t9t = tmApp(tmApp(polyIdT, tOne()), tTt())
  discard check(tcSupply, vOne(), t9t)
  areEqual(tcSupply, vStar(), infer(tcSupply, t9t), vOne())
  echo "ok: polyId 1 <> : 1"

  proc rejects(t: Term): bool =
    try:
      discard infer(tcSupply, t)
      false
    except ValueError:
      true

  assert rejects(tmApp(polyIdT, tTt())), "polyId <> not rejected"
  echo "ok: polyId <> rejected (argument type mismatch)"
  assert rejects(tmApp(tTt(), tTt())), "<> <> not rejected"
  echo "ok: <> <> rejected (non-function)"
  assert rejects(tmFst(tTt())), "fst <> not rejected"
  echo "ok: fst <> rejected"
  assert rejects(tmAbsurd(tTt())), "absurd <> not rejected"
  echo "ok: absurd <> rejected (non-empty scrutinee)"

  # pairSwap checks
  let psTy = infer(tcSupply, pairSwapT)
  echo "pairSwap : ", $psTy.syn
  echo "ok: pairSwap checks"

  # proof irrelevance for 1: any two inhabitants convertible
  let q1 = freshPara(tcSupply, vOne())
  let q2 = freshPara(tcSupply, vOne())
  areEqual(tcSupply, vOne(), q1, q2)
  echo "ok: proof irrelevance for 1"

  # const checks with the dependent type Pi(A:? ). Pi(B:? ). A -> B -> A
  let cTy = infer(tcSupply, constT)
  echo "const : ", $cTy.syn
  let expCT = tmPi(tStar(), "A",
                tmPi(tStar(), "B",
                 tmPi(vv(1), "a",
                  tmPi(vv(2), "b", vv(3)))))
  areEqual(tcSupply, vStar(), cTy, eval(expCT, @[]))
  echo "ok: const checks"

  echo "--- all tests passed ---"
