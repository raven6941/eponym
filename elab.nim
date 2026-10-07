## Experiment 3: bidirectional elaborator with metavariables, Miller pattern
## unification, and implicit-argument insertion.
##
## Two modes, following Dunfield & Krishnaswami, extended à la
## Kovács's elaboration-zoo / Norell:
##   inferTm -- synthesis mode; produces (Term, Term), the type possibly
##              containing metavariables.
##   checkTm -- checking mode against an expected *Term*; lambdas and pairs
##              elaborate against it, everything else infers then unifies.
##
## Metavariables (unify.nim) are created for implicit arguments, holes `_`,
## unannotated lambda domains, and unknown function/pair types. They are
## solved by pattern unification during elaboration; elabCheck zonks
## (substitutes all solutions) before the core's check/infer ever runs, so
## the core never sees a metavariable in the success path. Leftover unsolved
## metas are elaboration errors carrying the creation location.
##
## Implicit arguments: Pi/lambda binders written `{A : ?}` elaborate to
## core binders flagged `impl`; using a variable whose type has implicit
## leading Pis inserts fresh metas for them (insertImplicits), which
## unification solves from later explicit arguments. There is no surface
## syntax for explicit implicit application in Experiment 3.

import tables
import sequtils
import strutils
import preterm
import parse_surf
import ett_init
import unify

type
  ElabError* = object of CatchableError
    loc*: Loc

proc elabErr(loc: Loc, msg: string): ref ElabError =
  let e = newException(ElabError,
    "line " & $loc.line & ", col " & $loc.col & ": " & msg)
  e.loc = loc
  e

proc unifyElab(ms: var MetaStore, a, b: Term, loc: Loc) =
  ## unify, translating UnifyError into ElabError (adds the source location).
  try:
    unify(ms, a, b, loc)
  except UnifyError as e:
    raise elabErr(loc, e.msg)

type
  CtxEntry = object
    name: string
    ty: Term
  Ctx = seq[CtxEntry]            # innermost-first
  GEntry = object
    tm: Term                     # the R node, for building terms
    ty: Term                     # elaborated + zonked type, for implicits
  Globals = Table[string, GEntry]

proc ext(ctx: Ctx, name: string, ty: Term): Ctx =
  ## Extend the context: every stored type is weakened into the new frame.
  ## (Types are Terms in the frame of the context that stores them; going
  ## under a binder shifts all of them, including the new entry.)
  let w = ctx.mapIt(CtxEntry(name: it.name, ty: weaken(it.ty)))
  @[CtxEntry(name: name, ty: weaken(ty))] & w

proc resolveVar(ctx: Ctx, globals: Globals, name: string,
                loc: Loc): tuple[tm, ty: Term] =
  for i, e in ctx:
    if e.name == name: return (vv(i), e.ty)
  if name in globals:
    let g = globals[name]
    return (g.tm, g.ty)
  raise elabErr(loc, "unbound variable '" & name & "'")

proc headTy(ms: MetaStore, t: Term): Term =
  ## Head-normalize a type for the elaborator: zonk, unfold definitions,
  ## head-beta. Purely syntactic; the core's eval is never involved.
  var cur = zonk(ms, t)
  while true:
    case cur.kind
    of tApp:
      let fh = headTy(ms, cur.fn)
      if fh.kind == tLam:
        cur = zonk(ms, subst(fh.scope.bdy, 0, cur.arg))
      else:
        return tmApp(fh, zonk(ms, cur.arg))
    of tR:
      if cur.refIsDefn and not cur.refVal.isNil:
        cur = zonk(ms, cur.refVal.syn)
      else:
        return cur
    else:
      return cur

proc ensurePi(ms: var MetaStore, loc: Loc, t: Term,
              ctxLen: int): tuple[dom, codBdy: Term, impl: bool, adv: string] =
  ## t's head must be a Pi; a metavariable head is unified with a fresh
  ## (explicit) Pi. Returns dom and the codomain body (in the extended frame).
  let h = headTy(ms, t)
  if h.kind == tPi:
    return (h.dom, h.scope.bdy, h.impl, h.scope.adv)
  if h.kind == tMeta:
    let dom = freshMeta(ms, tmC(cStar), ctxLen, 0, loc)
    let cod = freshMeta(ms, tmC(cStar), ctxLen, 1, loc)
    unifyElab(ms, h, tmPi(dom, "x", cod), loc)
    return (dom, cod, false, "x")
  raise elabErr(loc, "expected a function type")

proc ensureSi(ms: var MetaStore, loc: Loc, t: Term,
              ctxLen: int): tuple[dom, codBdy: Term, adv: string] =
  ## t's head must be a Sigma; a metavariable head is unified with a fresh one.
  let h = headTy(ms, t)
  if h.kind == tSi:
    return (h.dom, h.scope.bdy, h.scope.adv)
  if h.kind == tMeta:
    let dom = freshMeta(ms, tmC(cStar), ctxLen, 0, loc)
    let cod = freshMeta(ms, tmC(cStar), ctxLen, 1, loc)
    unifyElab(ms, h, tmSi(dom, "_", cod), loc)
    return (dom, cod, "_")
  raise elabErr(loc, "expected a Sigma type")

proc insertImplicits(pre: PreTerm, tm, ty: Term, ctxLen: int,
                     ms: var MetaStore): tuple[tm, ty: Term] =
  ## While the type's head is an implicit Pi, apply a fresh metavariable.
  var f = tm
  var fty = ty
  while true:
    let h = headTy(ms, fty)
    if h.kind == tPi and h.impl:
      let m = freshMeta(ms, h.dom, ctxLen, 0, pre.loc)
      f = tmApp(f, m)
      fty = subst(h.scope.bdy, 0, m)
    else:
      break
  (f, fty)

proc inferTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore): tuple[tm, ty: Term]
proc checkTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore, expTy: Term): Term

proc inferTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore): tuple[tm, ty: Term] =
  ## Synthesis mode.
  case pre.kind
  of pkVar:
    let (tm, ty) = resolveVar(ctx, globals, pre.name, pre.loc)
    insertImplicits(pre, tm, ty, ctx.len, ms)
  of pkUniv: (tmC(cStar), tmC(cStar))
  of pkUnitTy: (tmC(cOne), tmC(cStar))
  of pkUnitV: (tmC(cVoid), tmC(cOne))
  of pkEmptyTy: (tmC(cZero), tmC(cStar))
  of pkHole:
    let tyM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
    (freshMeta(ms, tyM, ctx.len, 0, pre.loc), tyM)
  of pkPi:
    let d = checkTm(pre.c1, ctx, globals, ms, tmC(cStar))
    let c = checkTm(pre.c2, ctx.ext(pre.name, d), globals, ms, tmC(cStar))
    (tmPi(d, pre.name, c, pre.impl), tmC(cStar))
  of pkSigma:
    let d = checkTm(pre.c1, ctx, globals, ms, tmC(cStar))
    let c = checkTm(pre.c2, ctx.ext(pre.name, d), globals, ms, tmC(cStar))
    (tmSi(d, pre.name, c), tmC(cStar))
  of pkLam:
    let d =
      if pre.c1.isNil: freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
      else: checkTm(pre.c1, ctx, globals, ms, tmC(cStar))
    let (b, bty) = inferTm(pre.c2, ctx.ext(pre.name, d), globals, ms)
    (tmLam(d, pre.name, b, pre.impl), tmPi(d, pre.name, bty, pre.impl))
  of pkApp:
    var (f, fty) = inferTm(pre.c1, ctx, globals, ms)
    (f, fty) = insertImplicits(pre, f, fty, ctx.len, ms)
    let (dom, codBdy, impl, _) = ensurePi(ms, pre.loc, fty, ctx.len)
    if impl:
      raise elabErr(pre.loc,
        "cannot apply explicitly to an implicit argument")
    let a = checkTm(pre.c2, ctx, globals, ms, dom)
    (tmApp(f, a), subst(codBdy, 0, a))
  of pkPair:
    # Non-dependent Sigma with metavariable components (as the core's cPair).
    let aM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
    let bM = freshMeta(ms, tmC(cStar), ctx.len, 0, pre.loc)
    let a = checkTm(pre.c1, ctx, globals, ms, aM)
    let b = checkTm(pre.c2, ctx, globals, ms, bM)
    (tmPair(a, b, "_", weaken(bM)), tmSi(aM, "_", weaken(bM)))
  of pkFst:
    let (p, pty) = inferTm(pre.c1, ctx, globals, ms)
    let (dom, _, _) = ensureSi(ms, pre.loc, pty, ctx.len)
    (tmFst(p), dom)
  of pkSnd:
    let (p, pty) = inferTm(pre.c1, ctx, globals, ms)
    let (_, codBdy, _) = ensureSi(ms, pre.loc, pty, ctx.len)
    (tmSnd(p), subst(codBdy, 0, tmFst(p)))
  of pkLet:
    let (v, vty) =
      if pre.c1.isNil: inferTm(pre.c2, ctx, globals, ms)
      else:
        let aty = checkTm(pre.c1, ctx, globals, ms, tmC(cStar))
        (checkTm(pre.c2, ctx, globals, ms, aty), aty)
    let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, vty), globals, ms)
    (tmLet(v, vty, pre.name, b), subst(bty, 0, v))
  of pkAnn:
    let ty = checkTm(pre.c2, ctx, globals, ms, tmC(cStar))
    (checkTm(pre.c1, ctx, globals, ms, ty), ty)

proc checkTm(pre: PreTerm, ctx: Ctx, globals: Globals,
             ms: var MetaStore, expTy: Term): Term =
  ## Checking mode against an expected type.
  case pre.kind
  of pkLam:
    let (dom, codBdy, _, _) = ensurePi(ms, pre.loc, expTy, ctx.len)
    let d =
      if pre.c1.isNil: dom
      else:
        let ad = checkTm(pre.c1, ctx, globals, ms, tmC(cStar))
        unifyElab(ms, ad, dom, pre.loc)
        ad
    let b = checkTm(pre.c2, ctx.ext(pre.name, d), globals, ms, codBdy)
    tmLam(d, pre.name, b, pre.impl)
  of pkPair:
    let h = headTy(ms, expTy)
    if h.kind == tSi:
      let a = checkTm(pre.c1, ctx, globals, ms, h.dom)
      let b = checkTm(pre.c2, ctx, globals, ms, subst(h.scope.bdy, 0, a))
      tmPair(a, b, h.scope.adv, h.scope.bdy)
    elif h.kind == tMeta:
      let (dom, codBdy, adv) = ensureSi(ms, pre.loc, expTy, ctx.len)
      let a = checkTm(pre.c1, ctx, globals, ms, dom)
      let b = checkTm(pre.c2, ctx, globals, ms, subst(codBdy, 0, a))
      tmPair(a, b, adv, codBdy)
    else:
      raise elabErr(pre.loc, "pair " & $pre &
        " checked against a non-Sigma type")
  of pkLet:
    if pre.c1.isNil:
      let (v, vty) = inferTm(pre.c2, ctx, globals, ms)
      let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, vty), globals, ms)
      unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
      tmLet(v, vty, pre.name, b)
    else:
      let aty = checkTm(pre.c1, ctx, globals, ms, tmC(cStar))
      let v = checkTm(pre.c2, ctx, globals, ms, aty)
      let (b, bty) = inferTm(pre.c3, ctx.ext(pre.name, aty), globals, ms)
      unifyElab(ms, subst(bty, 0, v), expTy, pre.loc)
      tmLet(v, aty, pre.name, b)
  of pkAnn:
    let ty = checkTm(pre.c2, ctx, globals, ms, tmC(cStar))
    let t = checkTm(pre.c1, ctx, globals, ms, ty)
    unifyElab(ms, ty, expTy, pre.loc)
    t
  else:
    let (t, ty) = inferTm(pre, ctx, globals, ms)
    try:
      unify(ms, ty, expTy, pre.loc)
    except UnifyError as e:
      raise elabErr(pre.loc, "inferred type " & $zonk(ms, ty) &
        " does not match expected type " & $zonk(ms, expTy) & ": " & e.msg)
    t

type
  ElabDef* = object
    name*: string
    tyTm*: Term
    tmTm*: Term
    loc*: Loc

proc elabCheck*(src: string): seq[ElabDef] =
  ## Parse, elaborate, and typecheck a surface program, def by def.
  ## Later defs may mention earlier ones (via closed R nodes).
  ## Raises ParseError (carries loc) or ElabError (carries loc).
  let defs = parseProgram(src)
  var globals: Globals = initTable[string, GEntry]()
  var supply = Supply()
  var ms = initMetaStore()
  for d in defs:
    # 1. elaborate the type; it must be a type and contain no metas
    let (tyTm0, tyTy) = inferTm(d.desugarTy(), @[], globals, ms)
    unifyElab(ms, tyTy, tmC(cStar), d.loc)
    let tyT = zonk(ms, tyTm0)
    let ru = findUnsolved(ms, tyT)
    if ru.found:
      raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
        " in the type of '" & d.name & "'")
    let tyV =
      try: check(supply, vStar(), tyT)
      except ValueError as e:
        raise elabErr(d.loc,
          "ill-formed type of '" & d.name & "': " & e.msg)
    # 2. elaborate the body against the type; zonk; reject leftovers
    let tmT0 = checkTm(d.desugarTm(), @[], globals, ms, tyT)
    let tmT = zonk(ms, tmT0)
    let ru2 = findUnsolved(ms, tmT)
    if ru2.found:
      raise elabErr(ru2.loc, "unsolved metavariable ?m" & $ru2.id &
        " in the definition of '" & d.name & "'")
    # 3. the core verifies the zonked (meta-free) terms
    let tmV =
      try: check(supply, tyV, tmT)
      except ValueError as e:
        raise elabErr(d.loc, "definition '" & d.name &
          "' does not check against its declared type: " & e.msg &
          "\n  expected: " & $d.desugarTy() &
          "\n  body:     " & $d.desugarTm())
    if d.name in globals:
      raise elabErr(d.loc, "duplicate definition '" & d.name & "'")
    globals[d.name] = GEntry(tm: newDefRef(supply, tyV, tmV), ty: tyT)
    result.add(ElabDef(name: d.name, tyTm: tyT, tmTm: tmT, loc: d.loc))

when isMainModule:
  # --- Experiment 2's programs still elaborate --------------------------------
  let defs = elabCheck("""
def twice (A : ?) (f : A -> A) (x : A) : A :=
  f (f x)
def constFn (A : ?) (B : ?) (x : A) (y : B) : A :=
  x
def pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A :=
  (snd p, fst p)
""")
  assert defs.len == 3
  echo "ok: twice, constFn, pairSwap elaborate and check"

  let defs2 = elabCheck("""
def myId (A : ?) (x : A) : A :=
  x
def useId (A : ?) (x : A) : A :=
  myId A x
""")
  assert defs2.len == 2
  echo "ok: later defs can mention earlier defs"

  let defs3 = elabCheck("""
def withLet (A : ?) (x : A) : A :=
  let y : A = x in y
""")
  assert defs3.len == 1
  echo "ok: annotated let elaborates"

  # --- Experiment 3: implicit arguments inferred -------------------------------
  let defs4 = elabCheck("""
def polyId {A : ?} (x : A) : A :=
  x
def usePolyId : 1 :=
  polyId <>
def constI {A : ?} {B : ?} (x : A) (y : B) : A :=
  x
def useConstI : 1 :=
  constI <> <>
def pairSwapI {A : ?} {B : ?} (p : Sig (u : A). B) : Sig (v : B). A :=
  (snd p, fst p)
def usePairSwapI : Sig (v : 1). 1 :=
  pairSwapI (<>, <>)
""")
  assert defs4.len == 6
  echo "ok: implicit arguments inferred for polyId, constI, pairSwapI"

  # --- Experiment 3: unannotated lambdas and lets infer ------------------------
  let defs5 = elabCheck("""
def idU : Pi (A : ?). A -> A :=
  lam A. lam x. x
def letU : 1 :=
  let f = lam x. x in f <>
""")
  assert defs5.len == 2
  echo "ok: unannotated lambda and unannotated let infer"

  # --- failures carry surface locations ---------------------------------------
  proc expectElabErr(src: string, frag: string) =
    try:
      discard elabCheck(src)
      assert false, "expected ElabError for: " & src
    except ElabError as e:
      assert frag in e.msg, "missing '" & frag & "' in: " & e.msg
      assert e.loc.line > 0
      echo "ok: ElabError [" & frag & "] at line " & $e.loc.line &
        ", col " & $e.loc.col & ": " & e.msg.splitLines()[0]

  expectElabErr("def bad (A : ?) (x : A) : A :=\n  1\n",
    "does not match expected type")
  expectElabErr("def bad : ? :=\n  x\n", "unbound variable 'x'")
  expectElabErr("def bad : 1 :=\n  (<>, <>)\n",
    "checked against a non-Sigma type")
  expectElabErr("def bad (A : ?) (p : Sig (u : A). A) : ? :=\n  fst (snd p, fst p)\n",
    "cannot unify")
  expectElabErr("def bad (A : ?) : ? :=\n  _\n",
    "unsolved metavariable")
  expectElabErr("def bad : ? :=\n  lam x. x x\n",
    "expected a function type")
  expectElabErr("def bad : 1 :=\n  polyIdBad <>\n",
    "unbound variable 'polyIdBad'")

  # --- annotated surface lambdas elaborate; mismatches caught by check --------
  let defs6 = elabCheck("""
def constLam : Pi (A : ?) . A -> A :=
  lam (A : ?) . lam (x : A) . x
""")
  assert defs6.len == 1
  echo "ok: annotated surface lambda elaborates"
  expectElabErr("def bad : ? :=\n  lam (x : ?) . x\n",
    "expected a function type")

  # --- parse errors propagate with locations ----------------------------------
  try:
    discard elabCheck("def bad (A : ?) : :=\n  x\n")
    assert false, "expected ParseError"
  except ParseError as e:
    assert e.loc.line > 0
    echo "ok: ParseError at line " & $e.loc.line & ": " & e.msg.splitLines()[0]

  echo "--- all elaborator tests passed ---"
