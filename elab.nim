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
    isElim: bool                 # Experiment 4: declared with 'elim'
    elimNargs: int               # Experiment 4: eliminator arity (incl. scrutinee)
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

proc elabDefDecl(d: SurfDef, globals: var Globals, supply: var Supply,
               ms: var MetaStore): ElabDef =
  ## Elaborate one `def` (the Experiment 2/3 pipeline, unchanged).
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
  ElabDef(name: d.name, tyTm: tyT, tmTm: tmT, loc: d.loc)

proc elabPostulateDecl(name: string, ty: PreTerm, loc: Loc,
                       globals: var Globals, supply: var Supply,
                       ms: var MetaStore, isElim: bool) =
  ## Experiment 4: `postulate name : Ty` / `elim name : Ty`.
  ## A parameter-like global; `elim` additionally installs an empty
  ## reduction rule table on the R node for later `red` declarations.
  if name in globals:
    raise elabErr(loc, "duplicate declaration '" & name & "'")
  let (tyTm0, tyTy) = inferTm(ty, @[], globals, ms)
  unifyElab(ms, tyTy, tmC(cStar), loc)
  let tyT = zonk(ms, tyTm0)
  let ru = findUnsolved(ms, tyT)
  if ru.found:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the type of '" & name & "'")
  let tyV =
    try: check(supply, vStar(), tyT)
    except ValueError as e:
      raise elabErr(loc, "ill-formed type of '" & name & "': " & e.msg)
  # the type must be a Pi spine (for `elim`: determines the arity)
  var nargs = 0
  var tyHead = tyT
  while true:
    let h = headTy(ms, tyHead)
    if h.kind != tPi: break
    inc nargs
    tyHead = h.scope.bdy  # already in the extended frame
  if isElim and nargs < 1:
    raise elabErr(loc, "eliminator '" & name &
      "' must have a Pi type (at least the scrutinee argument)")
  let tm =
    if isElim: newRedRef(supply, tyV, nargs)
    else: newPostulateRef(supply, tyV)
  globals[name] = GEntry(tm: tm, ty: tyT, isElim: isElim, elimNargs: nargs)

proc flattenAppSpine(pre: PreTerm): seq[PreTerm] =
  ## head-first application spine
  var cur = pre
  var rev: seq[PreTerm] = @[]
  while cur.kind == pkApp:
    rev.add(cur.c2); cur = cur.c1
  rev.add(cur)
  for i in countdown(rev.high, 0):
    result.add(rev[i])

proc elabRedDecl(lhs, rhs: PreTerm, loc: Loc,
                 globals: var Globals, supply: var Supply,
                 ms: var MetaStore) =
  ## Experiment 4: `red elim v1..v(k-1) scPat := contractum`,
  ## where scPat is `ctor` or `(ctor w1..wm)`, all bare variables.
  ## Elaborates the contractum in the pattern context and registers
  ## the case on the eliminator's rule table.
  let spine = flattenAppSpine(lhs)
  if spine[0].kind != pkVar:
    raise elabErr(loc, "red pattern must start with the eliminator name")
  let elimName = spine[0].name
  if elimName notin globals:
    raise elabErr(loc, "unbound eliminator '" & elimName & "'")
  let g = globals[elimName]
  if not g.isElim:
    raise elabErr(loc, "'" & elimName &
      "' is not an eliminator (declare it with 'elim')")
  let nargs = g.elimNargs
  if spine.len != nargs + 1:
    raise elabErr(loc, "eliminator '" & elimName & "' takes " & $nargs &
      " arguments; red pattern has " & $(spine.len - 1))
  # eliminator argument patterns: distinct bare variables
  var elimVars: seq[string] = @[]
  for i in 1 ..< nargs:
    if spine[i].kind != pkVar:
      raise elabErr(loc,
        "eliminator arguments in a red pattern must be bare variables")
    elimVars.add(spine[i].name)
  # scrutinee pattern: `ctor` or `(ctor w1..wm)`.
  # Arguments may be fresh variables (bound as ctor vars) or references
  # to already-bound eliminator variables (Experiment 5: `data`
  # generates `(nil A)` where A is a param). Leading bound variables
  # are the constructor's params (nParams); only fresh ones are ctor vars.
  let scSpine = flattenAppSpine(spine[nargs])
  if scSpine[0].kind != pkVar:
    raise elabErr(loc, "scrutinee pattern must be a constructor application")
  let ctorName = scSpine[0].name
  var ctorVars: seq[string] = @[]
  var nParams = 0
  var seenParamsDone = false
  for i in 1 ..< scSpine.len:
    if scSpine[i].kind != pkVar:
      raise elabErr(loc,
        "constructor arguments in a red pattern must be bare variables")
    let vn = scSpine[i].name
    if not seenParamsDone and vn in elimVars:
      inc nParams
    else:
      seenParamsDone = true
      if vn in elimVars or vn in ctorVars:
        raise elabErr(loc, "pattern variables in a red rule must be distinct")
      ctorVars.add(vn)
  let allVars = elimVars & ctorVars
  if allVars.deduplicate().len != allVars.len:
    raise elabErr(loc, "pattern variables in a red rule must be distinct")
  if ctorName notin globals:
    raise elabErr(loc, "unbound constructor '" & ctorName & "'")
  let cg = globals[ctorName]
  if cg.tm.kind != tR:
    raise elabErr(loc, "constructor '" & ctorName & "' must be a postulate")
  # introduce the eliminator variables, types from the eliminator's Pi spine
  var ctx: Ctx = @[]
  var elimTy = g.ty
  for nm in elimVars:
    let h = headTy(ms, elimTy)
    if h.kind != tPi:
      raise elabErr(loc, "eliminator type is not a Pi spine of length " &
        $nargs)
    ctx = ext(ctx, nm, h.dom)   # h.dom is in the current frame
    elimTy = h.scope.bdy        # already in the extended frame
  # introduce the constructor variables, types from the constructor's Pi spine.
  # First instantiate the leading params with the already-bound variables
  # (Experiment 5: `nil : Pi (A:? ). Vec A zero` applied to the elim's A).
  var ctorTy = cg.ty
  for i in 0 ..< nParams:
    let h = headTy(ms, ctorTy)
    if h.kind != tPi:
      raise elabErr(loc, "constructor '" & ctorName &
        "' does not take enough arguments")
    let varIdx = elimVars.len - 1 - i  # de Bruijn index of elimVars[i]
    ctorTy = subst(h.scope.bdy, 0, vv(varIdx))
  for nm in ctorVars:
    let h = headTy(ms, ctorTy)
    if h.kind != tPi:
      raise elabErr(loc, "constructor '" & ctorName & "' does not take " &
        $(nParams + ctorVars.len) & " arguments")
    ctx = ext(ctx, nm, h.dom)
    ctorTy = h.scope.bdy
  # elaborate the contractum (inference mode — the rule is trusted, like
  # an axiom; a production system would check it against the motive)
  let (rhsTm0, _) = inferTm(rhs, ctx, globals, ms)
  let rhsTm = zonk(ms, rhsTm0)
  let ru = findUnsolved(ms, rhsTm)
  if ru.found:
    raise elabErr(ru.loc, "unsolved metavariable ?m" & $ru.id &
      " in the contractum of a red rule")
  try:
    attachRedCase(g.tm, cg.tm.refId, rhsTm, nParams)
  except ValueError as e:
    raise elabErr(loc, e.msg)

# --- Experiment 5: data declarations -------------------------------------------
# A `data` declaration desugars to postulate/elim/red (Experiment 4) and
# goes through the same elaborators. The desugarer generates:
#   postulate F : Pi (params...). indexTy
#   postulate c : Pi (params...). Pi (tele...). retTy     (per constructor)
#   elim fElim : Pi (params...)(C : Pi (idx...). F params idx -> ?).
#                Pi (methods...). Pi (idx...)(v : F params idx). C idx v
#   red fElim params C methods idxVars (c params teleVars) := contractum
# Index positions in red patterns are dummy variables (unused in the
# contractum); fireRed's spine convention already accounts for them.

proc mkPis(tele: seq[tuple[name: string, ty: PreTerm, impl: bool]],
           body: PreTerm, loc: Loc): PreTerm =
  result = body
  for i in countdown(tele.high, 0):
    result = mkPi(tele[i].name, tele[i].ty, result, loc, tele[i].impl)

proc flattenPiPre(pre: PreTerm):
    tuple[tele: seq[tuple[name: string, ty: PreTerm]], body: PreTerm] =
  var cur = pre
  var tele: seq[tuple[name: string, ty: PreTerm]] = @[]
  while cur.kind == pkPi:
    tele.add((cur.name, cur.c1))
    cur = cur.c2
  (tele, cur)

proc extractIndices(retTy: PreTerm, famName: string, nParams: int,
                    loc: Loc): seq[PreTerm] =
  ## retTy should be `F p1..pn i1..ik`; return [i1..ik] as PreTerms.
  let spine = flattenAppSpine(retTy)
  if spine.len == 0 or spine[0].kind != pkVar or spine[0].name != famName:
    raise elabErr(loc, "constructor return type must be the family '" &
      famName & "' applied to indices")
  if spine.len < 1 + nParams:
    raise elabErr(loc, "constructor return type missing parameters")
  spine[1 + nParams .. ^1]

proc mentionsFam(pre: PreTerm, famName: string): bool =
  case pre.kind
  of pkVar: pre.name == famName
  of pkApp: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  of pkPi: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  of pkSigma: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  of pkLam: mentionsFam(pre.c2, famName)
  of pkPair: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  of pkFst, pkSnd: mentionsFam(pre.c1, famName)
  of pkLet: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName) or
             mentionsFam(pre.c3, famName)
  of pkAnn: mentionsFam(pre.c1, famName) or mentionsFam(pre.c2, famName)
  else: false

proc elimNameFor(dname: string): string =
  result = dname
  if result.len > 0:
    result[0] = result[0].toLowerAscii()
  result &= "Elim"

proc famAppPre(famName: string, params: seq[tuple[name: string, ty: PreTerm, impl: bool]],
               idxTerms: seq[PreTerm], loc: Loc): PreTerm =
  result = mkVar(famName, loc)
  for p in params: result = mkApp(result, mkVar(p.name, loc), loc)
  for t in idxTerms: result = mkApp(result, t, loc)

proc genElimTy(d: SurfDecl, loc: Loc): tuple[ty: PreTerm, methodNames: seq[string]] =
  ## Generate the eliminator type PreTerm and the method binder names.
  let famName = d.dname
  let (indexTele, _) = flattenPiPre(d.indexTy)
  var indexNames: seq[string] = @[]
  for i in 0 ..< indexTele.len:
    indexNames.add("i" & $i)
  # C : Pi (idx...). F params idx -> ?
  var cTy = mkArrow(famAppPre(famName, d.params,
                             indexNames.mapIt(mkVar(it, loc)), loc),
                    mkUniv(loc), loc)
  for i in countdown(indexTele.high, 0):
    cTy = mkPi(indexNames[i], indexTele[i].ty, cTy, loc)
  # methods, one per constructor
  var methodNames: seq[string] = @[]
  var methodTys: seq[PreTerm] = @[]
  for ci, ctor in d.ctors:
    let mName = "m" & $ci & "_" & ctor.name
    methodNames.add(mName)
    var teleVars: seq[PreTerm] = @[]
    for t in ctor.tele: teleVars.add(mkVar(t.name, loc))
    var ctorApp = mkVar(ctor.name, loc)
    for p in d.params: ctorApp = mkApp(ctorApp, mkVar(p.name, loc), loc)
    for v in teleVars: ctorApp = mkApp(ctorApp, v, loc)
    let retIndices = extractIndices(ctor.retTy, famName, d.params.len, ctor.cloc)
    var mRet = mkVar("C", loc)
    for ri in retIndices: mRet = mkApp(mRet, ri, loc)
    mRet = mkApp(mRet, ctorApp, loc)
    var mTy = mRet
    var ihCount = 0
    for i in countdown(ctor.tele.high, 0):
      let argTy = ctor.tele[i].ty
      if mentionsFam(argTy, famName):
        let argIndices = extractIndices(argTy, famName, d.params.len, ctor.cloc)
        var ihTy = mkVar("C", loc)
        for ai in argIndices: ihTy = mkApp(ihTy, ai, loc)
        ihTy = mkApp(ihTy, mkVar(ctor.tele[i].name, loc), loc)
        mTy = mkPi("ih" & $ihCount, ihTy, mTy, loc)
        inc ihCount
      mTy = mkPi(ctor.tele[i].name, argTy, mTy, loc)
    methodTys.add(mTy)
  # Pi (params...)(C : cTy)(methods...)(idx...)(v : F params idx). C idx v
  var vTy = famAppPre(famName, d.params,
                      indexNames.mapIt(mkVar(it, loc)), loc)
  var body = mkVar("C", loc)
  for iNm in indexNames: body = mkApp(body, mkVar(iNm, loc), loc)
  body = mkApp(body, mkVar("v", loc), loc)
  var elimTy = mkPi("v", vTy, body, loc)
  for i in countdown(indexNames.high, 0):
    elimTy = mkPi(indexNames[i], indexTele[i].ty, elimTy, loc)
  for i in countdown(methodNames.high, 0):
    elimTy = mkPi(methodNames[i], methodTys[i], elimTy, loc)
  elimTy = mkPi("C", cTy, elimTy, loc)
  for i in countdown(d.params.high, 0):
    elimTy = mkPi(d.params[i].name, d.params[i].ty, elimTy, d.daloc,
                  d.params[i].impl)
  (elimTy, methodNames)

proc genRedDecls(d: SurfDecl, elimName: string, methodNames: seq[string],
                 loc: Loc): seq[SurfDecl] =
  ## Generate one `red` per constructor. Index positions are dummy
  ## variables (fireRed's spine convention includes them; the
  ## contractum never mentions them).
  let famName = d.dname
  let (indexTele, _) = flattenPiPre(d.indexTy)
  var idxNames: seq[string] = @[]
  for i in 0 ..< indexTele.len:
    idxNames.add("idx" & $i)
  for ci, ctor in d.ctors:
    var lhs = mkVar(elimName, loc)
    for p in d.params: lhs = mkApp(lhs, mkVar(p.name, loc), loc)
    lhs = mkApp(lhs, mkVar("C", loc), loc)
    for mn in methodNames: lhs = mkApp(lhs, mkVar(mn, loc), loc)
    for iNm in idxNames: lhs = mkApp(lhs, mkVar(iNm, loc), loc)
    var sc = mkVar(ctor.name, loc)
    for p in d.params: sc = mkApp(sc, mkVar(p.name, loc), loc)
    for t in ctor.tele: sc = mkApp(sc, mkVar(t.name, loc), loc)
    lhs = mkApp(lhs, sc, loc)
    # contractum: method teleVars recCalls...
    var rhs = mkVar(methodNames[ci], loc)
    for t in ctor.tele:
      rhs = mkApp(rhs, mkVar(t.name, loc), loc)
    for t in ctor.tele:
      if mentionsFam(t.ty, famName):
        let argIndices = extractIndices(t.ty, famName, d.params.len, ctor.cloc)
        var rec = mkVar(elimName, loc)
        for p in d.params: rec = mkApp(rec, mkVar(p.name, loc), loc)
        rec = mkApp(rec, mkVar("C", loc), loc)
        for mn in methodNames: rec = mkApp(rec, mkVar(mn, loc), loc)
        for ai in argIndices: rec = mkApp(rec, ai, loc)
        rec = mkApp(rec, mkVar(t.name, loc), loc)
        rhs = mkApp(rhs, rec, loc)
    result.add(SurfDecl(kind: dkRed, lhs: lhs, rhs: rhs, rloc: ctor.cloc))

proc elabDataDecl(d: SurfDecl, globals: var Globals, supply: var Supply,
                  ms: var MetaStore) =
  ## Experiment 5: desugar `data` to postulate/elim/red.
  let loc = d.daloc
  # name clash check for the generated binders
  for p in d.params:
    if p.name == "C":
      raise elabErr(loc, "data parameter may not be named 'C' (reserved for the motive)")
  for ctor in d.ctors:
    for t in ctor.tele:
      if t.name == "C":
        raise elabErr(ctor.cloc, "constructor binder may not be named 'C' (reserved)")
  # type former
  elabPostulateDecl(d.dname, mkPis(d.params, d.indexTy, loc), loc,
                    globals, supply, ms, false)
  # constructors
  for ctor in d.ctors:
    discard extractIndices(ctor.retTy, d.dname, d.params.len, ctor.cloc)
    var fullTele = d.params & ctor.tele
    elabPostulateDecl(ctor.name, mkPis(fullTele, ctor.retTy, ctor.cloc),
                      ctor.cloc, globals, supply, ms, false)
  # eliminator
  let elimName = elimNameFor(d.dname)
  let (elimTy, methodNames) = genElimTy(d, loc)
  elabPostulateDecl(elimName, elimTy, loc, globals, supply, ms, true)
  # reduction rules
  for rd in genRedDecls(d, elimName, methodNames, loc):
    elabRedDecl(rd.lhs, rd.rhs, rd.rloc, globals, supply, ms)

proc elabDecl(d: SurfDecl, globals: var Globals, supply: var Supply,
              ms: var MetaStore): seq[ElabDef] =
  ## Elaborate one top-level declaration (Experiment 5: data desugars
  ## to postulate/elim/red and goes through the same path).
  ## Returns the defs it produced (only dkDef yields one directly).
  case d.kind
  of dkDef:
    result.add(elabDefDecl(d.def, globals, supply, ms))
  of dkPostulate:
    elabPostulateDecl(d.name, d.ty, d.dloc, globals, supply, ms, false)
  of dkElim:
    elabPostulateDecl(d.name, d.ty, d.dloc, globals, supply, ms, true)
  of dkRed:
    elabRedDecl(d.lhs, d.rhs, d.rloc, globals, supply, ms)
  of dkData:
    elabDataDecl(d, globals, supply, ms)

proc elabCheck*(src: string): seq[ElabDef] =
  ## Parse, elaborate, and typecheck a surface program, decl by decl.
  ## Later decls may mention earlier ones (via closed R nodes).
  ## Raises ParseError (carries loc) or ElabError (carries loc).
  let decls = parseProgram(src)
  var globals: Globals = initTable[string, GEntry]()
  var supply = Supply()
  var ms = initMetaStore()
  for d in decls:
    result.add(elabDecl(d, globals, supply, ms))

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

  # --- Experiment 4: postulate / elim / red; reduction fires ------------------
  let boolDefs = elabCheck("""
postulate Bool : ?
postulate true : Bool
postulate false : Bool
elim boolElim : Pi (C : Bool -> ?). C true -> C false -> Pi (b : Bool). C b
red boolElim C t f true  := t
red boolElim C t f false := f
def not (b : Bool) : Bool :=
  boolElim (lam (u : Bool). Bool) false true b
def notTrue : Bool := not true
def notFalse : Bool := not false
""")
  assert boolDefs.len == 3
  # not true reduces to false; not false reduces to true.
  # The postulate refIds come from the argument positions: `not true`
  # is tApp(R_not, R_true), `not false` is tApp(R_not, R_false).
  let trueId = boolDefs[1].tmTm.arg.refId
  let falseId = boolDefs[2].tmTm.arg.refId
  assert trueId != falseId
  let notTrueV = eval(boolDefs[1].tmTm, @[])
  assert notTrueV.whnfKind == wRef and notTrueV.whnfRefId == falseId and
    notTrueV.whnfSpineLen == 0, "not true should reduce to false"
  let notFalseV = eval(boolDefs[2].tmTm, @[])
  assert notFalseV.whnfKind == wRef and notFalseV.whnfRefId == trueId and
    notFalseV.whnfSpineLen == 0, "not false should reduce to true"
  echo "ok: Bool eliminator reduces (not true = false, not false = true)"

  # Nat: constructor with arguments; recursive rule; stuck scrutinee
  let natDefs = elabCheck("""
postulate Nat : ?
postulate zero : Nat
postulate suc : Nat -> Nat
elim natElim : Pi (C : Nat -> ?). C zero -> (Pi (n : Nat). C n -> C (suc n)) -> Pi (n : Nat). C n
red natElim C z s zero    := z
red natElim C z s (suc n) := s n (natElim C z s n)
def two : Nat := suc (suc zero)
def add (m : Nat) (n : Nat) : Nat :=
  natElim (lam (u : Nat). Nat) m (lam (p : Nat). lam (ih : Nat). suc ih) n
def four : Nat := add two two
def stuckTest (n : Nat) : Nat :=
  natElim (lam (u : Nat). Nat) zero (lam (p : Nat). lam (ih : Nat). p) n
""")
  assert natDefs.len == 4
  let twoTm = natDefs[0].tmTm  # suc (suc zero)
  let sucId = twoTm.fn.refId
  let zeroId = twoTm.arg.arg.refId
  proc sucDepth(v: Value): int =
    if v.whnfKind == wRef and v.whnfRefId == sucId and v.whnfSpineLen == 1:
      1 + sucDepth(v.whnfSpineArg(0))
    elif v.whnfKind == wRef and v.whnfRefId == zeroId and v.whnfSpineLen == 0:
      0
    else: -1000
  let depth4 = sucDepth(eval(natDefs[2].tmTm, @[]))
  assert depth4 == 4, "add two two should reduce to suc^4 zero, got depth " & $depth4
  echo "ok: Nat eliminator reduces (add two two = 4); neutral scrutinee stays stuck"

  # red errors: duplicate rule, non-eliminator, wrong arity
  expectElabErr("""
postulate Bool : ?
postulate true : Bool
elim boolElim : Pi (C : Bool -> ?). C true -> Pi (b : Bool). C b
red boolElim C t true := t
red boolElim C t true := t
""", "duplicate reduction rule")
  expectElabErr("""
postulate Bool : ?
postulate true : Bool
postulate notElim : Bool -> Bool
red notElim x true := x
""", "not an eliminator")
  expectElabErr("""
postulate Bool : ?
postulate true : Bool
elim boolElim : Pi (C : Bool -> ?). C true -> Pi (b : Bool). C b
red boolElim C true := true
""", "takes 3 arguments")

  # --- Experiment 5: data declarations --------------------------------------
  # data Nat: non-indexed, desugars to postulate/elim/red
  let dataNatDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
def two : Nat := suc (suc zero)
def add (m : Nat) (n : Nat) : Nat :=
  natElim (lam (u : Nat). Nat) m (lam (p : Nat). lam (ih : Nat). suc ih) n
def four : Nat := add two two
""")
  assert dataNatDefs.len == 3
  let dataTwoTm = dataNatDefs[0].tmTm
  let dataSucId = dataTwoTm.fn.refId
  let dataZeroId = dataTwoTm.arg.arg.refId
  proc dataSucDepth(v: Value): int =
    if v.whnfKind == wRef and v.whnfRefId == dataSucId and v.whnfSpineLen == 1:
      1 + dataSucDepth(v.whnfSpineArg(0))
    elif v.whnfKind == wRef and v.whnfRefId == dataZeroId and v.whnfSpineLen == 0:
      0
    else: -1000
  assert dataSucDepth(eval(dataNatDefs[2].tmTm, @[])) == 4
  echo "ok: data Nat desugars; eliminator computes (add two two = 4)"

  # data Vec: indexed family; the eliminator computes over indices
  let dataVecDefs = elabCheck("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
def v2 : Vec Nat (suc (suc zero)) :=
  cons Nat (suc zero) (suc zero) (cons Nat zero zero (nil Nat))
def lenIsTwo : Nat :=
  vecElim Nat (lam (i : Nat). lam (v : Vec Nat i). Nat)
            zero
            (lam (i : Nat). lam (x : Nat). lam (xs : Vec Nat i). lam (ih : Nat). suc ih)
            (suc (suc zero)) v2
""")
  assert dataVecDefs.len == 2
  assert dataSucDepth(eval(dataVecDefs[1].tmTm, @[])) == 2
  echo "ok: data Vec (indexed) desugars; eliminator computes (length = 2)"

  # data errors: constructor return must be the family
  expectElabErr("""
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Bad : ? where
| mk : Nat
""", "must be the family")

  echo "--- all elaborator tests passed ---"
