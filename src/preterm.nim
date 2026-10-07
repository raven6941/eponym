# preterm.nim — surface preterms for Experiment 1.
#
# Named binders + source locations. Both front ends (the string-literal
# parser in parse_surf.nim and the Nim-AST macro in mac_surf.nim)
# produce these; Experiment 2 will elaborate them to ett_init.Term.
#
# Representation: flat ref object with three child slots whose meaning
# depends on `kind` (documented per constructor). Client code should
# only use the mk* constructors, never touch c1/c2/c3 directly.

type
  Loc* = object
    line*: int
    col*: int

  PreKind* = enum
    pkVar, pkUniv,                 # x, ?
    pkUnitTy, pkUnitV, pkEmptyTy,  # 1, <>, O
    pkPi, pkLam, pkApp,            # Pi, lam, application
    pkSigma, pkPair, pkFst, pkSnd, # Sig, pairs, projections
    pkLet, pkAnn,                  # let, ascription
    pkHole,                       # _ (Experiment 3: elaborator hole)
    pkInt,                        # integer literal (Experiment 11)
    pkBy                          # by tactic (Experiment 6)

  PreTerm* = ref object
    loc*: Loc
    kind*: PreKind
    name*: string     # pkVar name; binder name for pkPi/pkSigma/pkLam/pkLet
    impl*: bool       # pkPi/pkLam: implicit binder (Experiment 3)
    erased*: bool     # pkPi/pkLam/pkSigma: erased binder (Experiment 9)
    intVal*: int      # pkInt: the literal value (Experiment 11)
    c1*: PreTerm      # Pi/Sig: dom; Lam: binder type (may be nil); App: fn
                      # Pair: first; Fst/Snd: target; Let: annotation (may be nil)
                      # Ann: the term
    c2*: PreTerm      # Pi/Sig: cod; Lam: body; App: arg; Pair: second
                      # Let: value; Ann: the type
    c3*: PreTerm      # Let: body

const noLoc* = Loc(line: 0, col: 0)

# --- constructors ----------------------------------------------------

proc mkVar*(name: string, loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkVar, name: name)
proc mkUniv*(loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkUniv)
proc mkUnitTy*(loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkUnitTy)
proc mkUnitV*(loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkUnitV)
proc mkEmptyTy*(loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkEmptyTy)
proc mkPi*(binder: string, dom, cod: PreTerm, loc = noLoc,
           impl = false, erased = false): PreTerm =
  PreTerm(loc: loc, kind: pkPi, name: binder, impl: impl, erased: erased, c1: dom, c2: cod)
proc mkArrow*(dom, cod: PreTerm, loc = noLoc): PreTerm =
  ## Non-dependent function type; renders as `dom -> cod`.
  mkPi("_", dom, cod, loc)
proc mkLam*(binder: string, ty, body: PreTerm, loc = noLoc,
            impl = false, erased = false): PreTerm =
  PreTerm(loc: loc, kind: pkLam, name: binder, impl: impl, erased: erased, c1: ty, c2: body)
proc mkApp*(fn, arg: PreTerm, loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkApp, c1: fn, c2: arg)
proc mkSigma*(binder: string, dom, cod: PreTerm, loc = noLoc,
              erased = false): PreTerm =
  PreTerm(loc: loc, kind: pkSigma, name: binder, erased: erased, c1: dom, c2: cod)
proc mkPair*(a, b: PreTerm, loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkPair, c1: a, c2: b)
proc mkFst*(p: PreTerm, loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkFst, c1: p)
proc mkSnd*(p: PreTerm, loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkSnd, c1: p)
proc mkLet*(name: string, ann, val, body: PreTerm, loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkLet, name: name, c1: ann, c2: val, c3: body)
proc mkAnn*(e, ty: PreTerm, loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkAnn, c1: e, c2: ty)
proc mkHole*(loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkHole)
proc mkInt*(n: int, loc = noLoc): PreTerm =
  PreTerm(loc: loc, kind: pkInt, intVal: n)

# --- structural equality (ignores source locations) ------------------

proc `==`*(a, b: PreTerm): bool =
  if a.isNil and b.isNil: return true
  if a.isNil or b.isNil: return false
  a.kind == b.kind and a.name == b.name and a.impl == b.impl and
    a.erased == b.erased and a.intVal == b.intVal and
    a.c1 == b.c1 and a.c2 == b.c2 and a.c3 == b.c3

# --- rendering (canonical surface syntax) ----------------------------

proc render(p: PreTerm, prec: int): string

proc par(s: string): string = "(" & s & ")"

proc render(p: PreTerm, prec: int): string =
  ## prec: 0 top, 1 arrow, 2 application, 3 atom.
  case p.kind
  of pkVar: p.name
  of pkHole: "_"
  of pkInt: $p.intVal
  of pkBy: "by " & p.name
  of pkUniv: "?"
  of pkUnitTy: "1"
  of pkUnitV: "<>"
  of pkEmptyTy: "O"
  of pkPi:
    let s =
      if p.name == "_" and not p.impl: render(p.c1, 2) & " -> " & render(p.c2, 1)
      elif p.impl: "Pi {" & p.name & " : " & render(p.c1, 0) & "}. " & render(p.c2, 0)
      else: "Pi (" & p.name & " : " & render(p.c1, 0) & "). " & render(p.c2, 0)
    if prec > 1: par(s) else: s
  of pkSigma:
    let s = "Sig (" & p.name & " : " & render(p.c1, 0) & "). " & render(p.c2, 0)
    if prec > 0: par(s) else: s
  of pkLam:
    let b = if p.c1.isNil: p.name else: p.name & " : " & render(p.c1, 0)
    let s =
      if p.impl: "lam {" & b & "}. " & render(p.c2, 0)
      else: "lam (" & b & "). " & render(p.c2, 0)
    if prec > 0: par(s) else: s
  of pkApp:
    let s = render(p.c1, 2) & " " & render(p.c2, 3)
    if prec > 2: par(s) else: s
  of pkPair:
    "(" & render(p.c1, 0) & ", " & render(p.c2, 0) & ")"
  of pkFst, pkSnd:
    let s = (if p.kind == pkFst: "fst " else: "snd ") & render(p.c1, 3)
    if prec > 2: par(s) else: s
  of pkLet:
    let a = if p.c1.isNil: "" else: " : " & render(p.c1, 0)
    let s = "let " & p.name & a & " = " & render(p.c2, 0) &
      " in " & render(p.c3, 0)
    if prec > 0: par(s) else: s
  of pkAnn:
    "(" & render(p.c1, 0) & " : " & render(p.c2, 0) & ")"

proc `$`*(p: PreTerm): string = render(p, 0)

# --- top-level definitions -------------------------------------------

type
  SurfDef* = object
    ## A surface definition: `def name (x1 : T1) ... : Ret = body`.
    ## Telescope entries may be implicit (`{x : T}`) or erased (`(0 x : T)`).
    name*: string
    tele*: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool]]
    retTy*: PreTerm
    body*: PreTerm
    loc*: Loc

  DeclKind* = enum dkDef, dkPostulate, dkElim, dkRed, dkData
  DataCtor* = object
    ## One constructor in a `data` declaration.
    name*: string
    tele*: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool]]
    retTy*: PreTerm   # F params indices
    cloc*: Loc
  SurfDecl* = object
    ## A top-level declaration (Experiment 4 adds postulate/elim/red;
    ## Experiment 5 adds data).
    case kind*: DeclKind
    of dkDef: def*: SurfDef
    of dkPostulate, dkElim:
      name*: string
      ty*: PreTerm
      dloc*: Loc
    of dkRed:
      lhs*: PreTerm   # application pattern: elim v1..v(k-1) (ctor w1..wm)
      rhs*: PreTerm   # contractum template
      rloc*: Loc
    of dkData:
      dname*: string
      params*: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool]]
      indexTy*: PreTerm  # indices -> ?  (e.g. Nat -> ?)
      ctors*: seq[DataCtor]
      daloc*: Loc

proc desugarTy*(d: SurfDef): PreTerm =
  ## Telescope to nested Pis (implicit entries to implicit Pis).
  result = d.retTy
  for i in countdown(d.tele.high, 0):
    result = mkPi(d.tele[i].name, d.tele[i].ty, result, d.loc, d.tele[i].impl)

proc desugarTm*(d: SurfDef): PreTerm =
  ## Telescope to nested lambdas (implicit entries to implicit lambdas).
  result = d.body
  for i in countdown(d.tele.high, 0):
    result = mkLam(d.tele[i].name, d.tele[i].ty, result, d.loc, d.tele[i].impl)

proc `$`*(d: SurfDef): string =
  result = "def " & d.name
  for b in d.tele:
    if b.impl: result &= " {" & b.name & " : " & $b.ty & "}"
    else: result &= " (" & b.name & " : " & $b.ty & ")"
  result &= " : " & $d.retTy & " =\n  " & $d.body

# --- tests ------------------------------------------------------------

when isMainModule:
  let twiceTy = mkPi("A", mkUniv(), mkArrow(mkArrow(mkVar("A"), mkVar("A")),
                                          mkArrow(mkVar("A"), mkVar("A"))))
  assert $twiceTy == "Pi (A : ?). (A -> A) -> A -> A"
  let p = mkApp(mkVar("f"), mkApp(mkVar("f"), mkVar("x")))
  assert $p == "f (f x)"
  assert mkVar("x") == mkVar("x")
  assert mkVar("x") != mkVar("y")
  assert mkPi("A", mkUniv(), mkVar("A")) != mkPi("B", mkUniv(), mkVar("A"))
  assert $(mkLet("z", nil, mkVar("x"), mkVar("z"))) == "let z = x in z"
  assert $(mkPair(mkVar("a"), mkVar("b"))) == "(a, b)"
  let d = SurfDef(name: "const", tele: @[(name: "A", ty: mkUniv(), impl: false),
                                         (name: "x", ty: mkVar("A"), impl: false)],
                  retTy: mkVar("A"), body: mkVar("x"))
  assert $d.desugarTy() == "Pi (A : ?). Pi (x : A). A"
  assert $d.desugarTm() == "lam (A : ?). lam (x : A). x"
  echo "preterm: all tests passed"
