## Experiment 2: elaborator from named surface preterms to de Bruijn core terms.
##
## Two modes, following the bidirectional typing recipe (Dunfield & Krishnaswami):
##   elab    -- synthesis mode; produces a Term with no expected type.
##   elabChk -- checking mode against an expected *Term*; exists only to supply
##              the Sigma range for surface pairs (and Pi domains for lambdas),
##              which synthesis cannot invent. Verification stays with the core:
##              elabCheck runs check() on the final closed terms, so every
##              accepted program is genuinely well-typed in ETT.
##
## Known Experiment 2 limits (see decisions.org):
## - A pair must be checked against a known Sigma type; elaboration cannot
##   infer the range of `(a, b)` from the components alone.
## - Unannotated lambdas and lets are rejected in synthesis mode (Experiment 3:
##   full bidirectional elaboration with inference).
## - Ascriptions guide elaboration but nested ones are not separately verified
##   against their ascribed type; the def-level check still applies.

import tables
import strutils
import preterm
import parse_surf
import ett_init

type
  ElabError* = object of CatchableError
    loc*: Loc

proc elabErr(loc: Loc, msg: string): ref ElabError =
  let e = newException(ElabError,
    "line " & $loc.line & ", col " & $loc.col & ": " & msg)
  e.loc = loc
  e

type
  Ctx = seq[string]              # innermost-first binder names
  Globals = Table[string, Term]  # earlier defs, as closed R nodes

proc ext(ctx: Ctx, name: string): Ctx = @[name] & ctx

proc resolveVar(ctx: Ctx, globals: Globals, name: string, loc: Loc): Term =
  for i, n in ctx:
    if n == name: return vv(i)
  if name in globals: return globals[name]
  raise elabErr(loc, "unbound variable '" & name & "'")

proc elab(pre: PreTerm, ctx: Ctx, globals: Globals): Term
proc elabChk(pre: PreTerm, ctx: Ctx, globals: Globals, exp: Term): Term

proc elab(pre: PreTerm, ctx: Ctx, globals: Globals): Term =
  ## Synthesis mode: elaborate without an expected type.
  case pre.kind
  of pkVar:
    resolveVar(ctx, globals, pre.name, pre.loc)
  of pkUniv: tmC(cStar)
  of pkUnitTy: tmC(cOne)
  of pkUnitV: tmC(cVoid)
  of pkEmptyTy: tmC(cZero)
  of pkPi:
    tmPi(elab(pre.c1, ctx, globals), pre.name,
         elab(pre.c2, ctx.ext(pre.name), globals))
  of pkSigma:
    tmSi(elab(pre.c1, ctx, globals), pre.name,
         elab(pre.c2, ctx.ext(pre.name), globals))
  of pkLam:
    if pre.c1.isNil:
      raise elabErr(pre.loc, "cannot elaborate unannotated lambda '" &
        pre.name & "'; annotate it or check it against a known Pi type")
    tmLam(elab(pre.c1, ctx, globals), pre.name,
          elab(pre.c2, ctx.ext(pre.name), globals))
  of pkApp:
    tmApp(elab(pre.c1, ctx, globals), elab(pre.c2, ctx, globals))
  of pkPair:
    raise elabErr(pre.loc, "cannot infer the type of a pair " &
      $pre & "; it must be checked against a known Sigma type")
  of pkFst: tmFst(elab(pre.c1, ctx, globals))
  of pkSnd: tmSnd(elab(pre.c1, ctx, globals))
  of pkLet:
    if pre.c1.isNil:
      raise elabErr(pre.loc, "let '" & pre.name &
        "' needs a type annotation in Experiment 2")
    tmLet(elab(pre.c2, ctx, globals), elab(pre.c1, ctx, globals), pre.name,
          elab(pre.c3, ctx.ext(pre.name), globals))
  of pkAnn:
    elabChk(pre.c1, ctx, globals, elab(pre.c2, ctx, globals))

proc elabChk(pre: PreTerm, ctx: Ctx, globals: Globals, exp: Term): Term =
  ## Checking mode: elaborate against an expected type Term.
  ## The expected type only *guides* elaboration (pair ranges, lambda domains);
  ## the core's check() still verifies the result.
  case pre.kind
  of pkPair:
    if exp.kind != tSi:
      raise elabErr(pre.loc, "pair " & $pre &
        " checked against a non-Sigma type")
    # The expected Sigma's scope is already in the right de Bruijn frame for
    # the pair's range: one fresh binder over the current context.
    tmPair(elab(pre.c1, ctx, globals), elab(pre.c2, ctx, globals),
           exp.scope.adv, exp.scope.bdy)
  of pkLam:
    if exp.kind != tPi:
      return elab(pre, ctx, globals)  # fall back to the annotation
    let domT =
      if pre.c1.isNil: exp.dom
      else: elab(pre.c1, ctx, globals)
    tmLam(domT, pre.name,
          elabChk(pre.c2, ctx.ext(pre.name), globals, exp.scope.bdy))
  of pkAnn:
    elabChk(pre.c1, ctx, globals, elab(pre.c2, ctx, globals))
  else:
    elab(pre, ctx, globals)

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
  var globals: Globals = initTable[string, Term]()
  var supply = Supply()
  for d in defs:
    let tyT = elab(d.desugarTy(), @[], globals)
    let tyV =
      try: check(supply, vStar(), tyT)
      except ValueError as e:
        raise elabErr(d.loc,
          "ill-formed type of '" & d.name & "': " & e.msg)
    let tmT = elabChk(d.desugarTm(), @[], globals, tyT)
    let tmV =
      try: check(supply, tyV, tmT)
      except ValueError as e:
        raise elabErr(d.loc, "definition '" & d.name &
          "' does not check against its declared type: " & e.msg &
          "\n  expected: " & $d.desugarTy() &
          "\n  body:     " & $d.desugarTm())
    if d.name in globals:
      raise elabErr(d.loc, "duplicate definition '" & d.name & "'")
    globals[d.name] = newDefRef(supply, tyV, tmV)
    result.add(ElabDef(name: d.name, tyTm: tyT, tmTm: tmT, loc: d.loc))

when isMainModule:
  # --- Experiment 1's test programs elaborate and check -----------------------
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

  # --- cross-definition references --------------------------------------------
  let defs2 = elabCheck("""
def myId (A : ?) (x : A) : A :=
  x
def useId (A : ?) (x : A) : A :=
  myId A x
""")
  assert defs2.len == 2
  echo "ok: later defs can mention earlier defs"

  # --- let --------------------------------------------------------------------
  let defs3 = elabCheck("""
def withLet (A : ?) (x : A) : A :=
  let y : A = x in y
""")
  assert defs3.len == 1
  echo "ok: annotated let elaborates"

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
    "does not check against its declared type")
  expectElabErr("def bad : ? :=\n  x\n", "unbound variable 'x'")
  expectElabErr("def bad (A : ?) (p : Sig (u : A). A) : ? :=\n  fst (snd p, fst p)\n",
    "cannot infer the type of a pair")
  expectElabErr("def bad (A : ?) (x : A) : A :=\n  let y = x in y\n",
    "needs a type annotation")
  # --- annotated surface lambdas elaborate; mismatches caught by check --------
  let defs4 = elabCheck("""
def constLam : Pi (A : ?) . A -> A :=
  lam (A : ?) . lam (x : A) . x
""")
  assert defs4.len == 1
  echo "ok: annotated surface lambda elaborates"
  expectElabErr("def bad : ? :=\n  lam (x : ?) . x\n",
    "does not check against its declared type")

  # --- parse errors propagate with locations ----------------------------------
  try:
    discard elabCheck("def bad (A : ?) : :=\n  x\n")
    assert false, "expected ParseError"
  except ParseError as e:
    assert e.loc.line > 0
    echo "ok: ParseError at line " & $e.loc.line & ": " & e.msg.splitLines()[0]

  echo "--- all elaborator tests passed ---"
