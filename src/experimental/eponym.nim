#===============================================================================
# eponym.nim -- A finally-tagless interpreter for ETT, Epigram's Type Theory.
#
# Based on: Chapman, Altenkirch & McBride, "Epigram Reloaded: A Standalone
#           Typechecker for ETT" (TYPES 2006).
#
# ETT is "a rather spartan lambda-calculus with dependent types", the core
# language that Epigram's elaborator targets. From the paper (§6.4), its
# syntax is:
#
#   Term  ::= R Reference        (free var / definition; host-level here)
#           | V Int              (bound var, de Bruijn; host closures here)
#           | Pi Type Scope      (dependent function type)
#           | Si Type Scope      (dependent pair type)
#           | L Type Scope       (lambda, domain-annotated)
#           | P Term (Term,Scope)(pair, with its range type)
#           | Term :$ Elim Term  (eliminations: application, projections, OE)
#           | C Const            (Star | One | Void | Zero  i.e. Type 0 | 1 | <> | O)
#           | Let (Term,Type) Scope  (local definition [x |-> s:S]t)
#
# We use the finally-tagless style (Carette, Kiselyov & Shan): the language
# is an *interface* `Sym[R]` over an abstract representation type R, and each
# interpretation (evaluation, pretty-printing, typechecking, ...) is an
# *instance*. Object-language terms are written once, polymorphically in R,
# against the interface -- e.g. `twice` below is meaningful for *every*
# instance.
#
# Implementation note: the direct analogue of a Haskell typeclass in Nim is
# a `concept`, but concepts currently mishandle this combination of
# higher-order proc fields and a generic representation type (nested
# `proc(x: R): R` literals inside concept-dispatched calls fail to resolve
# R, and multi-line trailing proc arguments misparse). We therefore use the
# dictionary-passing desugaring of the same idea: `Sym[R]` is an object of
# closures, one per ETT construct. Semantically this is identical -- one
# interface, many interpretations, terms written once -- and it compiles.
#
# Consequences, true to the paper's architecture:
#  * binders use higher-order abstract syntax (host closures), so there is
#    no de Bruijn bookkeeping and no possibility of unbound variables;
#  * top-level definitions are just host procs (cf. the paper's R Reference
#    carrying a cached value);
#  * local definitions [x |-> s:S]t are plain beta-redexes (see `cLet`).
#
# ETT's *observational* equality rules (proof-irrelevance of 1 and O,
# eta for Pi/Sigma) govern definitional equality, hence typechecking --
# not evaluation -- so the evaluator below implements beta-reduction
# only. A typechecker instance (the paper's §§6.5-6.7) would follow the
# same interface; that is the natural next step before the elaborator.
#===============================================================================

## ---------------------------------------------------------------------------
## 1. The finally-tagless interface: ETT as a dictionary of closures
## ---------------------------------------------------------------------------

type
  Sym*[R] = object
    ## The universe of (small) types, `Type 0` (we follow the paper: Type 0:Type 0).
    cStar*: proc(): R
    ## The unit type `1` and its canonical inhabitant `<>`.
    cUnit*: proc(): R
    cTt*: proc(): R
    ## The empty type `O`.
    cEmpty*: proc(): R
    ## Dependent function type, lambda (domain-annotated, as in the paper)
    ## and application.
    cPi*: proc(dom: R, cod: proc(x: R): R): R
    cLam*: proc(dom: R, body: proc(x: R): R): R
    cApp*: proc(f, a: R): R
    ## Dependent pair type, pairing and the two projections.
    cSigma*: proc(dom: R, cod: proc(x: R): R): R
    cPair*: proc(a, b: R): R
    cFst*: proc(p: R): R
    cSnd*: proc(p: R): R
    ## Ex falso: the eliminator for O (the paper's postfix `OE`).
    cAbsurd*: proc(z: R): R

## ---------------------------------------------------------------------------
## 2. Derived combinators, valid for every instance
## ---------------------------------------------------------------------------

proc cArr*[R](s: Sym[R], dom, cod: R): R =
  ## Non-dependent arrow `dom -> cod`, derived from Pi.
  s.cPi(dom, proc(x: R): R = cod)

proc cLet[R](s: Sym[R], typ, val: R, body: proc(x: R): R): R =
  ## Local definition `[x |-> val:typ]body`, as a beta-redex.
  s.cApp(s.cLam(typ, body), val)

## ---------------------------------------------------------------------------
## 3. Instance 1: the interpreter (evaluation to weak-head normal form)
## ---------------------------------------------------------------------------

type
  ElimKind = enum ekApp, ekFst, ekSnd
  Elim = object
    ## A stuck elimination on a neutral head.
    case kind: ElimKind
    of ekApp: arg: Value
    else: discard
  VKind* = enum
    vkStar, vkUnit, vkTt, vkEmpty,   # constants: Type 0  1  <>  O
    vkPi, vkLam,                     # Pi-type and lambda (closures)
    vkSigma, vkPair,                 # Sigma-type and pair
    vkNeutral,                       # stuck variable + elimination spine
    vkNat                            # primitive natural number (staging experiments)
  Value* = ref object
    ## Run-time values. Binders are host closures, so evaluation is just
    ## host-language beta-reduction -- the "functional representation" half
    ## of the paper's glued values (§6.6), without the syntactic half.
    ## Neutrals (free variables with stuck spines) only arise when the
    ## typechecker evaluates open terms; closed-term evaluation never
    ## produces them.
    case kind*: VKind
    of vkPi, vkSigma:
      dom*: Value
      cod*: proc(x: Value): Value
    of vkLam:
      body*: proc(x: Value): Value
    of vkPair:
      fstV*, sndV*: Value
    of vkNeutral:
      neutId*: int
      spine*: seq[Elim]
    of vkNat:
      natV*: int
    else:
      discard

proc vApp(f, a: Value): Value =
  ## Weak-head application; stuck eliminations accumulate on neutrals.
  case f.kind
  of vkLam: f.body(a)  # beta
  of vkNeutral:
    var sp = f.spine
    sp.add(Elim(kind: ekApp, arg: a))
    Value(kind: vkNeutral, neutId: f.neutId, spine: sp)
  else:
    raise newException(ValueError, "stuck application")

proc vFst(p: Value): Value =
  case p.kind
  of vkPair: p.fstV
  of vkNeutral:
    var sp = p.spine
    sp.add(Elim(kind: ekFst))
    Value(kind: vkNeutral, neutId: p.neutId, spine: sp)
  else:
    raise newException(ValueError, "fst of non-pair")

proc vSnd(p: Value): Value =
  case p.kind
  of vkPair: p.sndV
  of vkNeutral:
    var sp = p.spine
    sp.add(Elim(kind: ekSnd))
    Value(kind: vkNeutral, neutId: p.neutId, spine: sp)
  else:
    raise newException(ValueError, "snd of non-pair")

let evalSym* = Sym[Value](
  cStar: proc(): Value = Value(kind: vkStar),
  cUnit: proc(): Value = Value(kind: vkUnit),
  cTt: proc(): Value = Value(kind: vkTt),
  cEmpty: proc(): Value = Value(kind: vkEmpty),
  cPi: proc(dom: Value, cod: proc(x: Value): Value): Value =
    Value(kind: vkPi, dom: dom, cod: cod),
  cLam: proc(dom: Value, body: proc(x: Value): Value): Value =
    Value(kind: vkLam, body: body),
  cApp: proc(f, a: Value): Value = vApp(f, a),
  cSigma: proc(dom: Value, cod: proc(x: Value): Value): Value =
    Value(kind: vkSigma, dom: dom, cod: cod),
  cPair: proc(a, b: Value): Value =
    Value(kind: vkPair, fstV: a, sndV: b),
  cFst: proc(p: Value): Value = vFst(p),
  cSnd: proc(p: Value): Value = vSnd(p),
  cAbsurd: proc(z: Value): Value =
    # No closed term inhabits O; reaching this is a stuck computation.
    raise newException(ValueError, "absurd: empty type has no closed values")
)

## ---------------------------------------------------------------------------
## 4. Instance 2: pretty-printer (proves the interface is really tagless:
##    the same terms below are reused unchanged for both instances)
## ---------------------------------------------------------------------------

type NameSupply = ref object
  next: int

proc newPrinter(): Sym[string] =
  let ns = NameSupply(next: 0)
  proc fresh(hint: string): string =
    result = hint & $ns.next
    inc ns.next
  Sym[string](
    cStar: proc(): string = "Type 0",
    cUnit: proc(): string = "1",
    cTt: proc(): string = "<>",
    cEmpty: proc(): string = "O",
    cPi: proc(dom: string, cod: proc(x: string): string): string =
      let x = fresh("x")
      "Pi " & x & " : " & dom & ". " & cod(x),
    cLam: proc(dom: string, body: proc(x: string): string): string =
      let x = fresh("x")
      "\\" & x & " : " & dom & ". " & body(x),
    cApp: proc(f, a: string): string =
      "(" & f & " " & a & ")",
    cSigma: proc(dom: string, cod: proc(x: string): string): string =
      let x = fresh("x")
      "Sigma " & x & " : " & dom & ". " & cod(x),
    cPair: proc(a, b: string): string =
      "<" & a & "; " & b & ">",
    cFst: proc(p: string): string = "(" & p & " .1)",
    cSnd: proc(p: string): string = "(" & p & " .2)",
    cAbsurd: proc(z: string): string = "(" & z & " absurd)"
  )

## ---------------------------------------------------------------------------
## 4b. Instance 2b: erasing code generator (Experiment 8: staging)
##
##    A Sym[string] that produces untyped lambda-calculus code by erasing
##    types. The same ETT term (e.g. `twice`) denotes a value under
##    `evalSym`, pretty syntax under `newPrinter`, and executable code
##    here — staging as just another interpretation (Carette/Kiselyov/Shan).
## ---------------------------------------------------------------------------

proc newCodeGen(): Sym[string] =
  let ns = NameSupply(next: 0)
  proc fresh(hint: string): string =
    result = hint & $ns.next
    inc ns.next
  Sym[string](
    # Types erase to a placeholder (no runtime representation)
    cStar: proc(): string = "/*: Type 0*/",
    cUnit: proc(): string = "/*: 1*/",
    cTt: proc(): string = "()",
    cEmpty: proc(): string = "/*: O*/",
    # Pi/Sigma erase; the domain is not represented at runtime
    cPi: proc(dom: string, cod: proc(x: string): string): string =
      let x = fresh("x")
      "/*Pi*/ " & cod(x),
    cLam: proc(dom: string, body: proc(x: string): string): string =
      let x = fresh("x")
      "(\\" & x & ". " & body(x) & ")",
    cApp: proc(f, a: string): string =
      "(" & f & " " & a & ")",
    cSigma: proc(dom: string, cod: proc(x: string): string): string =
      let x = fresh("x")
      "/*Sigma*/ " & cod(x),
    cPair: proc(a, b: string): string =
      "(" & a & ", " & b & ")",
    cFst: proc(p: string): string = "(fst " & p & ")",
    cSnd: proc(p: string): string = "(snd " & p & ")",
    cAbsurd: proc(z: string): string = "(absurd " & z & ")"
  )

## ---------------------------------------------------------------------------
## 5. Instance 3: the typechecker (bidirectional, after the paper §§6.5-6.7)
##
##    This is a *third* interpretation of the same Sym[R] interface:
##    R = Checked, a term paired with its inferred type. Each dictionary
##    operation checks its arguments as it builds them, so ill-typed terms
##    cannot be constructed -- a type error raises instead of returning.
##    Conversion follows the paper: beta-structural equality plus the
##    observational rules (proof-irrelevance of 1 and O, eta for Pi/Sigma).
## ---------------------------------------------------------------------------

var neutSupply = 0

proc freshNeutral(): Value =
  inc neutSupply
  Value(kind: vkNeutral, neutId: neutSupply, spine: @[])

let starV = Value(kind: vkStar)
let unitV = Value(kind: vkUnit)
let ttV = Value(kind: vkTt)
let emptyV = Value(kind: vkEmpty)

proc convVal(a, b: Value): bool =
  ## Structural (beta) conversion on weak-head-normal values, with
  ## eta-expansion of lambdas against neutrals.
  if a.kind != b.kind:
    if a.kind == vkLam and b.kind == vkNeutral:
      let x = freshNeutral()
      return convVal(a.body(x), vApp(b, x))
    if a.kind == vkNeutral and b.kind == vkLam:
      let x = freshNeutral()
      return convVal(vApp(a, x), b.body(x))
    return false
  case a.kind
  of vkStar, vkUnit, vkTt, vkEmpty:
    true
  of vkPi, vkSigma:
    let x = freshNeutral()  # one variable, shared by both sides
    convVal(a.dom, b.dom) and convVal(a.cod(x), b.cod(x))
  of vkLam:
    let x = freshNeutral()
    convVal(a.body(x), b.body(x))
  of vkPair:
    convVal(a.fstV, b.fstV) and convVal(a.sndV, b.sndV)
  of vkNat:
    a.natV == b.natV
  of vkNeutral:
    if a.neutId != b.neutId or a.spine.len != b.spine.len:
      return false
    for i in 0 ..< a.spine.len:
      let ea = a.spine[i]
      let eb = b.spine[i]
      if ea.kind != eb.kind:
        return false
      if ea.kind == ekApp and not convVal(ea.arg, eb.arg):
        return false
    true

proc convAt(ty, a, b: Value): bool =
  ## Type-directed conversion (paper §6.7): proof-irrelevance for 1 and O,
  ## eta for Pi and Sigma, structural otherwise.
  case ty.kind
  of vkUnit, vkEmpty:
    true  # proof-irrelevant: any two inhabitants are convertible
  of vkPi:
    let x = freshNeutral()
    convAt(ty.cod(x), vApp(a, x), vApp(b, x))
  of vkSigma:
    convAt(ty.dom, vFst(a), vFst(b)) and
      convAt(ty.cod(vFst(a)), vSnd(a), vSnd(b))
  else:
    convVal(a, b)

proc showValue(v: Value): string =
  ## Readable rendering of values (for types in test output).
  case v.kind
  of vkStar: "Type 0"
  of vkUnit: "1"
  of vkTt: "<>"
  of vkEmpty: "O"
  of vkPi:
    let x = Value(kind: vkNeutral, neutId: -1, spine: @[])
    "Pi(" & showValue(v.dom) & ", " & showValue(v.cod(x)) & ")"
  of vkSigma:
    let x = Value(kind: vkNeutral, neutId: -1, spine: @[])
    "Sigma(" & showValue(v.dom) & ", " & showValue(v.cod(x)) & ")"
  of vkLam: "<lam>"
  of vkPair: "<" & showValue(v.fstV) & "; " & showValue(v.sndV) & ">"
  of vkNat: $v.natV
  of vkNeutral:
    var s = if v.neutId == -1: "_" else: "Type 0" & $v.neutId
    for e in v.spine:
      case e.kind
      of ekApp: s &= " " & showValue(e.arg)
      of ekFst: s &= ".1"
      of ekSnd: s &= ".2"
    s

type Checked = object
  rep: Value  # the term's value
  typ: Value  # its inferred type

proc expectType(c: Checked, what: string) =
  if not convVal(c.typ, starV):
    raise newException(ValueError,
      what & " is not a type (has type " & showValue(c.typ) & ")")

let tcSym = Sym[Checked](
  cStar: proc(): Checked = Checked(rep: starV, typ: starV),
  cUnit: proc(): Checked = Checked(rep: unitV, typ: starV),
  cTt: proc(): Checked = Checked(rep: ttV, typ: unitV),
  cEmpty: proc(): Checked = Checked(rep: emptyV, typ: starV),
  cPi: proc(dom: Checked, cod: proc(x: Checked): Checked): Checked =
    expectType(dom, "pi domain")
    let domV = dom.rep
    expectType(cod(Checked(rep: freshNeutral(), typ: domV)), "pi codomain")
    # The Pi's codomain closure returns the *type* (rep) of cod(x),
    # not its type-of-type.
    let codV = proc(x: Value): Value =
      cod(Checked(rep: x, typ: domV)).rep
    Checked(rep: Value(kind: vkPi, dom: domV, cod: codV), typ: starV),
  cLam: proc(dom: Checked, body: proc(x: Checked): Checked): Checked =
    expectType(dom, "lambda domain")
    let domV = dom.rep
    # Run the body once against a fresh variable: nested checks fire now,
    # so ill-typed bodies are rejected at construction time.
    discard body(Checked(rep: freshNeutral(), typ: domV))
    let codV = proc(x: Value): Value =
      body(Checked(rep: x, typ: domV)).typ
    let repV = proc(x: Value): Value =
      body(Checked(rep: x, typ: domV)).rep
    Checked(rep: Value(kind: vkLam, body: repV),
            typ: Value(kind: vkPi, dom: domV, cod: codV)),
  cApp: proc(f, a: Checked): Checked =
    let fty = f.typ
    if fty.kind != vkPi:
      raise newException(ValueError,
        "application of non-function (type " & showValue(fty) & ")")
    if not convVal(a.typ, fty.dom):
      raise newException(ValueError,
        "argument type mismatch: expected " & showValue(fty.dom) &
        ", got " & showValue(a.typ))
    Checked(rep: vApp(f.rep, a.rep), typ: fty.cod(a.rep)),
  cSigma: proc(dom: Checked, cod: proc(x: Checked): Checked): Checked =
    expectType(dom, "sigma domain")
    let domV = dom.rep
    expectType(cod(Checked(rep: freshNeutral(), typ: domV)), "sigma codomain")
    let codV = proc(x: Value): Value =
      cod(Checked(rep: x, typ: domV)).rep
    Checked(rep: Value(kind: vkSigma, dom: domV, cod: codV), typ: starV),
  cPair: proc(a, b: Checked): Checked =
    # NOTE: the Sym interface does not carry the pair's Sigma range
    # annotation (cf. paper §6.4 `P Term (Term, Scope)`), so we synthesize
    # the non-dependent Sigma. Fully dependent pair types need checking
    # mode with an ascribed type -- elaborator work.
    let domV = a.typ
    let codV = proc(x: Value): Value = b.typ
    Checked(rep: Value(kind: vkPair, fstV: a.rep, sndV: b.rep),
            typ: Value(kind: vkSigma, dom: domV, cod: codV)),
  cFst: proc(p: Checked): Checked =
    let ty = p.typ
    if ty.kind != vkSigma:
      raise newException(ValueError,
        "fst of non-sigma (type " & showValue(ty) & ")")
    Checked(rep: vFst(p.rep), typ: ty.dom),
  cSnd: proc(p: Checked): Checked =
    let ty = p.typ
    if ty.kind != vkSigma:
      raise newException(ValueError,
        "snd of non-sigma (type " & showValue(ty) & ")")
    Checked(rep: vSnd(p.rep), typ: ty.cod(vFst(p.rep))),
  cAbsurd: proc(z: Checked): Checked =
    if not convVal(z.typ, emptyV):
      raise newException(ValueError,
        "absurd needs an empty-type scrutinee, got: " & showValue(z.typ))
    # Paper §6.5: z OE : Pi(X:Type 0). X  (apply it to the desired type)
    let absurdTy = Value(kind: vkPi, dom: starV,
      cod: proc(x: Value): Value = starV)
    Checked(rep: freshNeutral(), typ: absurdTy)
)

## ---------------------------------------------------------------------------
## 6. Example ETT programs, written once against the interface
##    (the paper's §6.4 `twice` example, plus friends)
## ---------------------------------------------------------------------------

proc polyId[R](s: Sym[R]): R =
  ## Polymorphic identity: Pi(X:Type 0). X -> X
  s.cLam(s.cStar(), proc(X: R): R =
    s.cLam(X, proc(x: R): R = x))

proc twice*[R](s: Sym[R]): R =
  ## Twice: Pi(X:Type 0). (X -> X) -> X -> X
  ## (the paper's §6.4 example, in HOAS instead of de Bruijn)
  s.cLam(s.cStar(), proc(X: R): R =
    s.cLam(s.cArr(X, X), proc(f: R): R =
      s.cLam(X, proc(x: R): R =
        s.cApp(f, s.cApp(f, x)))))

proc constFn*[R](s: Sym[R]): R =
  ## const: Pi(A:Type 0). Pi(B:Type 0). A -> B -> A
  s.cLam(s.cStar(), proc(A: R): R =
    s.cLam(s.cStar(), proc(B: R): R =
      s.cLam(A, proc(x: R): R =
        s.cLam(B, proc(y: R): R = x))))

proc pairSwap*[R](s: Sym[R]): R =
  ## Swap the components of a pair over the unit type.
  s.cLam(s.cSigma(s.cUnit(), proc(x: R): R = s.cUnit()), proc(p: R): R =
    s.cPair(s.cSnd(p), s.cFst(p)))

## ---------------------------------------------------------------------------
## 6. Tests: every term is interpreted twice (print + evaluate)
## ---------------------------------------------------------------------------

when isMainModule:
  let pr = newPrinter()

  echo "--- pretty-printed terms ---"
  echo "twice    : ", twice(pr)
  echo "polyId   : ", polyId(pr)
  echo "const    : ", constFn(pr)
  echo "pairSwap : ", pairSwap(pr)

  echo "--- staged code generation (Experiment 8) ---"
  let cg = newCodeGen()
  echo "twice    : ", twice(cg)
  echo "polyId   : ", polyId(cg)
  echo "const    : ", constFn(cg)
  echo "pairSwap : ", pairSwap(cg)

  echo "--- evaluation tests ---"
  let ev = evalSym

  # Test 1: twice 1 (id on 1) <>  ~~> <>
  let idUnit = ev.cLam(ev.cUnit(), proc(x: Value): Value = x)
  let tw1 = ev.cApp(twice(ev), ev.cUnit())
  let tw2 = ev.cApp(tw1, idUnit)
  let t1 = ev.cApp(tw2, ev.cTt())
  assert t1.kind == vkTt, "twice 1 id <> should evaluate to <>"
  echo "ok: twice 1 (\\x:1. x) <>  ==>  <>"

  # Test 2: polyId 1 <>  ~~> <>
  let pi1 = ev.cApp(polyId(ev), ev.cUnit())
  let t2 = ev.cApp(pi1, ev.cTt())
  assert t2.kind == vkTt, "polyId 1 <> should evaluate to <>"
  echo "ok: polyId 1 <>  ==>  <>"

  # Test 3: const 1 1 <> <>  ~~> <>
  let c1 = ev.cApp(constFn(ev), ev.cUnit())
  let c2 = ev.cApp(c1, ev.cUnit())
  let c3 = ev.cApp(c2, ev.cTt())
  let t3 = ev.cApp(c3, ev.cTt())
  assert t3.kind == vkTt, "const 1 1 <> <> should evaluate to <>"
  echo "ok: const 1 1 <> <>  ==>  <>"

  # Test 4: pair projections: fst <tt; tt> ~~> tt, snd <tt; tt> ~~> tt
  let p = ev.cPair(ev.cTt(), ev.cTt())
  assert ev.cFst(p).kind == vkTt
  assert ev.cSnd(p).kind == vkTt
  echo "ok: fst <tt;tt> and snd <tt;tt>  ==>  <>"

  # Test 5: pairSwap <tt; tt> ~~> <tt; tt> (a pair value)
  let t5 = ev.cApp(pairSwap(ev), p)
  assert t5.kind == vkPair and t5.fstV.kind == vkTt and t5.sndV.kind == vkTt
  echo "ok: pairSwap <tt;tt>  ==>  <tt;tt>"

  # Test 6: cLet as a beta-redex: [x |-> <> : 1]x  ~~> <>
  let t6 = ev.cLet(ev.cUnit(), ev.cTt(), proc(x: Value): Value = x)
  assert t6.kind == vkTt
  echo "ok: let x = <> : 1 in x  ==>  <>"

  # Test 7: types evaluate too: Pi(x:1). 1 is a value (not stuck)
  let ty = ev.cPi(ev.cUnit(), proc(x: Value): Value = ev.cUnit())
  assert ty.kind == vkPi
  echo "ok: Pi(x:1). 1 evaluates to a Pi value"

  echo "--- typechecker tests ---"
  let tc = tcSym

  # Test 8: twice checks; inferred type is Pi(X:Type 0 ). (X->X) -> X->X
  let twc = twice(tc)
  let expTwTy = ev.cPi(ev.cStar(),
    proc(X: Value): Value = ev.cArr(ev.cArr(X, X), ev.cArr(X, X)))
  assert convVal(twc.typ, expTwTy), "twice type mismatch: " & showValue(twc.typ)
  echo "ok: twice checks : ", showValue(twc.typ)

  # Test 9: dependent application: polyId 1 <> : 1
  let t9a = tc.cApp(polyId(tc), tc.cUnit())
  let t9 = tc.cApp(t9a, tc.cTt())
  assert convVal(t9.typ, unitV), "expected type 1, got " & showValue(t9.typ)
  echo "ok: polyId 1 <> : 1"

  # Test 10: ill-typed application rejected (<> : 1 against domain Type 0)
  var rejected = false
  try:
    discard tc.cApp(polyId(tc), tc.cTt())
  except ValueError:
    rejected = true
  assert rejected, "ill-typed application was not rejected"
  echo "ok: polyId <> rejected (argument type mismatch)"

  # Test 11: application of a non-function rejected
  rejected = false
  try:
    discard tc.cApp(tc.cTt(), tc.cTt())
  except ValueError:
    rejected = true
  assert rejected, "non-function application was not rejected"
  echo "ok: <> <> rejected (non-function)"

  # Test 12: fst of a non-pair rejected
  rejected = false
  try:
    discard tc.cFst(tc.cTt())
  except ValueError:
    rejected = true
  assert rejected, "fst of non-pair was not rejected"
  echo "ok: fst <> rejected"

  # Test 13: pairSwap checks (exercises Sigma + projections)
  let psc = pairSwap(tc)
  echo "ok: pairSwap checks : ", showValue(psc.typ)

  # Test 14: proof irrelevance for 1 -- any two inhabitants convertible
  let n1 = freshNeutral()
  let n2 = freshNeutral()
  assert convAt(unitV, n1, n2), "unit proof irrelevance failed"
  assert convAt(emptyV, n1, n2), "empty proof irrelevance failed"
  echo "ok: proof irrelevance for 1 and O"

  # Test 15: absurd rejects a non-empty scrutinee
  rejected = false
  try:
    discard tc.cAbsurd(tc.cTt())
  except ValueError:
    rejected = true
  assert rejected, "absurd of non-empty was not rejected"
  echo "ok: absurd <> rejected (non-empty scrutinee)"

  # Test 16: const checks with the dependent type Pi(A:Type 0 ). Pi(B:Type 0 ). A->B->A
  let cc = constFn(tc)
  let expCTy = ev.cPi(ev.cStar(), proc(A: Value): Value =
    ev.cPi(ev.cStar(), proc(B: Value): Value = ev.cArr(A, ev.cArr(B, A))))
  assert convVal(cc.typ, expCTy), "const type mismatch: " & showValue(cc.typ)
  echo "ok: const checks : ", showValue(cc.typ)

  echo "--- all tests passed ---"
