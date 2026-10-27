## Surface-syntax conformance (issue #144, step 3).
##
## Eponym has exactly one surface syntax, defined by parse_surf's grammar.
## The embedded front end (`eponymBlock`) maps Nim AST to a source string
## via `blockToEponym` (eponym_mac) and parses it with the same parser.
## This suite pins the agreement: each case pairs an eponymBlock-style Nim
## block with the equivalent standalone `.ep` source; both must parse to
## identical `SurfDecl`s. Comparison ignores source locations but checks
## binder quantities explicitly (`PreTerm.==` compares `erased` but not
## `qty`, and the renderer drops quantities).

import macros
import eponym_mac  # blockToEponym: Nim AST -> Eponym source string
import parse_surf  # parseProgram: the canonical parser
import preterm     # SurfDecl / PreTerm

type Tele = seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]]

proc sameQty(a, b: Qty): bool =
  ## Qty is a case object, so the default `==` does not apply.
  if a.isVar != b.isVar: return false
  if a.isVar: a.vname == b.vname else: a.q == b.q

proc sameTerm(a, b: PreTerm): bool =
  ## Structural equality including binder quantities.
  if a.isNil and b.isNil: return true
  if a.isNil or b.isNil: return false
  a.kind == b.kind and a.name == b.name and a.impl == b.impl and
    a.erased == b.erased and sameQty(a.qty, b.qty) and a.intVal == b.intVal and
    sameTerm(a.c1, b.c1) and sameTerm(a.c2, b.c2) and sameTerm(a.c3, b.c3)

proc sameTele(a, b: Tele): bool =
  if a.len != b.len: return false
  for i in 0 ..< a.len:
    if a[i].name != b[i].name or not sameTerm(a[i].ty, b[i].ty) or
       a[i].impl != b[i].impl or a[i].erased != b[i].erased or
       not sameQty(a[i].qty, b[i].qty):
      return false
  true

proc sameCtor(a, b: DataCtor): bool =
  a.name == b.name and sameTele(a.tele, b.tele) and sameTerm(a.retTy, b.retTy)

proc sameClauses(a, b: ClausesDef): bool =
  if a.name != b.name or not sameTerm(a.ty, b.ty): return false
  if a.clauses.len != b.clauses.len: return false
  for i in 0 ..< a.clauses.len:
    let x = a.clauses[i]
    let y = b.clauses[i]
    if x.pats.len != y.pats.len: return false
    for j in 0 ..< x.pats.len:
      if not sameTerm(x.pats[j], y.pats[j]): return false
    if not sameTerm(x.rhs, y.rhs): return false
  true

proc sameDecl(a, b: SurfDecl): bool =
  if a.kind != b.kind: return false
  case a.kind
  of dkDef:
    a.def.name == b.def.name and sameTele(a.def.tele, b.def.tele) and
      sameTerm(a.def.retTy, b.def.retTy) and sameTerm(a.def.body, b.def.body) and
      a.def.hasPeg == b.def.hasPeg and a.def.pegNames == b.def.pegNames
  of dkPostulate, dkElim:
    a.name == b.name and sameTerm(a.ty, b.ty)
  of dkRed:
    sameTerm(a.lhs, b.lhs) and sameTerm(a.rhs, b.rhs)
  of dkData:
    if a.dname != b.dname or not sameTele(a.params, b.params): return false
    if not sameTerm(a.indexTy, b.indexTy): return false
    if a.ctors.len != b.ctors.len: return false
    for i in 0 ..< a.ctors.len:
      if not sameCtor(a.ctors[i], b.ctors[i]): return false
    true
  of dkClauses:
    sameClauses(a.clausesDef, b.clausesDef)
  of dkMutual:
    if a.mutualDefs.len != b.mutualDefs.len: return false
    for i in 0 ..< a.mutualDefs.len:
      if not sameClauses(a.mutualDefs[i], b.mutualDefs[i]): return false
    true
  of dkImport:
    a.ipath == b.ipath
  of dkInterface:
    a.ifname == b.ifname
  of dkCommand:
    a.cname == b.cname and a.ciface == b.ciface and sameTerm(a.cty, b.cty)
  of dkRecord:
    if a.rname != b.rname or a.fields.len != b.fields.len: return false
    for i in 0 ..< a.fields.len:
      if a.fields[i].name != b.fields[i].name or
         not sameTerm(a.fields[i].ty, b.fields[i].ty):
        return false
    true

macro conforms*(src: static string, blk: untyped): untyped =
  ## Assert `blockToEponym(blk)` parses to the same decls as `src`.
  ## Usage: conforms """.ep source""": <eponymBlock-style block>
  let gen = blockToEponym(blk)
  let a = parseProgram(gen)
  let b = parseProgram(src)
  if a.len != b.len:
    error("decl count mismatch: embedded block gave " & $a.len &
      ", standalone source gave " & $b.len &
      "\n--- generated source ---\n" & gen, blk)
  for i in 0 ..< a.len:
    if not sameDecl(a[i], b[i]):
      error("decl " & $i & " differs between embedded and standalone parse" &
        "\n--- generated source ---\n" & gen, blk)
  newStmtList()  # success: expand to nothing

# --- corpus ----------------------------------------------------------

# arrows, application, nested calls
conforms """proc twice (A : Univ) (f : A -> A) (x : A) : A = f (f x)
proc constFn (A : Univ) (B : Univ) (x : A) (y : B) : A = x
""":
  proc twice(A: Univ, f: A -> A, x: A): A = f(f(x))
  proc constFn(A: Univ, B: Univ, x: A, y: B): A = x

# lam, Sig (named and anonymous), pairs, projections
conforms """proc pairSwap (A : Univ) (B : Univ) (p : Sig(u: A, B)) : Sig(v: B, A) =
  (snd p, fst p)
proc applyLam (A : Univ) : A -> A =
  lam(x: A) => x
proc anonSig (A : Univ) (B : Univ) : Sig(A, B) -> A =
  lam(p: Sig(A, B)) => fst p
""":
  proc pairSwap(A: Univ, B: Univ, p: Sig(u, A, B)): Sig(v, B, A) =
    (snd(p), fst(p))
  proc applyLam(A: Univ): A -> A = lam(x: A) => x
  proc anonSig(A: Univ, B: Univ): Sig(A, B) -> A =
    lam(p: Sig(A, B)) => fst(p)

# Lambda groups, greedy bodies, unannotated/implicit binders, and nested use.
conforms """proc nested (A : Univ) : A -> A = lam(x: A) => lam(y: A) => x
proc inferred (A : Univ) : A -> A = lam(x) => x
proc implicitId : Pi{A: Univ, A -> A} = lam({A: Univ}) => lam(x: A) => x
proc linearId : Nat -> Nat = lam(1 x: Nat) => x
proc eraseNat : Nat -> unitTy = lam(0 x: Nat) => unitv
proc underApply (A : Univ) (f : A -> A) (x : A) : A = (lam(y: A) => f y) x
""":
  proc nested(A: Univ): A -> A = lam(x: A, y: A) => x
  proc inferred(A: Univ): A -> A = lam(x) => x
  proc implicitId(): Pi({A: Univ}, A -> A) =
    lam({A: Univ}) => lam(x: A) => x
  proc linearId(): Nat -> Nat = lam(x {.linear.}: Nat) => x
  proc eraseNat(): Nat -> unitTy =
    lam(x {.erased.}: Nat) => unitv
  proc underApply(A: Univ, f: A -> A, x: A): A = (lam(y: A) => f(y))(x)

# Lambda terms nested in type-level bracket arguments retain their boundary.
conforms """postulate(F, (Nat -> Univ) -> Univ)
proc useFunctionType : F[lam(x: Nat) => Nat] = _
""":
  postulate(F, (Nat -> Univ) -> Univ)
  proc useFunctionType(): F[lam(x: Nat) => Nat] = _

# Pi with named binders, implicit binders, let..in, holes
conforms """proc polyId (A : Univ) (x : A) : A = x
proc impId : Pi{A: Univ, A -> A} = lam(x: A) => x
proc withLet (A : Univ) (x : A) : A = let y = x in y
proc holeTy : Univ = _
""":
  proc polyId(A: Univ, x: A): A = x
  proc impId(): Pi({A: Univ}, A -> A) = lam(x: A) => x
  proc withLet(A: Univ, x: A): A =
    let y = x
    y
  proc holeTy(): Univ = _

# Pi/Sig as terms (Nim parses named-binder Pi as an object constructor)
conforms """proc piTy : Univ = Pi(x: Nat, Nat)
""":
  proc piTy(): Univ = Pi(x: Nat, Nat)

# data declaration + postulate
conforms """data(Nat, Univ) where
| zero : Nat
| suc (n : Nat) : Nat
postulate(Bool, Univ)
""":
  data(Nat, Univ):
    proc zero(): Nat
    proc suc(n: Nat): Nat
  postulate(Bool, Univ)

# parameterized indexed data (Vec); `vecnil` maps to `nil`
conforms """data(Vec, [A: Univ], Pi(n: Nat, Vec[A, n] -> Univ)) where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
""":
  data(Vec, [A: Univ], Pi(n: Nat, Vec[A, n] -> Univ)):
    proc vecnil(): Vec[A, zero]
    proc cons(n: Nat, x: A, xs: Vec[A, n]): Vec[A, suc(n)]

# import declaration (parse-only; the path need not resolve here)
conforms """import "lib/nat.ep"
proc useNat (x : Nat) : Nat = x
""":
  import "lib/nat.ep"
  proc useNat(x: Nat): Nat = x

# quantity binders from {.linear.} / {.erased.} pragmas
conforms """proc useLin (1 ch : Univ) (x : Univ) : Univ = x
proc useEra (0 ch : Univ) (x : Univ) : Univ = x
""":
  proc useLin(ch {.linear.}: Univ, x: Univ): Univ = x
  proc useEra(ch {.erased.}: Univ, x: Univ): Univ = x

# Single syntax: `1` is the integer literal one. Expected-type overloading
# still selects Nat or Int (issues #8, #115).
conforms """proc three : Nat = 3
proc one : Nat = 1
""":
  proc three(): Nat = 3
  proc one(): Nat = 1

# elim / red declarations (smoke tests 07/08; issue #151)
conforms """elim(boolElim, Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b))))
red(boolElim C t f true, t)
red(boolElim C t f false, f)
""":
  elim(boolElim, Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b))))
  red(boolElim(C, t, f, true), t)
  red(boolElim(C, t, f, false), f)

# by-tactic terms (smoke test 14; issue #151)
conforms """proc pf1 : Eq Int 42 42 = byTac(refl)
proc pid (x : Int) : Int = byTac("assumption")
""":
  proc pf1(): Eq(Int, 42, 42) = byTac(refl)
  proc pid(x: Int): Int = byTac("assumption")

# def clause-style definitions (issue #151)
conforms """def(isZero, Nat -> Bool):
  clause([zero], true)
  clause([suc(n)], false)
""":
  def(isZero, Nat -> Bool):
    clause([zero], true)
    clause([suc(n)], false)

# quantity-variable binders (issue #151 / #66)
conforms """proc qid (q x : Univ) : Univ = x
""":
  proc qid(x {.qvar(q).}: Univ): Univ = x

# unit value, unit type, empty type (issue #151)
conforms """proc unitVal : unitTy = unitv
proc absurd (x : emptyTy) : emptyTy = x
""":
  proc unitVal(): unitTy = unitv
  proc absurd(x: emptyTy): emptyTy = x

# term ascription, typed let, quantity-annotated lam (issue #151)
conforms """proc asc (A : Univ) (x : A) : A = (x : A)
proc typedLet (A : Univ) (x : A) : A =
  let y : A = x in y
proc linLam : Univ = lam(1 x: Univ) => x
""":
  proc asc(A: Univ, x: A): A = (x: A)
  proc typedLet(A: Univ, x: A): A =
    let y: A = x
    y
  proc linLam(): Univ = lam(x {.linear.}: Univ) => x

# record declaration + dot projection (issue #37)
conforms """record(Point):
| x : Univ
| y : Univ
proc getX (p : Point) : Univ = p.x
""":
  record(Point):
    field(x, Univ)
    field(y, Univ)
  proc getX(p: Point): Univ = p.x

# mutual block of clause defs (issue #42)
conforms """mutual
def(even, Nat -> Bool):
  clause([zero], true)
  clause([suc(n)], odd(n))
def(odd, Nat -> Bool):
  clause([zero], false)
  clause([suc(n)], even(n))
""":
  mutual:
    def(even, Nat -> Bool):
      clause([zero], true)
      clause([suc(n)], odd(n))
    def(odd, Nat -> Bool):
      clause([zero], false)
      clause([suc(n)], even(n))

# embedded-block forms in .ep text (issue #467)
conforms """proc unitVal : unitTy = unitv
proc absurd (x : emptyTy) : emptyTy = x
proc holeTy : Univ = _
""":
  proc unitVal(): unitTy = unitv
  proc absurd(x: emptyTy): emptyTy = x
  proc holeTy(): Univ = _

conforms """proc applyLam (A : Univ) : A -> A = lam(x: A) => x
proc piTy : Univ = Pi(x: Nat, Nat)
proc sigTy (A : Univ) (B : Univ) : Univ = Sig(A, B)
proc sigTy2 (A : Univ) (B : Univ) : Univ = Sig(u: A, B)
proc sigTy3 (A : Univ) (B : Univ) : Univ = Sig(u, A, B)
proc vecTy (n : Nat) : Univ = Vec[Int, n]
""":
  proc applyLam(A: Univ): A -> A = lam(x: A) => x
  proc piTy(): Univ = Pi(x: Nat, Nat)
  proc sigTy(A: Univ, B: Univ): Univ = Sig(A, B)
  proc sigTy2(A: Univ, B: Univ): Univ = Sig(u, A, B)
  proc sigTy3(A: Univ, B: Univ): Univ = Sig(u, A, B)
  proc vecTy(n: Nat): Univ = Vec[Int, n]

conforms """postulate(Bool, Univ)
elim(boolElim, Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b))))
red(boolElim C t f true, t)
""":
  postulate(Bool, Univ)
  elim(boolElim, Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b))))
  red(boolElim(C, t, f, true), t)

conforms """proc pf1 : Eq Int 42 42 = byTac(refl)
proc pid (x : Int) : Int = byTac("assumption")
""":
  proc pf1(): Eq(Int, 42, 42) = byTac(refl)
  proc pid(x: Int): Int = byTac("assumption")

conforms """data(Vec2, [A: Univ], Pi(n: Nat, Vec2[A, n] -> Univ)) where
| nil : Vec2[A, zero]
| cons2 (n : Nat) (x : A) (xs : Vec2[A, n]) : Vec2[A, suc(n)]
""":
  data(Vec2, [A: Univ], Pi(n: Nat, Vec2[A, n] -> Univ)):
    proc vecnil(): Vec2[A, zero]
    proc cons2(n: Nat, x: A, xs: Vec2[A, n]): Vec2[A, suc(n)]

conforms """def(isZero3, Nat -> Bool):
  clause([zero], true)
  clause([suc(n)], false)
  clause([_], true)
""":
  def(isZero3, Nat -> Bool):
    clause([zero], true)
    clause([suc(n)], false)
    clause([_], true)

conforms """record(Point2):
| x : Univ
| y : Univ
""":
  record(Point2):
    field(x, Univ)
    field(y, Univ)

# Nim call rule (issue #467): f(a, b) is the two-argument call, f((a, b))
# passes the pair.
conforms """proc apply2 (A : Univ) (B : Univ) (f : A -> B -> A) (x : A) (y : B) : A = f(x, y)
proc applyPair (A : Univ) (B : Univ) (f : Sig(A, B) -> A) (p : Sig(A, B)) : A = f((fst p, snd p))
""":
  proc apply2(A: Univ, B: Univ, f: A -> B -> A, x: A, y: B): A = f(x, y)
  proc applyPair(A: Univ, B: Univ, f: Sig(A, B) -> A, p: Sig(A, B)): A = f((fst(p), snd(p)))

echo "surface_conformance: all tests passed"
