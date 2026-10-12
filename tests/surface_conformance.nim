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
      sameTerm(a.def.retTy, b.def.retTy) and sameTerm(a.def.body, b.def.body)
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
  of dkImport:
    a.ipath == b.ipath

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
conforms """proc twice (A : ?) (f : A -> A) (x : A) : A = f (f x)
proc constFn (A : ?) (B : ?) (x : A) (y : B) : A = x
""":
  proc twice(A: Univ, f: A -> A, x: A): A = f(f(x))
  proc constFn(A: Univ, B: Univ, x: A, y: B): A = x

# lam, Sig (named and anonymous), pairs, projections
conforms """proc pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A =
  (snd p, fst p)
proc applyLam (A : ?) : A -> A =
  lam (x : A). x
proc anonSig (A : ?) (B : ?) : Sig (_ : A). B -> A =
  lam (p : Sig (_ : A). B). fst p
""":
  proc pairSwap(A: Univ, B: Univ, p: Sig(u, A, B)): Sig(v, B, A) =
    (snd(p), fst(p))
  proc applyLam(A: Univ): A -> A = lam(x, A, x)
  proc anonSig(A: Univ, B: Univ): Sig(A, B) -> A =
    lam(p, Sig(A, B), fst(p))

# Pi with named binders, implicit binders, let..in, holes
conforms """proc polyId (A : ?) (x : A) : A = x
proc impId : Pi {A : ?}. A -> A = lam (x : A). x
proc withLet (A : ?) (x : A) : A = let y = x in y
proc holeTy : ? = _
""":
  proc polyId(A: Univ, x: A): A = x
  proc impId(): Pi({A: Univ}, A -> A) = lam(x, A, x)
  proc withLet(A: Univ, x: A): A =
    let y = x
    y
  proc holeTy(): Univ = _

# Pi/Sig as terms (Nim parses named-binder Pi as an object constructor)
conforms """proc piTy : ? = Pi (x : Nat). Nat
""":
  proc piTy(): Univ = Pi(x: Nat, Nat)

# data declaration + postulate
conforms """data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
postulate Bool : ?
""":
  data(Nat, Univ):
    proc zero(): Nat
    proc suc(n: Nat): Nat
  postulate(Bool, Univ)

# parameterized indexed data (Vec); `vecnil` maps to `nil`
conforms """data Vec (A : ?) : Pi (n : Nat). Vec A n -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
""":
  data(Vec, [A: Univ], Pi(n: Nat, Vec(A, n) -> Univ)):
    proc vecnil(): Vec(A, zero)
    proc cons(n: Nat, x: A, xs: Vec(A, n)): Vec(A, suc(n))

# import declaration (parse-only; the path need not resolve here)
conforms """import "lib/nat.ep"
proc useNat (x : Nat) : Nat = x
""":
  import "lib/nat.ep"
  proc useNat(x: Nat): Nat = x

# quantity binders from {.linear.} / {.erased.} pragmas
conforms """proc useLin (1 ch : ?) (x : ?) : ? = x
proc useEra (0 ch : ?) (x : ?) : ? = x
""":
  proc useLin(ch {.linear.}: Univ, x: Univ): Univ = x
  proc useEra(ch {.erased.}: Univ, x: Univ): Univ = x

# integer literals; `1` is the unit type in surface syntax, so the Nat
# literal one is spelled `(suc zero)` (issues #8, #115)
conforms """proc three : Nat = 3
proc one : Nat = (suc zero)
""":
  proc three(): Nat = 3
  proc one(): Nat = 1

echo "surface_conformance: all tests passed"
