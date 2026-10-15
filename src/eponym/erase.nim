## Issue #2 (Experiment 9): erasure beyond metadata.
##
## Status quo: the elaborator enforces QTT quantities (usage checking,
## #64/#66/#88) and threads an `erased` flag from surface `(0 x : T)`
## binders through PreTerm to core Term — but the core ignores the flag
## (eponym_init.nim: the elaborator stamps it; "the core ignores it (like
## impl/erased)"). Erased subterms are still carried in types/terms and,
## worse, eagerly evaluated: `evalWhnf`'s `tApp` case evaluates the argument
## before applying, even when the binder is quantity-0. So today "erased"
## is a checking-time discipline with no runtime effect.
##
## This module implements erasure as a term transformation over elaborated,
## usage-checked, zonked core Terms:
##
## - `eraseTerm(t)`: drop every erased binder (tLam/tPi/tSi with erased=true),
##   shifting de Bruijn indices down past the dropped binder; recurse
##   everywhere else (including inside domains/types, uniformly).
## - `eraseDef(tyTm, tmTm)`: erase a definition's type and body; asserts the
##   Pi telescope and the body lambdas agree on which positions are erased.
##
## Occurrence kinds: dropping a binder must distinguish *term* positions
## (where the erased variable cannot occur — usage checking guarantees it)
## from *type* positions (domains, Pi/Si bodies, let-types — where the
## variable may freely occur; QTT checks types in the all-0 context). In
## term position an occurrence is a compiler bug: fail loudly. In type
## position the occurrence is replaced by a closed placeholder
## (`erasedPlaceholder`, the unit type): types are computationally
## irrelevant, and the placeholder keeps indices well-scoped. This mirrors
## usage_check.countVarUses, which likewise does not descend into domains.
##
## Deliberate non-goals (documented for the follow-up):
## - Call-site argument dropping is NOT done here. Dropping `f`'s argument in
##   `tApp(f, a)` needs the callee's Pi type (type-directed erasure); the
##   syntactic pass cannot know that a `tR`'s binder is erased. The design is
##   a mask table over the def sequence at emission (`getDefs`) time, skipping
##   eliminator refs (their `RedRule.nargs` counting would break) — see the
##   issue. Binder-dropping alone already removes the *binders*; the arguments
##   still evaluate eagerly at call sites until that lands.
## - No re-checking of erased terms against erased types here. Erasure is
##   type-preserving (standard QTT metatheory), but the audit pipeline for it
##   is future work; the tests below pin evaluation-equivalence instead.
##
## Latent bug found while writing this (not fixed here): `mkBinder`
## (eponym_init.nim) hardcodes `erased = false`, so `substEnv`, `weakenAt`,
## and `absGo` silently clear the flag on every substitution/weakening. Any
## erasure pass composed after those must re-derive erased-ness from
## quantities, not trust the flag. This module uses tmPi/tmLam/tmSi directly
## and never mkBinder.

import std/sequtils
import preterm  # Quantity, q0
import eponym_init

proc isErasedBinder*(t: Term): bool =
  ## The erasure predicate: quantity-0 binders erase. This covers both
  ## explicit `(0 x : T)` (which sets erased=true and qty=q0) and
  ## inferred-q0 binders (qty=q0, erased=false). We key off the quantity,
  ## not just the flag, because `mkBinder` (eponym_init.nim) hardcodes
  ## `erased = false`: subst/weaken/zonk silently clear the flag while
  ## preserving the quantity. (Fixing mkBinder to preserve the flag is
  ## follow-up work; see the issue.)

  (t.kind == tPi or t.kind == tSi or t.kind == tLam) and
    (t.erased or t.qty == q0)

let erasedPlaceholder* = tmC(cOne)
  ## Stands in for a type mentioning a dropped erased variable. Closed,
  ## inert, never meaningfully evaluated (lambda domains are not evaluated
  ## by `eval`; Pi domains evaluate to a value that is discarded for our
  ## equivalence tests).

proc strengthenAt(t: Term, depth: int, inType: bool): Term =
  ## Drop the binder at de Bruijn `depth`: indices above it shift down by 1.
  ## `inType` tracks whether we are in a type position (domains, Pi/Si
  ## bodies, let-types). An occurrence of the dropped binder in term position
  ## violates the usage-checking invariant — raise rather than corrupt.
  ## In type position it becomes `erasedPlaceholder`.
  case t.kind
  of tV:
    if t.idx < depth: t
    elif t.idx == depth:
      if inType: erasedPlaceholder
      else:
        raise newException(ValueError,
          "erase: erased variable occurs in term position (usage-checking bug)")
    else: vv(t.idx - 1)
  of tR, tC, tType, tInt, tPrim, tNatLit, tNatSing: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(strengthenAt(it, depth, inType)))
  of tPi, tSi, tLam:
    # Domains are always type positions. Pi/Si bodies are types;
    # lambda bodies are terms.
    let dom = strengthenAt(t.dom, depth, true)
    let bodyInType = inType or t.kind != tLam
    let bdy = strengthenAt(t.scope.bdy, depth + 1, bodyInType)
    case t.kind
    of tPi: tmPi(dom, t.scope.adv, bdy, t.impl, t.erased, t.qty, t.peg)
    of tSi: tmSi(dom, t.scope.adv, bdy, t.impl, t.erased, t.qty)
    else: tmLam(dom, t.scope.adv, bdy, t.impl, t.erased, t.qty, t.peg)
  of tPair:
    # pScope.bdy is the dependent codomain: a type position.
    tmPair(strengthenAt(t.pFst, depth, inType),
           strengthenAt(t.pSnd, depth, inType),
           t.pScope.adv, strengthenAt(t.pScope.bdy, depth + 1, true))
  of tApp:
    tmApp(strengthenAt(t.fn, depth, inType),
          strengthenAt(t.arg, depth, inType))
  of tFst: tmFst(strengthenAt(t.sub, depth, inType))
  of tSnd: tmSnd(strengthenAt(t.sub, depth, inType))
  of tAbsurd: tmAbsurd(strengthenAt(t.sub, depth, inType))
  of tLet:
    tmLet(strengthenAt(t.letVal, depth, inType),
          strengthenAt(t.letTy, depth, true),
          t.letScope.adv, strengthenAt(t.letScope.bdy, depth + 1, inType))

proc hasErased*(t: Term): bool =
  ## True if any binder in t (including inside types) is marked erased.
  case t.kind
  of tPi, tSi, tLam:
    isErasedBinder(t) or hasErased(t.dom) or hasErased(t.scope.bdy)
  of tR, tC, tType, tInt, tV, tPrim, tNatLit, tNatSing: false
  of tMeta: t.metaSpine.anyIt(hasErased(it))
  of tPair: hasErased(t.pFst) or hasErased(t.pSnd) or hasErased(t.pScope.bdy)
  of tApp: hasErased(t.fn) or hasErased(t.arg)
  of tFst, tSnd, tAbsurd: hasErased(t.sub)
  of tLet: hasErased(t.letVal) or hasErased(t.letTy) or hasErased(t.letScope.bdy)

proc eraseTerm*(t: Term): Term =
  ## Drop every erased binder; shift indices past dropped binders.
  case t.kind
  of tPi, tSi, tLam:
    if isErasedBinder(t):
      # Drop the binder entirely. The domain is computationally irrelevant
      # once the binder is gone; the body is erased then closed over the gap.
      # Pi/Si bodies are types (inType=true); lambda bodies are terms.
      strengthenAt(eraseTerm(t.scope.bdy), 0, t.kind != tLam)
    else:
      let dom = eraseTerm(t.dom)
      let bdy = eraseTerm(t.scope.bdy)
      case t.kind
      of tPi: tmPi(dom, t.scope.adv, bdy, t.impl, t.erased, t.qty, t.peg)
      of tSi: tmSi(dom, t.scope.adv, bdy, t.impl, t.erased, t.qty)
      else: tmLam(dom, t.scope.adv, bdy, t.impl, t.erased, t.qty, t.peg)
  of tR, tC, tType, tInt, tV, tPrim, tNatLit, tNatSing: t
  of tMeta: tmMeta(t.metaId, t.metaSpine.mapIt(eraseTerm(it)))
  of tPair:
    tmPair(eraseTerm(t.pFst), eraseTerm(t.pSnd),
           t.pScope.adv, eraseTerm(t.pScope.bdy))
  of tApp: tmApp(eraseTerm(t.fn), eraseTerm(t.arg))
  of tFst: tmFst(eraseTerm(t.sub))
  of tSnd: tmSnd(eraseTerm(t.sub))
  of tAbsurd: tmAbsurd(eraseTerm(t.sub))
  of tLet:
    tmLet(eraseTerm(t.letVal), eraseTerm(t.letTy),
          t.letScope.adv, eraseTerm(t.letScope.bdy))

proc teleErased*(ty: Term): seq[bool] =
  ## Erased-flags of the leading Pi telescope, outermost first.
  var t = ty
  while t.kind == tPi:
    result.add(isErasedBinder(t))
    t = t.scope.bdy

proc lamErased*(tm: Term): seq[bool] =
  ## Erased-flags of the leading lambdas, outermost first.
  var t = tm
  while t.kind == tLam:
    result.add(isErasedBinder(t))
    t = t.scope.bdy

proc eraseDef*(tyTm, tmTm: Term): tuple[ty, tm: Term] =
  ## Erase a definition's type and body. The Pi telescope and the body
  ## lambdas must agree on erased positions (both are built from the same
  ## surface telescope); a mismatch is an elaborator bug — fail loudly.
  ## The body may be eta-contracted (fewer lambdas than Pi binders); only
  ## the common prefix is checked.
  let tm = teleErased(tyTm)
  let lm = lamErased(tmTm)
  let n = min(tm.len, lm.len)
  for i in 0 ..< n:
    if tm[i] != lm[i]:
      raise newException(ValueError,
        "erase: type/body erased-binder mismatch at position " & $i)
  (eraseTerm(tyTm), eraseTerm(tmTm))

when isMainModule:
  import elab
  # End-to-end tests through the real elaborator (elabCheck), plus
  # hand-built Term unit tests.

  # 1. Drop a single erased lambda; outer index shifts down.
  #    L(0 _: Nat). L(x: Nat). x   ==>   L(x: Nat). x
  let natT = tmC(cStar)  # any closed type; dom content is irrelevant here
  let t1 = tmLam(natT, "_", tmLam(natT, "x", vv(0)), false, true)
  let e1 = eraseTerm(t1)
  doAssert not hasErased(e1)
  doAssert e1.kind == tLam and e1.scope.bdy.kind == tV and
    e1.scope.bdy.idx == 0
  echo "ok: erased lambda dropped, body kept"

  # 2. Nested erased binders with shadowing: indices tracked by depth.
  #    L(0 a: Nat). L(a: Nat). a   ==>   L(a: Nat). a   (inner a, idx 0)
  let t2 = tmLam(natT, "a", tmLam(natT, "a", vv(0)), false, true)
  let e2 = eraseTerm(t2)
  doAssert e2.kind == tLam and e2.scope.bdy.kind == tV and
    e2.scope.bdy.idx == 0
  echo "ok: shadowing respected under erased binder"

  # 3. Erased variable in term position: fail loudly, not silently corrupt.
  #    L(0 a: Nat). a
  let t3 = tmLam(natT, "a", vv(0), false, true)
  var raised = false
  try: discard eraseTerm(t3)
  except ValueError: raised = true
  doAssert raised
  echo "ok: erased var in term position raises"

  # 4. Pi telescope erasure: Pi(0 A: *). Pi(x: A). A ==> Pi(x: 1). A[placeholder]
  #    The type-level mention of A becomes the placeholder; B keeps its index.
  let ty4 = tmPi(tmC(cStar), "A", tmPi(vv(0), "x", vv(0)), false, true)
  let e4 = eraseTerm(ty4)
  doAssert not hasErased(e4)
  doAssert teleErased(e4) == @[false]
  doAssert e4.kind == tPi
  doAssert e4.dom.kind == tC and e4.dom.c == cOne,
    "type-position occurrence of the dropped binder becomes the placeholder"
  doAssert e4.scope.bdy.kind == tV and e4.scope.bdy.idx == 0,
    "body still refers to x"
  echo "ok: erased Pi binder dropped; type mention becomes placeholder"

  # 5. End-to-end: elaborate, erase, evaluation agrees on fewer args.
  let defs = elabCheck("""
postulate Int : ?
proc constErased (0 ign : Int) (x : Int) : Int = x
""")
  doAssert defs.len == 1
  let d = defs[0]
  doAssert hasErased(d.tmTm), "expected an erased binder in the body"
  let (ety, etm) = eraseDef(d.tyTm, d.tmTm)
  doAssert not hasErased(ety) and not hasErased(etm)
  doAssert teleErased(ety) == @[false]
  doAssert lamErased(etm) == @[false]
  # Original needs both args (erased one evaluated eagerly and discarded);
  # erased needs only the relevant one. Same result.
  let w1 = applyWhnf(eval(d.tmTm, @[]), vInt(999))
  let wOrig = applyWhnf(Value(syn: d.tmTm, whnf: w1), vInt(5))
  let wErased = applyWhnf(eval(etm, @[]), vInt(5))
  doAssert wOrig.kind == wInt and wOrig.intVal == 5
  doAssert wErased.kind == wInt and wErased.intVal == 5
  echo "ok: end-to-end eraseDef — evaluation agrees, one fewer argument"

  # 6. Inferred-q0 binders erase too (no explicit (0 ...) needed):
  #    proc k2 (A : ?) (x : A) : Int = three  — A, x unused: both infer q0.
  let defs6 = elabCheck("""
postulate Int : ?
postulate three : Int
proc k2 (A : ?) (x : A) : Int = three
""")
  doAssert defs6.len == 1
  let (ety6, etm6) = eraseDef(defs6[0].tyTm, defs6[0].tmTm)
  doAssert not hasErased(ety6) and not hasErased(etm6)
  doAssert teleErased(ety6).len == 0 and lamErased(etm6).len == 0,
    "both binders inferred q0, so the erased def is nullary"
  let w6 = eval(etm6, @[])
  doAssert w6.whnf.kind == wRef, "erased body is the postulate reference"
  echo "ok: inferred-q0 binders erase; def becomes nullary"

  echo "ALL ERASE TESTS PASSED"
