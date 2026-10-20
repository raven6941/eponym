# Convex optimization with a DCP-checked objective (Issue #101).
#
# Disciplined convex programming (Grant, Boyd & Ye 2006) is already a type
# system: curvature (constant/affine/convex/concave) is a type, the
# composition rules are typing rules, and `is_dcp()` is a type checker.
# CVXPY runs it at `solve()` time and raises DCPError on violations. Here
# the same rules run at *compile* time: the `Convex` family below is the
# DCP rule table as datatype constructors, and `minimize` demands a
# `Convex e` certificate in the objective position. A non-DCP objective
# (e.g. `x*x`) is not a runtime DCPError -- it is a compile-time
# elaboration error (see examples/ep/17a-convex-neg.ep).
#
# The `eMul` constructor is deliberately in the AST but admits NO `Convex`
# rule: the product of two variables is the classic DCP violation, and the
# absence of a rule is the check. `eScaleN` takes a `Nat` scalar so
# nonnegativity of the scale is by construction (negative scaling would
# flip convex to concave -- a separate `Concave` family, not needed here).
#
# The example: 2*(x-3)^2 + x, convex by construction. `quadExpr` is the
# reified expression, `quadConvex` its DCP certificate, and `prob` shows
# `minimize` accepting it. The Nim driver interprets the runtime Value of
# `prob`, so its ternary search consumes the same expression the checker saw.
#
# Note the two-layer shape (cf. paxos_session.nim): the proof layer is
# checked at compile time by the elaborator; the running layer interprets
# the checked objective through the Value bridge. CVXPY's DCP check happens
# at solve() time, after the problem is built; here a DCP violation stops
# compilation of this file.

import std/tables
import eponym_mac
import eponym_embed
import eponym_init
import elab

eponymBlock:
  # Prelude import (issue #131): Nat, zero, suc, add, mul from lib/nat.ep
  # (was a per-file data(Nat, ...) redefinition before #131).
  import "../../lib/nat.ep"

  postulate(Int, Univ)

  # Expression language, one variable. eMul is in the AST but has no
  # Convex rule -- that absence IS the DCP check for products.
  data(CExpr, Univ):
    proc eVar(): CExpr
    proc eConst(c: Int): CExpr
    proc ePlus(e1: CExpr, e2: CExpr): CExpr
    proc eMinus(e1: CExpr, e2: CExpr): CExpr
    proc eMul(e1: CExpr, e2: CExpr): CExpr
    proc eScaleN(k: Nat, e: CExpr): CExpr
    proc eSq(e: CExpr): CExpr
    proc eExp(e: CExpr): CExpr
    proc eMax(e1: CExpr, e2: CExpr): CExpr

  # Affine expressions: the DCP base cases (constants, the variable) and
  # the affine-preserving compositions.
  data(Affine, CExpr -> Univ):
    proc afVar(): Affine[eVar()]
    proc afConst(c: Int): Affine[eConst(c)]
    proc afPlus(e1: CExpr, e2: CExpr, h1: Affine[e1], h2: Affine[e2]):
      Affine[ePlus(e1, e2)]
    proc afMinus(e1: CExpr, e2: CExpr, h1: Affine[e1], h2: Affine[e2]):
      Affine[eMinus(e1, e2)]
    proc afScaleN(k: Nat, e: CExpr, h: Affine[e]): Affine[eScaleN(k, e)]

  # Convex expressions: the DCP composition rules as constructors.
  # cvSq/cvExp demand an *affine* argument (convex atom of affine is
  # convex; of general convex it is not DCP-certifiable without sign
  # info -- the conservative gap DCP is known for).
  data(Convex, CExpr -> Univ):
    proc cvAffine(e: CExpr, h: Affine[e]): Convex[e]
    proc cvPlus(e1: CExpr, e2: CExpr, h1: Convex[e1], h2: Convex[e2]):
      Convex[ePlus(e1, e2)]
    proc cvScaleN(k: Nat, e: CExpr, h: Convex[e]): Convex[eScaleN(k, e)]
    proc cvSq(e: CExpr, h: Affine[e]): Convex[eSq(e)]
    proc cvExp(e: CExpr, h: Affine[e]): Convex[eExp(e)]
    proc cvMax(e1: CExpr, e2: CExpr, h1: Convex[e1], h2: Convex[e2]):
      Convex[eMax(e1, e2)]

  # The objective position: minimize demands the convexity certificate.
  proc minimize(e: CExpr, h: Convex[e]): CExpr = e

  # f(x) = 2*(x-3)^2 + x, as a reified expression...
  # Integer literals overload: 2 elaborates as Nat (eScaleN's scalar),
  # 3 as primitive Int (eConst's payload) -- the elaborator decides
  # from the expected type, exactly as in string syntax (Issue #115).
  proc quadExpr(): CExpr =
    ePlus(eScaleN(2, eSq(eMinus(eVar(), eConst(3)))), eVar())

  # ...with its DCP certificate, built bottom-up from the rule table:
  # x-3 affine, sq of affine convex, nonneg scale of convex convex,
  # x affine hence convex, sum of convex convex.
  proc quadConvex(): Convex[quadExpr()] =
    cvPlus(eScaleN(2, eSq(eMinus(eVar(), eConst(3)))), eVar(),
      cvScaleN(2, eSq(eMinus(eVar(), eConst(3))),
        cvSq(eMinus(eVar(), eConst(3)),
          afMinus(eVar(), eConst(3), afVar(), afConst(3)))),
      cvAffine(eVar(), afVar()))

  # The problem: accepted only because the certificate checks.
  proc prob(): CExpr = minimize(quadExpr(), quadConvex())
  runtimeValue(prob)
  proc shiftedExpr(): CExpr = ePlus(quadExpr(), eConst(11))
  proc shiftedCert(): Convex[shiftedExpr()] =
    cvPlus(quadExpr(), eConst(11), quadConvex(),
      cvAffine(eConst(11), afConst(11)))
  proc shiftedProb(): CExpr = minimize(shiftedExpr(), shiftedCert())
  runtimeValue(shiftedProb)

# --- Normal Nim program: optimize the certified-convex objective --------
# Ternary search is a *local* method: it is only correct because `f` is
# convex (proved above at compile time). On a non-convex function this
# driver could return a mere local minimum; the `Convex` certificate is
# what rules that out. CVXPY would run its DCP check at solve() time;
# here the check ran when this file was compiled.

proc ctorArg(expr: Value, index: int): Value =
  if expr.whnfKind != wRef or expr.whnfSpineLen <= index or
      expr.whnfSpineKind(index) != eApp:
    raise newException(ValueError, "malformed certified CExpr constructor")
  expr.whnfSpineArg(index)

proc ctorId(globals: Globals, name: string): int =
  if name notin globals:
    raise newException(ValueError, "certified CExpr constructor missing: " & name)
  globals[name].tm.refId

proc evalCertifiedExpr(expr: Value, x: int, globals: Globals): int =
  let id = expr.whnfRefId
  if id == ctorId(globals, "eVar"):
    return x
  if id == ctorId(globals, "eConst"):
    let literal = ctorArg(expr, 0)
    if literal.whnfKind != wInt:
      raise newException(ValueError, "eConst payload is not an Int")
    return literal.whnfIntVal
  if id == ctorId(globals, "ePlus"):
    return evalCertifiedExpr(ctorArg(expr, 0), x, globals) +
      evalCertifiedExpr(ctorArg(expr, 1), x, globals)
  if id == ctorId(globals, "eMinus"):
    return evalCertifiedExpr(ctorArg(expr, 0), x, globals) -
      evalCertifiedExpr(ctorArg(expr, 1), x, globals)
  if id == ctorId(globals, "eScaleN"):
    let scale = ctorArg(expr, 0)
    if scale.whnfKind != wNatLit:
      raise newException(ValueError, "eScaleN payload is not a Nat literal")
    return scale.whnfNatLitVal * evalCertifiedExpr(ctorArg(expr, 1), x, globals)
  if id == ctorId(globals, "eSq"):
    let value = evalCertifiedExpr(ctorArg(expr, 0), x, globals)
    return value * value
  raise newException(ValueError, "unsupported constructor in certified CExpr")

proc evalCertifiedObjectiveValue(checked: tuple[value: Value,
                                               globals: Globals], x: int): int =
  evalCertifiedExpr(checked.value, x, checked.globals)

proc evalCertifiedObjective*(x: int): int =
  evalCertifiedObjectiveValue(probRuntimeValue(), x)

proc evalShiftedCertifiedObjective*(x: int): int =
  evalCertifiedObjectiveValue(shiftedProbRuntimeValue(), x)

proc ternaryMin(lo, hi: int,
                checked: tuple[value: Value, globals: Globals]):
    tuple[xstar, fstar: int] =
  var a = lo
  var b = hi
  while b - a > 3:
    let m1 = a + (b - a) div 3
    let m2 = b - (b - a) div 3
    if evalCertifiedObjectiveValue(checked, m1) <=
        evalCertifiedObjectiveValue(checked, m2): b = m2
    else: a = m1
  var best = a
  var bestV = evalCertifiedObjectiveValue(checked, a)
  for x in (a + 1)..b:
    let v = evalCertifiedObjectiveValue(checked, x)
    if v < bestV:
      best = x
      bestV = v
  (best, bestV)

proc main() =
  echo "convex_opt: DCP-checked convex optimization, embedded."
  echo "  f(x) = 2*(x-3)^2 + x elaborated with a Convex certificate;"
  echo "  `minimize` accepted it at compile time (x*x would not:"
  echo "  examples/ep/17a-convex-neg.ep)."
  let checkedProb = probRuntimeValue()
  let (xstar, fstar) = ternaryMin(-100, 100, checkedProb)
  echo "  ternary search on [-100, 100]: x* = ", xstar, ", f(x*) = ", fstar
  echo "  (convexity certifies this local minimum is the global one)"

when isMainModule:
  main()
