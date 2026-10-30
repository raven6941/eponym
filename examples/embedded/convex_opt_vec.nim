# Convex optimization with dimension-indexed vector variables (Issue #110).
#
# This extends convex_opt.nim (single-variable DCP) to the case that
# actually requires dependent types: vector variables `x = [x0..x_{n-1}]`
# with the dimension `n` tracked in the type, and multi-variable
# objectives whose variables have *different* dimensions.
#
# What dependent types buy here (all beyond Scala's type system, where
# Aaron had the single-variable DCP rules encoded):
# - `vDot n e1 e2` demands both sides have dimension `n`: a mismatch is
#   a compile-time error (18a), not a NumPy-style runtime shape error.
# - `quadForm n P x` needs `P : Mat n n` square *and* `x : VExpr n` of
#   matching dimension (18b); PSD-ness of P is the DCP side condition.
# - `vMatVec m n A e : VExpr m` threads dimensions through linear maps,
#   so `||A x - b||`-style residuals line up by construction.
#
# The headline demo is logistic regression, not least squares: for
# `||Ax-b||^2` convexity is trivially obvious from the quadratic form
# (Aaron's note on #110). Here convexity is genuinely non-obvious -- it
# goes through the DCP composition rule "convex-nondecreasing atom
# (softplus) of affine", i.e. `cvLogSum` below. CVXPY would run this
# analysis at solve() time and raise DCPError on violations; here a
# violation stops compilation of this file.
#
# The DCP and dimension proofs run at compile time. Runtime evaluation of
# the custom expression tree is compile-time-only until the representation
# backend can lower it to host variants; this strict block never interprets
# Values. The `vafMatVec` rule is a postulate, not a `data` constructor,
# for a principled reason: constructors of a parameterized family must
# target the family at the *same* params (`Vec`'s `cons` targets
# `Vec A`, never `Vec B`), but matvec changes the dimension from `n`
# to `m`. Dependent index telescopes (`Pi(n: Nat, VExpr n -> Univ)`)
# would allow it as a constructor, but the `data` desugar's eliminator
# generator does not support them (it renames index binders without
# substituting later index types). So the dimension-preserving rules
# are an inductive family and the dimension-changing composition is a
# lemma-axiom -- the same "typed API over untrusted backend" pattern
# as paxos_session.nim's postulated transport ops.

import eponym_mac

eponymBlock:
  # Prelude import (issue #131): Nat, zero, suc, add, mul from lib/nat.ep
  # (was a per-file data(Nat, ...) redefinition before #131).
  import "../../lib/nat.ep"

  postulate(Int, Univ)

  # Matrices: values abstract, dimensions in the type.
  postulate(Mat, Nat -> Nat -> Univ)
  postulate(VectorData, Nat -> Univ)
  # PSD-ness: the DCP side condition for quadForm. DCP tools check it
  # numerically at solve time; here it is an explicit assumption.
  postulate(PSD, Pi(n: Nat, Mat[n, n] -> Univ))

  # Vector expressions indexed by dimension. vMul is in the AST but admits
  # NO certificate rule: the elementwise product of two variables is the
  # vector analog of x*x -- the classic DCP violation -- and the absence
  # of a rule is the check (see 18c).
  data(VExpr, Nat -> Univ):
    proc vVar(n: Nat): VExpr[n]
    proc vConstV(n: Nat): VExpr[n]
    proc vData(n: Nat, values: VectorData[n]): VExpr[n]
    proc vPlus(n: Nat, e1: VExpr[n], e2: VExpr[n]): VExpr[n]
    proc vMinus(n: Nat, e1: VExpr[n], e2: VExpr[n]): VExpr[n]
    proc vScale(n: Nat, k: Nat, e: VExpr[n]): VExpr[n]
    proc vMatVec(m: Nat, n: Nat, A: Mat[m, n], e: VExpr[n]): VExpr[m]
    proc vMul(n: Nat, e1: VExpr[n], e2: VExpr[n]): VExpr[n]

  # Scalar expressions: the convex_opt.nim core (eConst/ePlus/eScaleN/eSq)
  # plus vector-to-scalar projections. logistic is the softplus atom
  # log(1+exp(e)); vLogSum is sum-of-softplus-losses, the logistic-
  # regression objective shape.
  data(CExpr, Univ):
    proc eConst(c: Int): CExpr
    proc ePlus(e1: CExpr, e2: CExpr): CExpr
    proc eScaleN(k: Nat, e: CExpr): CExpr
    proc eSq(e: CExpr): CExpr
    proc logistic(e: CExpr): CExpr
    proc vDot(n: Nat, e1: VExpr[n], e2: VExpr[n]): CExpr
    proc vSum(n: Nat, e: VExpr[n]): CExpr
    proc vLogSum(n: Nat, e: VExpr[n]): CExpr
    proc norm1(n: Nat, e: VExpr[n]): CExpr
    proc sumSq(n: Nat, e: VExpr[n]): CExpr
    proc quadForm(n: Nat, P: Mat[n, n], x: VExpr[n]): CExpr

  # Affine vector expressions, dimension-indexed (n is a parameter,
  # Vec-style, so the index type VExpr[n] -> Univ stays non-dependent).
  data(VAffine, [n: Nat], VExpr[n] -> Univ):
    proc vafVar(): VAffine[n, vVar[n]()]
    proc vafConstV(): VAffine[n, vConstV[n]()]
    proc vafData(values: VectorData[n]): VAffine[n, vData[n](values)]
    proc vafPlus(e1: VExpr[n], e2: VExpr[n], h1: VAffine[n, e1], h2: VAffine[n, e2]):
      VAffine[n, vPlus[n](e1, e2)]
    proc vafMinus(e1: VExpr[n], e2: VExpr[n], h1: VAffine[n, e1], h2: VAffine[n, e2]):
      VAffine[n, vMinus[n](e1, e2)]
    proc vafScale(k: Nat, e: VExpr[n], h: VAffine[n, e]):
      VAffine[n, vScale[n](k, e)]

  # Linear map of affine is affine (dimension-changing: postulate, see
  # the header note for why it cannot be a constructor).
  postulate(vafMatVec, Pi(m: Nat, n: Nat, A: Mat[m, n], e: VExpr[n],
    VAffine[n, e] -> VAffine[m, vMatVec[m, n](A, e)]))

  # Affine scalars: the DCP base cases plus affine-preserving compositions.
  # afDotConst: dot with a constant vector is a linear functional.
  data(Affine, CExpr -> Univ):
    proc afConst(c: Int): Affine[eConst(c)]
    proc afPlus(e1: CExpr, e2: CExpr, h1: Affine[e1], h2: Affine[e2]):
      Affine[ePlus(e1, e2)]
    proc afScaleN(k: Nat, e: CExpr, h: Affine[e]): Affine[eScaleN(k, e)]
    proc afDotConst(n: Nat, e: VExpr[n], h: VAffine[n, e]):
      Affine[vDot[n](vConstV[n](), e)]
    proc afSum(n: Nat, e: VExpr[n], h: VAffine[n, e]): Affine[vSum[n](e)]

  # Convex scalars: the DCP composition rules as constructors.
  # cvLogistic is the interesting one: softplus is convex *nondecreasing*,
  # so its argument must be convex (affine qualifies) -- this is the rule
  # that makes logistic regression check, and it has no analog in the
  # single-variable quadratic demo.
  data(Convex, CExpr -> Univ):
    proc cvAffine(e: CExpr, h: Affine[e]): Convex[e]
    proc cvPlus(e1: CExpr, e2: CExpr, h1: Convex[e1], h2: Convex[e2]):
      Convex[ePlus(e1, e2)]
    proc cvScaleN(k: Nat, e: CExpr, h: Convex[e]): Convex[eScaleN(k, e)]
    proc cvSq(e: CExpr, h: Affine[e]): Convex[eSq(e)]
    proc cvLogistic(e: CExpr, h: Convex[e]): Convex[logistic(e)]
    proc cvSumSq(n: Nat, e: VExpr[n], h: VAffine[n, e]): Convex[sumSq[n](e)]
    proc cvLogSum(n: Nat, e: VExpr[n], h: VAffine[n, e]): Convex[vLogSum[n](e)]
    proc cvNorm1(n: Nat, e: VExpr[n], h: VAffine[n, e]): Convex[norm1[n](e)]
    proc cvQuadForm(n: Nat, P: Mat[n, n], hp: PSD[n](P), x: VExpr[n], h: VAffine[n,
        x]): Convex[quadForm[n](P, x)]

  # The objective position: minimize demands the convexity certificate.
  proc minimize(e: CExpr, h: Convex[e]): CExpr = e

  # Logistic regression: minimize sum_i softplus((A x)_i - b_i) with
  # A : Mat m n and b an explicitly mapped constant vector of dim m.
  # The certificate: A x - b is affine (matvec of affine, minus const),
  # and sum-of-softplus of affine is convex by cvLogSum.
  proc lrTerm(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]): CExpr =
    vLogSum[m](vMinus[m](vMatVec[m, n](A, vVar[n]()), vData[m](b)))

  proc lrCert(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]):
      Convex[lrTerm(m, n, A, b)] =
    cvLogSum[m](vMinus[m](vMatVec[m, n](A, vVar[n]()), vData[m](b)), vafMinus[m](
        vMatVec[m, n](A, vVar[n]()), vData[m](b), vafMatVec[m, n](A, vVar[n](), vafVar[
        n]()), vafData[m](b)))

  proc lrProb(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]): CExpr =
    minimize(lrTerm(m, n, A, b), lrCert(m, n, A, b))

  proc shiftedLrTerm(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]):
      CExpr = ePlus(lrTerm(m, n, A, b), eConst(5))
  proc shiftedLrCert(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]):
      Convex[shiftedLrTerm(m, n, A, b)] =
    cvPlus(lrTerm(m, n, A, b), eConst(5), lrCert(m, n, A, b),
      cvAffine(eConst(5), afConst(5)))
  proc shiftedLrProb(m: Nat, n: Nat, A: Mat[m, n], b: VectorData[m]):
      CExpr = minimize(shiftedLrTerm(m, n, A, b),
                       shiftedLrCert(m, n, A, b))

  # Two variables of *different* dimensions in one objective: logistic
  # loss on x (dim n) plus an l1 penalty on y (dim m). Both check, and
  # their dimensions stay distinct throughout the certificate.
  proc twoVarTerm(p: Nat, n: Nat, m: Nat, A: Mat[p, n]): CExpr =
    ePlus(vLogSum[p](vMinus[p](vMatVec[p, n](A, vVar[n]()), vConstV[p]())),
          norm1[m](vVar[m]()))

  proc twoVarCert(p: Nat, n: Nat, m: Nat, A: Mat[p, n]):
      Convex[twoVarTerm(p, n, m, A)] =
    cvPlus(vLogSum[p](vMinus[p](vMatVec[p, n](A, vVar[n]()), vConstV[p]())),
           norm1[m](vVar[m]()),
      cvLogSum[p](vMinus[p](vMatVec[p, n](A, vVar[n]()), vConstV[p]()), vafMinus[p](
          vMatVec[p, n](A, vVar[n]()), vConstV[p](), vafMatVec[p, n](A, vVar[n](),
          vafVar[n]()), vafConstV[p]())),
      cvNorm1[m](vVar[m](), vafVar[m]()))

  proc twoVarProb(p: Nat, n: Nat, m: Nat, A: Mat[p, n]): CExpr =
    minimize(twoVarTerm(p, n, m, A), twoVarCert(p, n, m, A))

  # Portfolio risk term x' P x: P must be square (Mat n n) and PSD, x must
  # have dimension n. PSD-ness is discharged by postulate (DCP tools check
  # it numerically at solve time). Dimension literals overload as Nat.
  postulate(eye2, Mat[2, 2])
  postulate(psdEye2, PSD[2](eye2))

  proc qfTerm(): CExpr =
    quadForm[2](eye2, vVar[2]())

  proc qfCert(): Convex[qfTerm()] =
    cvQuadForm[2](eye2, psdEye2, vVar[2](), vafVar[2]())

  proc qfProb(): CExpr = minimize(qfTerm(), qfCert())

  # These checked objectives build custom expression trees. Until the
  # representation backend can lower those trees to host variants, keep
  # the certified terms compile-time-only rather than interpreting Values.
  compileTimeOnly(minimize)
  compileTimeOnly(lrTerm)
  compileTimeOnly(lrCert)
  compileTimeOnly(lrProb)
  compileTimeOnly(shiftedLrTerm)
  compileTimeOnly(shiftedLrCert)
  compileTimeOnly(shiftedLrProb)
  compileTimeOnly(twoVarTerm)
  compileTimeOnly(twoVarCert)
  compileTimeOnly(twoVarProb)
  compileTimeOnly(qfTerm)
  compileTimeOnly(qfCert)
  compileTimeOnly(qfProb)

proc main() =
  echo "convex_opt_vec: DCP-checked logistic regression, embedded."
  echo "  lrTerm = vLogSum m (vMinus m (vMatVec m n A (vVar n)) (vData m b))"
  echo "  elaborated with a Convex certificate (softplus-of-affine, cvLogSum);"
  echo "  `minimize` accepted it at compile time. Dimension mismatches"
  echo "  (vDot, quadForm) and non-DCP vector products (vMul) are"
  echo "  compile-time errors (examples/ep/18a,18b,18c-*-neg.ep)."
  echo "  objective evaluation is deferred until expression trees have a"
  echo "  representation-compiled host layout; no Value interpreter is used."

when isMainModule:
  main()
