## tests/pbt_staged_agreement.nim — Issue #163: property tests pinning
## agreement between the #57 generated-direct residual
## (src/experimental/staging/gen_elabo_full.nim: elaboD / inferD) and the unstaged
## relational elaborator it was staged from (src/experimental/relational/rel_elab_out.nim:
## elabo / inferoOut).
##
## This is the extensional half of the #143 verdict: the direct elaborator
## stays, the relational spec remains as codegen input, and the
## generated-direct residual is the performance path. These properties pin
## that the residual implements the spec on random ground fragment inputs:
##   P1 check-mode differential: for random ground (tm, ty, ctx),
##      elaboD(tm,ty,ctx).isSome == (relational elabo yields an answer),
##      and when both succeed their core terms are structurally equal.
##   P2 infer-mode differential: for random ground (tm, ctx),
##      inferD(tm,ctx).isSome == (relational inferoOut yields an answer),
##      and when both succeed the (ty, etm) pairs are structurally equal.
##
## The residual documents two restrictions the differential respects:
##   - non-ground relational answers are unrepresentable in Option results
##     (dynElabo degrades to none); the suite asserts they never occur on
##     the generated ground fragment (type-uniqueness), rather than
##     silently skipping them.
##   - inferD has no fallback in infer mode for the app-redex branch;
##     the probe shows its ground-fragment reading agrees with the relation
##     (which elaborates the lam in check mode against a fresh Pi).
##
## Run: nim c -r --hints:off --path:src --path:src/eponym --path:src/experimental --path:src/experimental/relational --path:src/experimental/staging tests/pbt_staged_agreement.nim
## Fixed seed 424242 in CI (change Seed locally for fresh fuzzing).

import pbt
import options
import minikanren
import rel_elab_dep    # surface ctors: varTm, lamTm, appTm, piTy, ...
import rel_elab_out    # relational spec: elabo, inferoOut, sucCore, ...
import staging/gen_elabo_full  # residual: elaboD, inferD, rTermEq, rTermGround

const Seed = 424242'u64
const Cases = 200

# --- generators -------------------------------------------------------------
# Ground surface terms over the #57 fragment: atoms, var, suc, app
# (redex + var head), pi, vec, lam, nil, cons, plus #87 nat literals.
# Types come from a small pool; junk (zeroTm as a "type") and out-of-range
# vars exercise the rejection paths.

proc genTy*(r: var Rng): RTerm =
  case r.below(7)
  of 0: natTy()
  of 1: univTy()
  of 2: piTy(natTy(), natTy())
  of 3: piTy(natTy(), piTy(natTy(), natTy()))
  of 4: vecTy(natTy(), sucTm(sucTm(zeroTm())))
  of 5: vecTy(vecTy(natTy(), zeroTm()), zeroTm())
  else: zeroTm()  # junk type: forces rejections

proc genCtx*(r: var Rng, n: int): RTerm =
  result = rnil()
  for _ in 0 ..< n: result = rpair(genTy(r), result)

proc genTm*(r: var Rng, depth: int, maxVar: int): RTerm =
  if depth <= 0:
    case r.below(7)
    of 0: zeroTm()
    of 1: nilTm()
    of 2: ratom("nat")
    of 3: ratom("univ")
    of 4: varTm(r.below(maxVar + 1))
    of 5: rint(r.below(4))  # #87 nat literal
    else: nilTm()
  else:
    case r.below(9)
    of 0: sucTm(genTm(r, depth - 1, maxVar))
    of 1: lamTm(genTm(r, depth - 1, maxVar + 1))
    of 2: appTm(genTm(r, depth - 1, maxVar), genTm(r, depth - 1, maxVar))
    of 3: piTy(genTm(r, depth - 1, maxVar), genTm(r, depth - 1, maxVar + 1))
    of 4: vecTy(genTm(r, depth - 1, maxVar), genTm(r, depth - 1, maxVar))
    of 5: consTm(genTm(r, depth - 1, maxVar), genTm(r, depth - 1, maxVar))
    of 6: varTm(r.below(maxVar + 2))  # sometimes out of range
    else: genTm(r, 0, maxVar)

type CheckCase* = tuple[tm, ty, ctx: RTerm]
type InferCase* = tuple[tm, ctx: RTerm]

proc genCheckCase*(r: var Rng): CheckCase =
  let ctxLen = r.below(4)
  (genTm(r, r.below(3), ctxLen), genTy(r), genCtx(r, ctxLen))

proc genInferCase*(r: var Rng): InferCase =
  let ctxLen = r.below(4)
  (genTm(r, r.below(3), ctxLen), genCtx(r, ctxLen))

# --- relational reference runs ----------------------------------------------

proc relElabo(tm, ty, ctx: RTerm): tuple[ok: bool, etm: RTerm, nonGround: bool] =
  ## First-answer run of the relational elabo/4.
  let q = freshVar()
  let sols = run(q, rel_elab_out.elabo(tm, ty, ctx, q), 1)
  if sols.len == 0: (false, rnil(), false)
  elif not rTermGround(sols[0]): (false, rnil(), true)
  else: (true, sols[0], false)

proc relInfer(tm, ctx: RTerm): tuple[ok: bool, ty, etm: RTerm, nonGround: bool] =
  ## First-answer run of the relational inferoOut/4, paired per the
  ## bench_direct_elabo_full.nim calling convention.
  let qp = freshVar()
  let sols = run(qp, fresh2(proc(ty2, et2: RTerm): Goal =
    conj(inferoOut(tm, ty2, ctx, et2),
      `==`(qp, rpair(ty2, rpair(et2, rnil()))))), 1)
  if sols.len == 0: (false, rnil(), rnil(), false)
  else:
    let ty2 = sols[0].head
    let et2 = sols[0].tail.head
    if not rTermGround(ty2) or not rTermGround(et2):
      (false, rnil(), rnil(), true)
    else: (true, ty2, et2, false)

# --- properties --------------------------------------------------------------

when isMainModule:
  var r = initRng(Seed)
  var skips = 0
  var checkAcc, checkRej = 0
  var inferAcc, inferRej = 0

  let p1 = forAll("check-mode residual agrees with relational elabo",
    r, Cases, genCheckCase,
    proc(c: CheckCase): bool =
      let rd = elaboD(c.tm, c.ty, c.ctx)
      let rel = relElabo(c.tm, c.ty, c.ctx)
      if rel.nonGround:
        inc skips
        echo "non-ground relational answer on ground input (check mode)"
        return false
      if rd.isSome: inc checkAcc else: inc checkRej
      if rd.isSome != rel.ok:
        echo "verdict diff: residual=", rd.isSome, " relational=", rel.ok
        return false
      if rd.isSome and not rTermEq(rd.get, rel.etm):
        echo "core-term diff on accepted case"
        return false
      true)

  let p2 = forAll("infer-mode residual agrees with relational inferoOut",
    r, Cases, genInferCase,
    proc(c: InferCase): bool =
      let rd = inferD(c.tm, c.ctx)
      let rel = relInfer(c.tm, c.ctx)
      if rel.nonGround:
        inc skips
        echo "non-ground relational answer on ground input (infer mode)"
        return false
      if rd.isSome: inc inferAcc else: inc inferRej
      if rd.isSome != rel.ok:
        echo "verdict diff: residual=", rd.isSome, " relational=", rel.ok
        return false
      if rd.isSome and not (rTermEq(rd.get.ty, rel.ty) and
                            rTermEq(rd.get.etm, rel.etm)):
        echo "(ty, etm) pair diff on accepted case"
        return false
      true)

  echo "check-mode: accept=", checkAcc, " reject=", checkRej,
       " | infer-mode: accept=", inferAcc, " reject=", inferRej,
       " | non-ground skips=", skips
  if checkAcc == 0 or checkRej == 0 or inferAcc == 0 or inferRej == 0:
    echo "VACUOUS: one mode saw only accepts or only rejects"
    quit(1)
  if not (p1 and p2): quit(1)
