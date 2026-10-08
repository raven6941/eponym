## Stage typeo via RelGoal: the 1st projection of the typing relation
##
## Takes typeo as RelGoal data, with ty static (ground) and tm dynamic.
## Derives a type-specialized checker via stageGoal rules.
##
## Compare to src/elaborator.nim (hand-written). This derives it.
##
## Issue #19: this is the experiment that decides whether
## relational+staging leaves experimental status.

import staging/relgoal
import staging/stagegoal
import staging/modes
import minikanren
import rel_elab   # natTy, arrTy, varTm, lamTm, appTm, zeroTm, sucTm
import tables
import sets

# --- typeo as RelGoal data (STLC + Nat, no Vec) ---
#
# typeo(tm, ty, ctx):
#   (tm == zero ∧ ty == nat)
#   ∨ (fresh n. tm == suc(n) ∧ typeo(n, nat, ctx) ∧ ty == nat)
#   ∨ (fresh ty0, ctxTail. tm == var(0) ∧ ctx == (ty0 . ctxTail) ∧ ty == ty0)
#   ∨ (fresh b, d, c. tm == lam(b) ∧ ty == arr(d,c) ∧ typeo(b, c, (d . ctx)))
#   ∨ (fresh f, a, d, c. tm == app(f,a) ∧ typeo(f, arr(d,c), ctx)
#                          ∧ typeo(a, d, ctx) ∧ ty == c)

proc typeoData*(): RelGoal =
  ## typeo as RelGoal data (hand-written mirror of rel_elab.typeo).
  ## Exported for the issue #24 staging comparison demo.
  let tm = ratom("__var_tm")
  let ty = ratom("__var_ty")
  let ctx = ratom("__var_ctx")

  # Branch 1: zero : nat
  let zeroCase = rgConj(rgEq(tm, zeroTm()), rgEq(ty, natTy()))

  # Branch 2: suc(n) : nat if n : nat
  let sucCase = rgFresh("n",
    rgConj(rgEq(tm, sucTm(ratom("__var_n"))),
      rgConj(rgCall("typeo", @[ratom("__var_n"), natTy(), ctx]),
        rgEq(ty, natTy()))))

  # Branch 3: var(0) : ty0 if ctx = (ty0 . ctxTail)
  let varCase = rgFresh("ty0", rgFresh("ctxTail",
    rgConj(rgEq(tm, varTm(0)),
      rgConj(rgEq(ctx, rpair(ratom("__var_ty0"), ratom("__var_ctxTail"))),
        rgEq(ty, ratom("__var_ty0"))))))

  # Branch 4: lam(b) : (arr d c) if b : c in (d . ctx)
  let lamCase = rgFresh("b", rgFresh("d", rgFresh("c",
    rgConj(rgEq(tm, lamTm(ratom("__var_b"))),
      rgConj(rgEq(ty, arrTy(ratom("__var_d"), ratom("__var_c"))),
        rgCall("typeo", @[ratom("__var_b"), ratom("__var_c"),
                          rpair(ratom("__var_d"), ctx)]))))))

  # Branch 5: app(f, a) : c if f : (arr d c), a : d
  let f = ratom("__var_f")
  let a = ratom("__var_a")
  let d = ratom("__var_d")
  let c = ratom("__var_c")
  let appCase = rgFresh("f", rgFresh("a", rgFresh("d", rgFresh("c",
    rgConj(
      rgEq(tm, appTm(f, a)),
      rgConj(
        rgCall("typeo", @[f, arrTy(d, c), ctx]),
        rgConj(
          rgCall("typeo", @[a, d, ctx]),
          rgEq(ty, c))))))))

  rgDisj(zeroCase,
    rgDisj(sucCase,
      rgDisj(varCase,
        rgDisj(lamCase, appCase))))

when isMainModule:
  echo "=== Staging typeo via RelGoal (Issue #19) ==="
  echo ""

  # Stage typeo(tm, nat, ctx) with ty=nat static, tm/ctx dynamic.
  # Expected: lam branch pruned (nat vs arr mismatch).
  var staticEnv = initTable[string, RTerm]()
  staticEnv["__var_ty"] = natTy()  # ty = nat, static

  # tm and ctx are dynamic (mOut / runtime inputs)
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")

  let rg = typeoData()
  let staged = stageGoal(rg, staticEnv, dynamicVars)

  echo "Staged with ty=nat static, tm/ctx dynamic:"
  echo "  Result kind: ", staged.kind
  echo ""
  case staged.kind
  of sgDone:
    echo "Fully evaluated at staging time (unexpected for dynamic tm)"
  of sgFail:
    echo "Statically impossible (shouldn't happen)"
  of sgResidual:
    echo "Residual goal:"
    echo "  ", staged.goal
    echo ""
    echo "Expected: lam branch pruned (nat vs arr(d,c) mismatch)."
    echo "Remaining: zero, suc, var, app branches specialized to ty=nat."
