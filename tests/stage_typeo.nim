## Stage typeo via RelGoal: the 1st projection of the typing relation
##
## Takes typeo as RelGoal data, with ty static (ground) and tm dynamic.
## Derives a type-specialized checker via stageGoal rules.
##
## Compare to rel_elab.typeo (hand-written). This derives it.
## See src/staging/bench_typeo.nim for the wall-clock benchmark.
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
import strutils

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
  ## Exported for the issue #19/#20 staging benchmark (bench_typeo.nim).
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

  # Partially deduce typeo(tm, nat, ctx): ty=nat static, tm/ctx dynamic.
  # Expected: lam branch pruned (nat vs arr mismatch); recursive calls
  # with the same signature become calls to the specialized relation,
  # calls with a dynamic ty get their own (generic) specialization.
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mIn, mIn], body: typeoData())
  var ctx = newSpecCtx(relEnv, fuel = 8)
  var staticParams = initTable[string, RTerm]()
  staticParams["ty"] = natTy()  # ty = nat, static

  # tm and ctx are dynamic (runtime inputs)
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")

  let top = specializeRelation(ctx, "typeo", staticParams, dynamicVars)

  echo "Specialized relation: ", top
  echo ""
  for name, e in ctx.specs:
    echo "--- ", name, "(", e.params.join(", "), ") ---"
    echo "  ", e.body
    echo ""
  echo "Expected: ", top, " has lam branch pruned (nat vs arr(d,c) mismatch);"
  echo "zero, suc, var, app branches specialized to ty=nat, with recursive"
  echo "calls to the specialized relations (not inlined — recursion is on"
  echo "the dynamic tm). A second, fully-dynamic specialization covers the"
  echo "app branch's dynamically-typed subterms."
