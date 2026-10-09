## Stage the relational dependent elaborator via RelGoal
##
## Express infero/checko as RelGoal data, then specialize with stagegoal.
## This is the "staged relational path" for comparison against the direct
## elaborator.

import staging/relgoal
import staging/stagegoal
import staging/modes
import minikanren
import rel_elab_dep  # constructors
import tables

# --- infero as RelGoal ------------------------------------------------------
# infero(tm, ty, ctx):
#   tm=zero, ty=nat
#   ∨ tm=suc(n), infero(n,nat,ctx), ty=nat
#   ∨ tm=var(i), lookupO(ctx,i,ty)
#   ∨ tm=app(f,a), f:Pi(d,c), a:d, ty=c   [non-dep]
#   ∨ tm=pi(d,c), d:univ, c:univ, ty=univ
#
# Note: lookupO needs to be expressed relationally too. For the MVP,
# we inline a simple version for small indices.

proc inferoData*(): RelGoal =
  let tm = ratom("__var_tm")
  let ty = ratom("__var_ty")
  let ctx = ratom("__var_ctx")

  # Branch: zero : nat
  let zeroCase = rgConj(rgEq(tm, zeroTm()), rgEq(ty, natTy()))

  # Branch: suc(n) : nat
  let sucCase = rgFresh("n",
    rgConj(rgEq(tm, sucTm(ratom("__var_n"))),
      rgConj(rgCall("infero", @[ratom("__var_n"), natTy(), ctx]),
        rgEq(ty, natTy()))))

  # Branch: var(0) : ty0 if ctx=(ty0._)
  # (MVP: only handle index 0; general lookup needs recursion)
  let var0Case = rgFresh("ty0", rgFresh("tl",
    rgConj(rgEq(tm, varTm(0)),
      rgConj(rgEq(ctx, rpair(ratom("__var_ty0"), ratom("__var_tl"))),
        rgEq(ty, ratom("__var_ty0"))))))

  # Branch: app(f,a) : c if f:Pi(d,c), a:d
  let appCase = rgFresh("f", rgFresh("a", rgFresh("d", rgFresh("c",
    rgConj(rgEq(tm, appTm(ratom("__var_f"), ratom("__var_a"))),
      rgConj(rgCall("infero", @[ratom("__var_f"),
                                piTy(ratom("__var_d"), ratom("__var_c")),
                                ctx]),
        rgConj(rgCall("checko", @[ratom("__var_a"), ratom("__var_d"), ctx]),
          rgEq(ty, ratom("__var_c"))))))))))

  # Combine with disj
  rgDisj(zeroCase,
    rgDisj(sucCase,
      rgDisj(var0Case, appCase)))

# --- checko as RelGoal ------------------------------------------------------

proc checkoData*(): RelGoal =
  let tm = ratom("__var_tm")
  let ty = ratom("__var_ty")
  let ctx = ratom("__var_ctx")

  # Branch: lam(b) : Pi(d,c) if b:c in (d.ctx)
  let lamCase = rgFresh("b", rgFresh("d", rgFresh("c",
    rgConj(rgEq(tm, lamTm(ratom("__var_b"))),
      rgConj(rgEq(ty, piTy(ratom("__var_d"), ratom("__var_c"))),
        rgCall("checko", @[ratom("__var_b"), ratom("__var_c"),
                           rpair(ratom("__var_d"), ctx)]))))))

  # Branch: nil : Vec(A,zero)
  let nilCase =
    rgConj(rgEq(tm, nilTm()),
      rgEq(ty, vecTy(ratom("__var_A"), zeroTm())))

  # Branch: cons(h,t) : Vec(A,suc(n)) if h:A, t:Vec(A,n)
  let consCase = rgFresh("h", rgFresh("t", rgFresh("a", rgFresh("n",
    rgConj(rgEq(tm, consTm(ratom("__var_h"), ratom("__var_t"))),
      rgConj(rgEq(ty, vecTy(ratom("__var_a"), sucTm(ratom("__var_n")))),
        rgConj(rgCall("checko", @[ratom("__var_h"), ratom("__var_a"), ctx]),
          rgCall("checko", @[ratom("__var_t"),
                             vecTy(ratom("__var_a"), ratom("__var_n")),
                             ctx]))))))))

  # Branch: fallback to infero
  let inferCase = rgFresh("ty2",
    rgConj(rgCall("infero", @[tm, ratom("__var_ty2"), ctx]),
      rgEq(ty, ratom("__var_ty2"))))

  rgDisj(lamCase,
    rgDisj(nilCase,
      rgDisj(consCase, inferCase)))

# --- Staging ----------------------------------------------------------------

proc stageCheckoForType*(ty: RTerm): RelGoal =
  ## Specialize checko for a static type ty (tm dynamic).
  ## Returns the residual RelGoal.
  let relEnv = initTable[string, RelDef]()
  # TODO: populate relEnv with inferoData and checkoData as RelDefs
  # For MVP, we use stagegoal directly on checkoData with ty bound.
  let ctx = newSpecCtx(relEnv, fuel = 8)
  # The staging: checko(tm, ty_static, ctx_dynamic)
  # We need to set up the static/dynamic distinction.
  # For now, return the unstaged version (staging is future work).
  checkoData()
