## Stage the relational dependent elaborator via RelGoal
##
## Complete RelGoal encoding of infero/checko for the fragment, suitable
## for partial deduction via stagegoal and compilation via relcompile.
##
## Fragment: Pi (non-dep), lam, app, Nat (zero/suc), Vec (nil/cons),
## vars (de Bruijn indices 0-2 explicit; larger indices not in fragment).

import staging/relgoal
import staging/stagegoal
import staging/modes
import staging/relcompile
import minikanren
import rel_elab_dep
import tables
import sets

# --- Helpers ---------------------------------------------------------------

proc v(name: string): RTerm = ratom("__var_" & name)

# --- infero as RelGoal -------------------------------------------------------
# infero(tm, ty, ctx) with modes (in, out, in).

proc inferoData*(): RelGoal =
  let tm = v("tm"); let ty = v("ty"); let ctx = v("ctx")

  # zero : nat
  let zeroCase = rgConj(rgEq(tm, zeroTm()), rgEq(ty, natTy()))

  # suc(n) : nat if n : nat
  let sucCase = rgFresh("n",
    rgConj(rgEq(tm, sucTm(v("n"))),
      rgConj(rgCall("infero", @[v("n"), natTy(), ctx]),
        rgEq(ty, natTy()))))

  # var(0): ctx = (ty0 . tl)
  let var0Case = rgFresh("ty0", rgFresh("tl",
    rgConj(rgEq(tm, varTm(0)),
      rgConj(rgEq(ctx, rpair(v("ty0"), v("tl"))),
        rgEq(ty, v("ty0"))))))

  # var(1): ctx = (h . (ty1 . tl))
  let var1Case = rgFresh("h", rgFresh("ty1", rgFresh("tl",
    rgConj(rgEq(tm, varTm(1)),
      rgConj(rgEq(ctx, rpair(v("h"), rpair(v("ty1"), v("tl")))),
        rgEq(ty, v("ty1")))))))

  # var(2): ctx = (h1 . (h2 . (ty2 . tl)))
  let var2Case = rgFresh("h1", rgFresh("h2", rgFresh("ty2", rgFresh("tl",
    rgConj(rgEq(tm, varTm(2)),
      rgConj(rgEq(ctx, rpair(v("h1"), rpair(v("h2"), rpair(v("ty2"), v("tl"))))),
        rgEq(ty, v("ty2"))))))))

  # app(f,a) : c if f : Pi(d,c), a : d  (non-dep; checko falls back to infero)
  let appCase = rgFresh("f", rgFresh("a", rgFresh("d", rgFresh("c",
    rgConj(rgEq(tm, appTm(v("f"), v("a"))),
      rgConj(rgCall("checko", @[v("f"), piTy(v("d"), v("c")), ctx]),
        rgConj(rgCall("checko", @[v("a"), v("d"), ctx]),
          rgEq(ty, v("c")))))))))

  # pi(d,c) : univ if d:univ, c:univ in (d.ctx)
  let piCase = rgFresh("d", rgFresh("c",
    rgConj(rgEq(tm, piTy(v("d"), v("c"))),
      rgConj(rgCall("checko", @[v("d"), univTy(), ctx]),
        rgConj(rgCall("checko", @[v("c"), univTy(), rpair(v("d"), ctx)]),
          rgEq(ty, univTy()))))))

  rgDisj(zeroCase, rgDisj(sucCase,
    rgDisj(var0Case, rgDisj(var1Case,
      rgDisj(var2Case, rgDisj(appCase, piCase))))))

# --- checko as RelGoal -------------------------------------------------------
# checko(tm, ty, ctx) with modes (in, in, in).

proc checkoData*(): RelGoal =
  let tm = v("tm"); let ty = v("ty"); let ctx = v("ctx")

  # lam(b) : Pi(d,c) if b : c in (d.ctx)
  let lamCase = rgFresh("b", rgFresh("d", rgFresh("c",
    rgConj(rgEq(tm, lamTm(v("b"))),
      rgConj(rgEq(ty, piTy(v("d"), v("c"))),
        rgCall("checko", @[v("b"), v("c"), rpair(v("d"), ctx)]))))))

  # nil : Vec(A, zero)
  let nilCase = rgFresh("A",
    rgConj(rgEq(tm, nilTm()),
      rgEq(ty, vecTy(v("A"), zeroTm()))))

  # cons(h,t) : Vec(A, suc(n)) if h:A, t:Vec(A,n)
  let consCase = rgFresh("h", rgFresh("t", rgFresh("A", rgFresh("n",
    rgConj(rgEq(tm, consTm(v("h"), v("t"))),
      rgConj(rgEq(ty, vecTy(v("A"), sucTm(v("n")))),
        rgConj(rgCall("checko", @[v("h"), v("A"), ctx]),
          rgCall("checko", @[v("t"), vecTy(v("A"), v("n")), ctx]))))))))

  # fallback: infer and unify
  let inferCase = rgFresh("ty2",
    rgConj(rgCall("infero", @[tm, v("ty2"), ctx]),
      rgEq(ty, v("ty2"))))

  rgDisj(lamCase, rgDisj(nilCase, rgDisj(consCase, inferCase)))

# --- RelEnv ------------------------------------------------------------------

proc buildRelEnv*(): Table[string, RelDef] =
  result = initTable[string, RelDef]()
  result["infero"] = RelDef(
    name: "infero",
    params: @["tm", "ty", "ctx"],
    modes: @[mIn, mOut, mIn],
    body: inferoData()
  )
  result["checko"] = RelDef(
    name: "checko",
    params: @["tm", "ty", "ctx"],
    modes: @[mIn, mIn, mIn],
    body: checkoData()
  )

# --- Driver macro ------------------------------------------------------------

import macros

macro stagedCheckoVec2Procs*(): untyped =
  ## Specialize checko(tm, Vec(Nat, 2), ctx) at compile time and emit one
  ## Nim proc per specialized relation, plus a `stagedCheckoVec2(tm, ctx)`
  ## template. Single build step.
  var relEnv = buildRelEnv()
  var spCtx = newSpecCtx(relEnv, fuel = 12)
  var staticParams = initTable[string, RTerm]()
  staticParams["ty"] = vecTy(natTy(), sucTm(sucTm(zeroTm())))
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")
  let top = specializeRelation(spCtx, "checko", staticParams, dynamicVars)
  result = compileSpecCtx(spCtx)
  let topIdent = ident(top)
  # Build vecTy(natTy(), sucTm(sucTm(zeroTm()))) as AST
  let vec2Node = newCall(ident("vecTy"),
    newCall(ident("natTy")),
    newCall(ident("sucTm"),
      newCall(ident("sucTm"), newCall(ident("zeroTm")))))
  result.add(nnkTemplateDef.newTree(
    ident("stagedCheckoVec2"), newEmptyNode(), newEmptyNode(),
    nnkFormalParams.newTree(ident("Goal"),
      newIdentDefs(ident("tm"), ident("RTerm")),
      newIdentDefs(ident("ctx"), ident("RTerm"))),
    newEmptyNode(), newEmptyNode(),
    newStmtList(newCall(topIdent, ident("tm"), vec2Node, ident("ctx")))))
