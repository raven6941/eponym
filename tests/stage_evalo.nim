## Stage evalo via RelGoal: the 1st projection derived
##
## Takes evalo as RelGoal data, with tm static (ground) and v dynamic.
## Derives the staged evaluator via stageGoal rules.
##
## Compare to src/staged_eval.nim (hand-written). This derives it.

import staging/relgoal
import staging/stagegoal
import staging/modes
import minikanren
import rel_elab   # zeroTm, sucTm
import rel_interp # addTm, mulTm
import tables
import sets
import strutils

# --- evalo as RelGoal data (simplified: zero/suc/add cases) ---
#
# evalo(tm, v):
#   (tm == zero ∧ v == zero)
#   ∨ (fresh n, vn. tm == suc(n) ∧ evalo(n, vn) ∧ v == suc(vn))
#   ∨ (fresh a,b,va,vb. tm == add(a,b) ∧ evalo(a,va) ∧ evalo(b,vb) ∧ addo(va,vb,v))
#
# For prototype, we inline the structure with tm=__var_tm, v=__var_v.

proc evaloData*(): RelGoal =
  ## Exported for the issue #29 differential suite (fuzz_soundness.nim).
  let tm = ratom("__var_tm")
  let v = ratom("__var_v")
  let n = ratom("__var_n")
  let vn = ratom("__var_vn")
  let a = ratom("__var_a")
  let b = ratom("__var_b")
  let va = ratom("__var_va")
  let vb = ratom("__var_vb")

  let zeroCase = rgConj(rgEq(tm, zeroTm()), rgEq(v, zeroTm()))

  let sucCase = rgFresh("n", rgFresh("vn",
    rgConj(rgEq(tm, sucTm(n)),
      rgConj(rgCall("evalo", @[n, vn]),
        rgEq(v, sucTm(vn))))))

  let addCase = rgFresh("a", rgFresh("b", rgFresh("va", rgFresh("vb",
    rgConj(rgEq(tm, addTm(a, b)),
      rgConj(rgCall("evalo", @[a, va]),
        rgConj(rgCall("evalo", @[b, vb]),
          rgCall("addo", @[va, vb, v]))))))))

  rgDisj(zeroCase, rgDisj(sucCase, addCase))

proc addoData*(): RelGoal =
  ## addo as RelGoal data (hand-written mirror of rel_interp.addo).
  ## Exported for the issue #29 differential suite: staged evalo needs
  ## addo in its relEnv — an unknown relation would residualize as a
  ## call to a relation that doesn't exist at toGoal time.
  let a = ratom("__var_a")
  let b = ratom("__var_b")
  let c = ratom("__var_c")
  let zeroCase = rgConj(rgEq(a, zeroTm()), rgEq(c, b))
  let sucCase = rgFresh("ap", rgFresh("cp",
    rgConj(rgEq(a, sucTm(ratom("__var_ap"))),
      rgConj(rgEq(c, sucTm(ratom("__var_cp"))),
        rgCall("addo", @[ratom("__var_ap"), b, ratom("__var_cp")])))))
  rgDisj(zeroCase, sucCase)

when isMainModule:
  echo "=== Staging evalo via RelGoal (partial deduction) ==="
  echo ""

  # Specialize evalo(tm, v) with tm=suc(zero) static, v dynamic (mOut).
  var relEnv = initTable[string, RelDef]()
  relEnv["evalo"] = RelDef(name: "evalo", params: @["tm", "v"],
                           modes: @[mIn, mOut], body: evaloData())
  var ctx = newSpecCtx(relEnv, fuel = 8)
  var staticParams = initTable[string, RTerm]()
  staticParams["tm"] = sucTm(zeroTm())  # tm = suc(zero), ground/static
  # v (__var_v) is mOut: dynamic, must NOT be bound at staging time.
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_v")

  let top = specializeRelation(ctx, "evalo", staticParams, dynamicVars)

  echo "Specialized relation: ", top
  echo ""
  for name, e in ctx.specs:
    echo "--- ", name, "(", e.params.join(", "), ") ---"
    echo "  ", e.body
    echo ""
  echo "The static tm=suc(zero) pruned the zero and add branches."
  echo "The recursive call evalo(n, vn) has n=zero statically known, so it"
  echo "became its own specialization (evalo with tm=zero static)."
  echo "v is mOut (dynamic), so v=suc(vn) stays as a residual equation."
  echo "This is the 1st projection: structure fixed, v dynamic."
  echo ""
  echo "Compare to staged_eval.nim: hand-writes stageEval(suc(zero)) = suc(zero)."
  echo "Here, the RULES derive the residual via branch pruning + specialization."
