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

# --- evalo as RelGoal data (simplified: zero/suc/add cases) ---
#
# evalo(tm, v):
#   (tm == zero ∧ v == zero)
#   ∨ (fresh n, vn. tm == suc(n) ∧ evalo(n, vn) ∧ v == suc(vn))
#   ∨ (fresh a,b,va,vb. tm == add(a,b) ∧ evalo(a,va) ∧ evalo(b,vb) ∧ addo(va,vb,v))
#
# For prototype, we inline the structure with tm=__var_tm, v=__var_v.

proc evaloData(): RelGoal =
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

when isMainModule:
  echo "=== Staging evalo via RelGoal ==="
  echo ""

  # Stage evalo(suc(zero), v) with tm static, v dynamic
  var staticEnv = initTable[string, RTerm]()
  staticEnv["__var_tm"] = sucTm(zeroTm())  # tm = suc(zero), ground/static
  # v (__var_v) is mOut: dynamic, must NOT be bound at staging time.
  # It stays as a residual equation v=suc(vn).
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_v")

  let rg = evaloData()
  echo "evalo RelGoal (tm=__var_tm, v=__var_v):"
  echo "  ", rg
  echo ""

  let staged = stageGoal(rg, staticEnv, dynamicVars)
  echo "Staged with tm=suc(zero) static, v dynamic (mOut):"
  echo "  Result kind: ", staged.kind
  echo ""

  case staged.kind
  of sgDone:
    echo "Fully evaluated at staging time (v is ground — shouldn't happen for v dynamic)"
  of sgFail:
    echo "Statically impossible (tm doesn't match — shouldn't happen)"
  of sgResidual:
    echo "Residual goal:"
    echo "  ", staged.goal
    echo ""
    echo "The static tm=suc(zero) pruned the zero and add branches."
    echo "The unifier learned n=zero and substituted it into the recursive"
    echo "call. v is mOut (dynamic), so v=suc(vn) stays as a residual equation."
    echo "This is the 1st projection: structure fixed, v dynamic."
  echo ""
  echo "Compare to staged_eval.nim: hand-writes stageEval(suc(zero)) = suc(zero)."
  echo "Here, the RULES derive the residual via branch pruning."
