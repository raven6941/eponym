## Stage typeo via RelGoal: the 1st projection of the typing relation
##
## Takes typeo as RelGoal data, with ty static (ground) and tm dynamic.
## Derives a type-specialized checker via stageGoal rules.
##
## Compare to rel_elab.typeo (hand-written). This derives it.
##
## Issue #19: this is the experiment that decides whether
## relational+staging leaves experimental status.
##
## Issue #85: typeoData moved to staging/typeo_relgoal (src/ may not import
## from tests/). This file keeps the compile-time driver; it re-exports
## typeoData so fuzz_soundness.nim's `import stage_typeo` keeps working.

import staging/typeo_relgoal
export typeo_relgoal
import staging/relgoal
import staging/stagegoal
import staging/modes
import minikanren
import rel_elab   # natTy, arrTy, varTm, lamTm, appTm, zeroTm, sucTm
import tables
import sets
import strutils

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
