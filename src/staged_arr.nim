## Staged function synthesis — composes Nat synthesizer (issue #14)
##
## Pattern: typeo(q, arrTy(natTy(), natTy()), rnil())
##   - Synthesize functions from Nat to Nat.
##
## Branch analysis (ty=arr(nat,nat) static, ctx=nil static):
## - zero: produces nat, not arr → prune
## - suc: produces nat, not arr → prune
## - var: ctx=nil → prune
## - lam: q=lam(b), b:nat in (nat.nil) → KEEP (only viable branch)
## - app: could produce arr, but complex → prune (conservative)
##
## Staged:
##   synthArr(q) = fresh(b => conj(q=lam(b), synthNatVar(b)))
## where synthNatVar is the staged Nat-with-var synthesizer.
##
## This demonstrates COMPOSITION of staged relations!

import macros
import minikanren
import rel_elab
import staged_var  # for the generated proc? Actually need the macro

# For now, hand-write the composition to prove the concept.
# The macro can generate this pattern later.

proc synthArr*(q: RTerm): Goal =
  ## Staged: synthesize functions q : arr(nat, nat) in empty context.
  ## Only the lam branch is viable; body uses Nat-with-var synthesizer.
  fresh(proc(b: RTerm): Goal =
    conj(`==`(q, lamTm(b)),
      # b : nat in (nat . nil) — use staged with-var
      # We need a Goal for this; for now, inline the logic
      # Actually, we can call the stagedWithVar macro here!
      stagedWithVar(b))
  )

when isMainModule:
  import times
  echo "=== Staged function synthesis ==="
  let q = freshVar()
  let start = cpuTime()
  let r = run(q, synthArr(q), 3)
  let time = cpuTime() - start
  echo "Results: ", r.len, " in ", time*1000, "ms"
  for t in r: echo "  ", t
  echo ""
  echo "Expected: lam(zero), lam(suc(zero)), lam(var(0)), ..."
