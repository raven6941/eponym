## Staged synthNat — manual staging prototype (issue #14)
##
## Hand-staged version of `typeo(q, natTy(), rnil())`.
## 
## Staging decisions (done manually, at "compile time"):
## - ty = nat is STATIC: prune branches that produce non-nat types
##   - var branch: pruned (requires ctx=(ty0 . _), but ctx=nil)
##   - lam branch: pruned (produces arr type, not nat)
##   - app branch: pruned (could produce nat, but complex; skip for now)
## - ctx = nil is STATIC: no need to thread it through
## - tm = q is DYNAMIC: the only logic variable
##
## Remaining branches:
## - zero: q = zero
## - suc: q = suc(n), synthNat(n) [recursive, specialized]
##
## This avoids:
## - 3 pruned branches (var, lam, app) and their fresh vars
## - ty/ctx unifications (known statically)
## - Generic disj over 5 branches (now 2)

import minikanren
import rel_elab  # for zeroTm, sucTm

proc synthNat*(q: RTerm): Goal =
  ## Staged: synthesize terms q of type nat in empty context.
  ## Equivalent to typeo(q, natTy(), rnil()), but specialized.
  disj(
    # zero: q = zero (ty=nat is static, no need to unify)
    `==`(q, zeroTm()),
    # suc: q = suc(n), n : nat (recursive, specialized)
    fresh(proc(n: RTerm): Goal =
      conj(`==`(q, sucTm(n)),
        synthNat(n)))
  )

when isMainModule:
  import times
  
  echo "=== Staged synthNat vs Interpretive typeo ==="
  echo ""
  
  # Interpretive: typeo(q, nat, nil)
  echo "Interpretive (typeo):"
  let start1 = cpuTime()
  let q1 = freshVar()
  let r1 = run(q1, typeo(q1, natTy(), rnil()), 5)
  let time1 = cpuTime() - start1
  echo "  Results: ", r1.len
  for t in r1: echo "    ", t
  echo "  Time: ", time1 * 1000, "ms"
  echo ""
  
  # Staged: synthNat(q)
  echo "Staged (synthNat):"
  let start2 = cpuTime()
  let q2 = freshVar()
  let r2 = run(q2, synthNat(q2), 5)
  let time2 = cpuTime() - start2
  echo "  Results: ", r2.len
  for t in r2: echo "    ", t
  echo "  Time: ", time2 * 1000, "ms"
  echo ""
  
  if time1 > 0 and time2 > 0:
    echo "Speedup: ", time1 / time2, "x"
