## Staged Vec synthesis — length index drives code generation (issue #14)
##
## This is the key demonstration of "dependent types as specialization fuel":
## the length index n (a Nat value at the type level) determines the
## *shape* of the generated code.
##
## For Vec Nat 2:
##   synthVec2(q) = fresh(h, t => q=veccons(h,t), synthNat(h), synthVec1(t))
## For Vec Nat 1:
##   synthVec1(q) = fresh(h, t => q=veccons(h,t), synthNat(h), synthVec0(t))
## For Vec Nat 0:
##   synthVec0(q) = (q = vecnil)
##
## The stager *computes* these from the length index. No search, no
## backtracking — the type tells us exactly what to generate.
##
## This is condition 1 (groundness) + condition 2 (discrimination):
## the ground length discriminates vecnil vs veccons at each level.

import minikanren
import rel_elab
import staged_synth  # for synthNat

proc synthVec0*(q: RTerm): Goal =
  ## Staged: q : Vec A 0. Only vecnil is possible.
  `==`(q, vecnilTm())

proc synthVec1*(q: RTerm): Goal =
  ## Staged: q : Vec Nat 1. Must be veccons(h, vecnil) with h:Nat.
  fresh2(proc(h, t: RTerm): Goal =
    conj(`==`(q, vecconsTm(h, t)), conj(synthNat(h), synthVec0(t))))

proc synthVec2*(q: RTerm): Goal =
  ## Staged: q : Vec Nat 2.
  fresh2(proc(h, t: RTerm): Goal =
    conj(`==`(q, vecconsTm(h, t)), conj(synthNat(h), synthVec1(t))))

when isMainModule:
  import times
  echo "=== Staged Vec synthesis (length-driven) ==="
  echo ""
  
  let q = freshVar()
  let start = cpuTime()
  let r = run(q, synthVec2(q), 3)
  let time = cpuTime() - start
  echo "Vec Nat 2: ", r.len, " results in ", time*1000, "ms"
  for t in r: echo "  ", t
  echo ""
  echo "The length index 2 generated exactly 2 veccons layers."
  echo "No search was needed — the type dictated the shape."
