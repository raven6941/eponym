## 4x4 Sudoku with setEqo global constraints
##
## Each row, column, and 2x2 box: set(cells) == set([1,2,3,4]).
## The setEqo constraint propagates:
## - When a cell binds, the value is removed from the remaining set
## - Naked single: if 3 of 4 bind, the 4th is determined
##
## This is the user's proposal: capture the constraint as set equality,
## not pairwise disequalities. Much stronger propagation.

import minikanren
import times

proc in1234(x: RTerm): Goal =
  disj(
    `==`(x, rint(1)),
    disj(`==`(x, rint(2)),
      disj(`==`(x, rint(3)),
        `==`(x, rint(4)))))

proc sudoku4set(q: RTerm, givens: seq[(int, int)]): Goal =
  fresh4(proc(c0, c1, c2, c3: RTerm): Goal =
    fresh4(proc(c4, c5, c6, c7: RTerm): Goal =
      fresh4(proc(c8, c9, c10, c11: RTerm): Goal =
        fresh4(proc(c12, c13, c14, c15: RTerm): Goal =
          let cells = @[c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15]
          let digits = @[rint(1), rint(2), rint(3), rint(4)]
          
          # Post all setEq constraints FIRST (no enumeration yet).
          # The domains are implied by these constraints.
          var g: Goal = proc(s: State): Stream = singleton(s)
          
          # Givens (bind specific cells)
          for (idx, val) in givens:
            let prev = g
            let cell = cells[idx]
            g = conj(prev, `==`(cell, rint(val)))
          
          # Rows: set equality
          g = conj(g, setEqo(@[c0,c1,c2,c3], digits))
          g = conj(g, setEqo(@[c4,c5,c6,c7], digits))
          g = conj(g, setEqo(@[c8,c9,c10,c11], digits))
          g = conj(g, setEqo(@[c12,c13,c14,c15], digits))
          
          # Columns: set equality
          g = conj(g, setEqo(@[c0,c4,c8,c12], digits))
          g = conj(g, setEqo(@[c1,c5,c9,c13], digits))
          g = conj(g, setEqo(@[c2,c6,c10,c14], digits))
          g = conj(g, setEqo(@[c3,c7,c11,c15], digits))
          
          # Boxes: set equality
          g = conj(g, setEqo(@[c0,c1,c4,c5], digits))
          g = conj(g, setEqo(@[c2,c3,c6,c7], digits))
          g = conj(g, setEqo(@[c8,c9,c12,c13], digits))
          g = conj(g, setEqo(@[c10,c11,c14,c15], digits))
          
          # THEN branch with fail-first: pick most constrained var,
          # compute its domain from constraints, branch on it.
          # No static in1234 disjunctions needed — domains are dynamic.
          g = conj(g, branchMostConstrained(cells))
          
          conj(g, `==`(q, rlist(cells)))
        ))))

when isMainModule:
  echo "=== 4x4 Sudoku with setEqo ==="
  echo ""
  let givens = @[(0, 1), (15, 4)]
  echo "Givens: c0=1, c15=4"
  echo ""
  
  let q = freshVar()
  let start = cpuTime()
  let solutions = run(q, sudoku4set(q, givens), 1)
  let elapsed = cpuTime() - start
  
  echo "Solutions: ", solutions.len, " in ", elapsed*1000, "ms"
  for s in solutions:
    echo "  ", s
