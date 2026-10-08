## Relational 4x4 Sudoku with constraint propagation
##
## Unlike the permo-based version (generate-and-test), this uses =/=
## disequality constraints for all-different. The constraint store
## propagates: when == binds a cell, checkDiseqs immediately fails
## branches that violate a disequality. This is forward checking
## captured in the relational declarations themselves.

import minikanren
import times

proc rcons(h, t: RTerm): RTerm = rpair(h, t)

# --- Domain: each cell is 1, 2, 3, or 4 ---

proc in1234(x: RTerm): Goal =
  disj(
    `==`(x, rint(1)),
    disj(`==`(x, rint(2)),
      disj(`==`(x, rint(3)),
        `==`(x, rint(4)))))

# --- All-different via pairwise disequality ---
# allDiff([a,b,c,d]) = a=/=b, a=/=c, a=/=d, b=/=c, b=/=d, c=/=d
# When any cell is bound, the disequalities propagate to peers.

proc allDiff(cells: seq[RTerm]): Goal =
  var g: Goal = proc(s: State): Stream = singleton(s)  # succeed
  for i in 0..<cells.len:
    for j in (i+1)..<cells.len:
      let a = cells[i]
      let b = cells[j]
      let prev = g
      g = conj(prev, `=/=`(a, b))
  g

proc sudoku4cp(q: RTerm, givens: seq[(int, int)]): Goal =
  ## 4x4 Sudoku with constraint propagation.
  ## q: output var, will be bound to the solution list.
  ## givens: (index, value) for pre-filled cells, index 0..15 row-major.
  
  fresh4(proc(c0, c1, c2, c3: RTerm): Goal =
    fresh4(proc(c4, c5, c6, c7: RTerm): Goal =
      fresh4(proc(c8, c9, c10, c11: RTerm): Goal =
        fresh4(proc(c12, c13, c14, c15: RTerm): Goal =
          let cells = @[c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15]
          
          # Each cell in {1,2,3,4}
          var g: Goal = proc(s: State): Stream = singleton(s)
          for c in cells:
            let prev = g
            g = conj(prev, in1234(c))
          
          # Givens
          for (idx, val) in givens:
            let prev = g
            let cell = cells[idx]
            let v = val
            g = conj(prev, `==`(cell, rint(v)))
          
          # Rows: all-different
          g = conj(g, allDiff(@[c0,c1,c2,c3]))
          g = conj(g, allDiff(@[c4,c5,c6,c7]))
          g = conj(g, allDiff(@[c8,c9,c10,c11]))
          g = conj(g, allDiff(@[c12,c13,c14,c15]))
          
          # Columns: all-different
          g = conj(g, allDiff(@[c0,c4,c8,c12]))
          g = conj(g, allDiff(@[c1,c5,c9,c13]))
          g = conj(g, allDiff(@[c2,c6,c10,c14]))
          g = conj(g, allDiff(@[c3,c7,c11,c15]))
          
          # Boxes (2x2): all-different
          g = conj(g, allDiff(@[c0,c1,c4,c5]))
          g = conj(g, allDiff(@[c2,c3,c6,c7]))
          g = conj(g, allDiff(@[c8,c9,c12,c13]))
          g = conj(g, allDiff(@[c10,c11,c14,c15]))
          
          # Return the solution as a list
          conj(g, `==`(q, rlist(cells)))
        ))))

when isMainModule:
  echo "=== 4x4 Sudoku with constraint propagation ==="
  echo ""
  
  # Simple puzzle: just two givens
  let givens = @[(0, 1), (15, 4)]
  echo "Givens: c0=1, c15=4"
  echo ""
  
  let q = freshVar()
  let start = cpuTime()
  let solutions = run(q, sudoku4cp(q, givens), 1)
  let elapsed = cpuTime() - start
  
  echo "Solutions: ", solutions.len, " in ", elapsed*1000, "ms"
  for s in solutions:
    echo "  ", s
