## Relational 4x4 Sudoku solver
##
## A meaningful relational program with runtime input:
## - Static (staging time): the Sudoku rules — 4x4 structure, row/col/box
##   constraints, the permutation-based all-different encoding
## - Dynamic (runtime): the puzzle grid with givens
##
## This connects Priority 1 (fair search) and Priority 2 (staging):
## the fair search makes the relational solver work, and staging
## will eliminate the miniKanren interpretive overhead.

import minikanren
import times

proc rcons(h, t: RTerm): RTerm = rpair(h, t)

# --- Basic list relations ---

proc appendo(a, b, c: RTerm): Goal =
  ## c is a ++ b
  disj(
    conj(`==`(a, rnil()), `==`(c, b)),
    fresh3(proc(x, xs, cs: RTerm): Goal =
      conj(`==`(a, rcons(x, xs)),
        conj(`==`(c, rcons(x, cs)),
          appendo(xs, b, cs)))))

proc permo(l, p: RTerm): Goal =
  ## p is a permutation of l
  let base = conj(`==`(l, rnil()), `==`(p, rnil()))
  let step = fresh(proc(x: RTerm): Goal =
    fresh(proc(xs: RTerm): Goal =
      fresh(proc(ys1: RTerm): Goal =
        fresh(proc(ys2: RTerm): Goal =
          fresh(proc(rest: RTerm): Goal =
            conj(`==`(l, rcons(x, xs)),
              conj(appendo(ys1, rcons(x, ys2), p),
                conj(appendo(ys1, ys2, rest),
                  permo(xs, rest)))))))))
  disj(base, step)

# --- 4x4 Sudoku ---
# Cells: c0..c15 in row-major order
#   c0  c1  c2  c3
#   c4  c5  c6  c7
#   c8  c9  c10 c11
#   c12 c13 c14 c15
# Digits: 1, 2, 3, 4
# Boxes are 2x2: [c0,c1,c4,c5], [c2,c3,c6,c7], [c8,c9,c12,c13], [c10,c11,c14,c15]

proc digits1234(): RTerm =
  rlist(@[rint(1), rint(2), rint(3), rint(4)])

proc sudoku4(cells: RTerm, givens: seq[(int, int)]): Goal =
  ## cells is a list of 16 logic vars (or ground values for givens).
  ## givens: seq of (index, value) for pre-filled cells.
  ## Each row, column, and 2x2 box must be a permutation of [1,2,3,4].
  
  # Extract cells c0..c15 via fresh variables and unify with the list
  fresh4(proc(c0, c1, c2, c3: RTerm): Goal =
    fresh4(proc(c4, c5, c6, c7: RTerm): Goal =
      fresh4(proc(c8, c9, c10, c11: RTerm): Goal =
        fresh4(proc(c12, c13, c14, c15: RTerm): Goal =
          let allCells = @[c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15]
          
          # Unify cells list with the 16 vars
          var g: Goal = `==`(cells, rlist(allCells))
          
          # Apply givens: unify specific cells with values
          for (idx, val) in givens:
            let cellVar = allCells[idx]
            g = conj(g, `==`(cellVar, rint(val)))
          
          # Row constraints: each row is a permutation of [1,2,3,4]
          let d = digits1234()
          g = conj(g, permo(rlist(@[c0,c1,c2,c3]), d))
          g = conj(g, permo(rlist(@[c4,c5,c6,c7]), d))
          g = conj(g, permo(rlist(@[c8,c9,c10,c11]), d))
          g = conj(g, permo(rlist(@[c12,c13,c14,c15]), d))
          
          # Column constraints
          g = conj(g, permo(rlist(@[c0,c4,c8,c12]), d))
          g = conj(g, permo(rlist(@[c1,c5,c9,c13]), d))
          g = conj(g, permo(rlist(@[c2,c6,c10,c14]), d))
          g = conj(g, permo(rlist(@[c3,c7,c11,c15]), d))
          
          # Box constraints (2x2)
          g = conj(g, permo(rlist(@[c0,c1,c4,c5]), d))
          g = conj(g, permo(rlist(@[c2,c3,c6,c7]), d))
          g = conj(g, permo(rlist(@[c8,c9,c12,c13]), d))
          g = conj(g, permo(rlist(@[c10,c11,c14,c15]), d))
          
          g
        ))))

when isMainModule:
  echo "=== Relational 4x4 Sudoku ==="
  echo ""
  echo "Puzzle (0 = empty):"
  echo "  1 . | . ."
  echo "  . . | . ."
  echo "  ----+----"
  echo "  . . | . ."
  echo "  . . | . 2"
  echo ""
  
  # Givens: c0=1, c15=2
  let givens = @[(0, 1), (15, 2)]
  
  let q = freshVar()
  let start = cpuTime()
  let solutions = run(q, sudoku4(q, givens), 1)
  let elapsed = cpuTime() - start
  
  echo "Solutions found: ", solutions.len, " in ", elapsed*1000, "ms"
  if solutions.len > 0:
    echo "First solution: ", solutions[0]
