## Staged 4x4 Sudoku: what staging eliminates
##
## Unstaged (sudoku_seteq.nim):
## - RTerm S-exprs for cells, generic unify to bind them
## - setEqo constraint store (seq of SetEqConstraint with RTerms)
## - computeDomain walks RTerm structures to derive domains
## - branchMostConstrained builds disjunctions dynamically
## - Stream/worklist interprets the search
## - The 4x4 structure (which indices form rows/cols/boxes) is DATA
##   that the generic engine interprets at runtime
##
## Staged (this file):
## - The 4x4 structure is STATIC: row/col/box index sets are constants
## - Grid is array[16, int] (0 = empty), not RTerm list
## - No unify: direct array access and assignment
## - No constraint store: direct peer checks via hardcoded index sets
## - No Stream/worklist: direct recursion
## - Domain computed by direct array lookup, not RTerm walking
## - Fail-first: pick cell with fewest candidates (direct count)
##
## Runtime input: the givens array. Everything else is specialized.

import times
import options

# --- Static: the 4x4 structure, hardcoded at staging time ---
# These are the "relational declarations" compiled to constants.

const
  Rows: array[4, array[4, int]] = [
    [0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]
  ]
  Cols: array[4, array[4, int]] = [
    [0, 4, 8, 12], [1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15]
  ]
  Boxes: array[4, array[4, int]] = [
    [0, 1, 4, 5], [2, 3, 6, 7], [8, 9, 12, 13], [10, 11, 14, 15]
  ]

# For each cell, the peer indices (same row, col, or box, excluding self).
# Precomputed at staging time — no runtime grouping logic.
# PeerCounts tracks how many are valid (rest are uninitialized).
const
  Peers: array[16, array[8, int]] = block:
    var p: array[16, array[8, int]]
    for i in 0..<16:
      var idx = 0
      let r = i div 4
      let c = i mod 4
      let b = (r div 2) * 2 + (c div 2)
      # Row peers
      for j in Rows[r]:
        if j != i:
          p[i][idx] = j
          inc idx
      # Col peers
      for j in Cols[c]:
        if j != i:
          var already = false
          for k in 0..<idx:
            if p[i][k] == j: already = true
          if not already:
            p[i][idx] = j
            inc idx
      # Box peers
      for j in Boxes[b]:
        if j != i:
          var already = false
          for k in 0..<idx:
            if p[i][k] == j: already = true
          if not already and idx < 8:
            p[i][idx] = j
            inc idx
    p
  PeerCounts: array[16, int] = block:
    var counts: array[16, int]
    for i in 0..<16:
      var n = 0
      let r = i div 4
      let c = i mod 4
      let b = (r div 2) * 2 + (c div 2)
      var seen: set[0..15] = {}
      for j in Rows[r]:
        if j != i and j notin seen:
          seen.incl(j)
          inc n
      for j in Cols[c]:
        if j != i and j notin seen:
          seen.incl(j)
          inc n
      for j in Boxes[b]:
        if j != i and j notin seen:
          seen.incl(j)
          inc n
      counts[i] = n
    counts

proc candidates(grid: array[16, int], cell: int): seq[int] =
  ## Direct domain computation: values 1-4 not used by peers.
  ## Compare: computeDomain walks RTerm setEq constraints.
  ## Here: direct array lookup via hardcoded Peers.
  var used: set[1..4] = {}
  for k in 0..<PeerCounts[cell]:
    let peer = Peers[cell][k]
    let v = grid[peer]
    if v != 0:
      used.incl(v)
  result = @[]
  for v in 1..4:
    if v notin used:
      result.add(v)

proc solveStaged(grid: var array[16, int]): bool =
  ## Direct backtracking with fail-first.
  ## No RTerm, no unify, no Stream, no constraint store.
  ## The search structure mirrors branchMostConstrained, but
  ## everything is direct: arrays, ints, hardcoded peers.
  
  # Find most constrained empty cell (fail-first)
  var bestCell = -1
  var bestCands: seq[int] = @[]
  for i in 0..<16:
    if grid[i] == 0:
      let cands = candidates(grid, i)
      if cands.len == 0:
        return false  # empty domain → fail fast
      if bestCell == -1 or cands.len < bestCands.len:
        bestCell = i
        bestCands = cands
        if cands.len == 1:
          break  # can't get better than 1
  
  if bestCell == -1:
    return true  # all filled → solved
  
  # Branch on candidates
  for v in bestCands:
    grid[bestCell] = v
    if solveStaged(grid):
      return true
    grid[bestCell] = 0  # backtrack
  
  false

proc solveSudoku4*(givens: array[16, int]): Option[array[16, int]] =
  ## Staged entry point: givens is runtime input (0 = empty).
  ## Returns the solved grid, or none if unsolvable.
  var grid = givens
  # Validate givens don't already violate constraints
  for i in 0..<16:
    if grid[i] != 0:
      let v = grid[i]
      grid[i] = 0
      let cands = candidates(grid, i)
      if v notin cands:
        return none(array[16, int])
      grid[i] = v
  if solveStaged(grid):
    some(grid)
  else:
    none(array[16, int])

when isMainModule:
  echo "=== Staged vs Unstaged Sudoku ==="
  echo ""
  echo "Static (staging time): 4x4 structure, row/col/box groupings,"
  echo "                       peer sets, fail-first strategy."
  echo "Dynamic (runtime):     the givens array."
  echo ""
  
  var givens: array[16, int]
  givens[0] = 1
  givens[15] = 4
  
  echo "Givens: c0=1, c15=4"
  echo ""
  
  # Staged
  let start = cpuTime()
  let sol = solveSudoku4(givens)
  let elapsed = cpuTime() - start
  
  echo "Staged (direct, hardcoded structure):"
  if sol.isSome:
    let g = sol.get
    echo "  Solved in ", elapsed*1000, "ms"
    echo "  Grid:"
    for r in 0..<4:
      stdout.write("    ")
      for c in 0..<4:
        stdout.write($g[r*4 + c] & " ")
      echo ""
  else:
    echo "  No solution in ", elapsed*1000, "ms"
  echo ""
  echo "Unstaged (from previous run): 19.7ms via RTerm/setEqo/worklist"
  echo ""
  echo "What staging eliminated:"
  echo "  - RTerm S-expr construction for 16 cells"
  echo "  - Generic unify for each binding (direct array assignment)"
  echo "  - setEqo constraint store (16 RTerm lists → hardcoded int arrays)"
  echo "  - computeDomain walking RTerms (direct peer array lookup)"
  echo "  - Stream/worklist search interpretation (direct recursion)"
  echo "  - branchMostConstrained dynamic disjunction building"
