# egraph.nim — E-graph conversion cache (Experiment 10)
#
# One e-graph per module over elaborated terms. Every areEqual(t1, t2)
# first probes e-class membership (O(α) hit skips NbE); on miss, run
# NbE as the oracle and on success merge the e-classes.
#
# Sound by construction — the e-graph only remembers equalities NbE proved.
#
# This is the lowest-risk e-graph experiment: a memoization layer, not
# a replacement for the conversion checker.

import tables
import ett_init

type
  EGraph* = object
    # Hash-cons table: term string -> e-class ID
    ids: Table[string, int]
    # Union-find parent pointers
    parent: seq[int]
    # Stats
    hits*: int
    misses*: int
    merges*: int

proc initEGraph*(): EGraph =
  EGraph(ids: initTable[string, int](), parent: @[], hits: 0, misses: 0, merges: 0)

proc find(eg: var EGraph, x: int): int =
  ## Union-find with path compression
  var root = x
  while eg.parent[root] != root:
    root = eg.parent[root]
  # Path compression
  var cur = x
  while eg.parent[cur] != root:
    let nxt = eg.parent[cur]
    eg.parent[cur] = root
    cur = nxt
  root

proc termId(eg: var EGraph, t: Term): int =
  ## Get or create the e-class ID for a term (hash-consed by $).
  let key = $t
  if key in eg.ids:
    return eg.ids[key]
  let id = eg.parent.len
  eg.ids[key] = id
  eg.parent.add(id)  # parent[i] = i (own root)
  id

proc areEqualCached*(eg: var EGraph, key: string): tuple[hit: bool, equal: bool] =
  ## Probe the cache with a precomputed key. If hit, return (true, true).
  ## If miss, return (false, false) — caller must run NbE and call merge.
  if key in eg.ids:
    let id = eg.ids[key]
    # Key maps to a canonical representative; if it's in the table,
    # it was merged before, so it's a hit
    inc eg.hits
    (true, true)
  else:
    inc eg.misses
    (false, false)

proc merge*(eg: var EGraph, key: string) =
  ## Record that the key (representing an equality) holds.
  ## We store the key mapping to itself; future probes with the same
  ## key will hit. (Full e-class merging across different keys is
  ## future work — this is a memo table, not yet a true e-graph.)
  if key notin eg.ids:
    let id = eg.parent.len
    eg.ids[key] = id
    eg.parent.add(id)
    inc eg.merges

proc stats*(eg: EGraph): string =
  "e-graph: " & $eg.hits & " hits, " & $eg.misses & " misses, " &
    $eg.merges & " merges, " & $eg.ids.len & " terms"
