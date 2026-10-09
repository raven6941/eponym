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
import hashes
import ett_init

type
  ConvKey* = tuple[ctxLen: int, ha: Hash, hb: Hash]
    ## Experiment 47: conversion-cache memo key as O(1) ints —
    ## (ctxLen, hashTerm(a), hashTerm(b)) — instead of the rendered
    ## `$ctxLen & ":" & $a & " === " & $b` string, whose rendering on
    ## every goal cost nearly as much as the NbE it skipped (#41).
    ## 64-bit structural hashes: at the goal counts we see (~10^4 keys)
    ## the collision probability is ~10^-11; the table still only ever
    ## stores goals NbE proved, and the choice is recorded in
    ## decisions.org.

  EGraph* = object
    # Hash-cons table: conversion key -> e-class ID
    ids: Table[ConvKey, int]
    # Union-find parent pointers
    parent: seq[int]
    # Stats
    hits*: int
    misses*: int
    merges*: int

proc initEGraph*(): EGraph =
  EGraph(ids: initTable[ConvKey, int](), parent: @[], hits: 0, misses: 0, merges: 0)

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

proc convKey*(ctxLen: int, a, b: Term): ConvKey =
  ## Experiment 47: build the O(1)-int memo key for a conversion goal.
  (ctxLen, hashTerm(a), hashTerm(b))

proc areEqualCached*(eg: var EGraph, key: ConvKey): tuple[hit: bool, equal: bool] =
  ## Probe the cache with a precomputed key. If hit, return (true, true).
  ## If miss, return (false, false) — caller must run NbE and call merge.
  if key in eg.ids:
    inc eg.hits
    (true, true)
  else:
    inc eg.misses
    (false, false)

proc merge*(eg: var EGraph, key: ConvKey) =
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
    $eg.merges & " merges, " & $eg.ids.len & " keys"
