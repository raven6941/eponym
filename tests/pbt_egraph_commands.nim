## tests/pbt_egraph_commands.nim — Model-based tests for the e-graph
## conversion cache (Experiment 10, src/eponym/egraph.nim).
##
## The single-op properties in pbt_egraph.nim can't see
## sequence-dependent bugs (a merge evicting the wrong entry, counters
## drifting over mixed workloads). Here random command sequences run
## against both the real cache and a simple Table model, failing on
## divergence — falsify's runCommands shrinks the failing sequence.
##
## Run: nim c -r --hints:off --path:src --path:src/eponym tests/pbt_egraph_commands.nim
## Fixed seed 424242 in CI (change Seed locally for fresh fuzzing).

import falsify
import egraph
import hashes
import tables

const Seed = 424242'u64

type
  EGraphCmdKind = enum ckMerge, ckProbe
  EGraphCmd = object
    kind: EGraphCmdKind
    key: ConvKey

  EGraphModel = object
    keys: Table[ConvKey, bool]
    hits, misses, merges: int

proc genKey(r: var Rng): ConvKey =
  ## Same key distribution as pbt_egraph.nim's genKey.
  (r.below(4), Hash(cast[int64](r.next() shr 1)),
   Hash(cast[int64](r.next() shr 1)))

proc genCmd(r: var Rng, m: EGraphModel): EGraphCmd =
  ## Every command is valid in every model state (no preconditions
  ## needed): merges are idempotent, probes never fail.
  let kind = if r.genBool(): ckMerge else: ckProbe
  EGraphCmd(kind: kind, key: genKey(r))

proc newModel(): EGraphModel =
  EGraphModel(keys: initTable[ConvKey, bool]())

proc runCmd(sys: var EGraph, m: var EGraphModel, c: EGraphCmd): bool =
  ## Apply one command to both system and model; false on divergence.
  case c.kind
  of ckMerge:
    if c.key notin m.keys:
      m.keys[c.key] = true
      inc m.merges
    merge(sys, c.key)
  of ckProbe:
    let (hit, eq) = areEqualCached(sys, c.key)
    let expHit = c.key in m.keys
    if expHit: inc m.hits else: inc m.misses
    if hit != expHit: return false
    if hit and not eq: return false
  # Cross-check the publicly observable counters after every command.
  # (ids/parent are private; `merges` already counts distinct keys.)
  sys.hits == m.hits and sys.misses == m.misses and
    sys.merges == m.merges

var r = initRng(Seed)
let ok = runCommands("egraph-command-sequences", r, 200, 15,
  genCmd, newModel, initEGraph, runCmd)
if not ok:
  echo "--- egraph command-sequence model test FAILED (seed ", Seed, ") ---"
  quit(1)
echo "--- egraph command-sequence model test passed ---"
