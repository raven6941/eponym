## Issue #55: per-phase elaboration wall-clock breakdown.
##
## Measures exclusive per-phase time (parse, checkTm, inferTm, unifyElab,
## zonk, convElab, driver-other) over the two bench_conv_cache corpora —
## the same corpora #47 used, where conversion was found to be ~6% of
## elaboration time and the other ~94% unprofiled.
##
## Build (profiling ON):
##   nim c -r -d:elabProfile --hints:off \
##     --path:src --path:src/eponym --path:src/relational --path:src/staging \
##     --path:bench bench/bench_elab_profile.nim
## Without -d:elabProfile the phase report prints "profiling disabled"
## (instrumentation compiles away; see src/eponym/elab_prof.nim).

import elab
import elab_prof
import bench_conv_cache  # buildRepeated / buildDistinct corpus builders
import std/times

proc runCorpus(name: string, corpus: string) =
  echo "=== " & name & " (" & $corpus.len & " chars) ==="
  resetPhases()
  let t0 = cpuTime()
  let defs = elabCheck(corpus)
  let wall = cpuTime() - t0
  echo "  decls: " & $defs.len & "  wall: " & $wall & "s"
  echo reportPhases()
  echo ""

proc runExamples() =
  ## Realistic corpus: the positive .ep examples, each with a fresh
  ## driver (as tests/run_examples.nim does). Small but representative
  ## of real programs (not numeral-heavy like the bench corpora).
  echo "=== examples/ep positive corpus ==="
  resetPhases()
  let t0 = cpuTime()
  var n = 0
  for f in ["01-twice-const.ep", "02-myid.ep", "03-let.ep",
            "04-polyid-implicit.ep", "05-id-universe.ep", "06-const-lam.ep",
            "07-bool-postulate.ep", "08-nat-postulate.ep", "09-data-nat.ep",
            "10-data-vec.ep", "11-vec-append-conv.ep", "12-eq-plusReducesZ.ep",
            "13-primint.ep", "14-tactics.ep", "15-session-types.ep",
            "21-borrow-ok.ep", "22-import-lib.ep", "23-import-client.ep",
            "25-clause-catchall.ep", "25b-clause-nested.ep",
            "25e-clause-multicol.ep"]:
    discard elabCheckFile("examples/ep/" & f)
    inc n
  let wall = cpuTime() - t0
  echo "  files: " & $n & "  wall: " & $wall & "s"
  echo reportPhases()
  echo ""

when isMainModule:
  const Reps = 15  # same as bench_conv_cache's main
  runCorpus("repeated-goals", buildRepeated(Reps))
  runCorpus("distinct-goals", buildDistinct(Reps))
  runExamples()
