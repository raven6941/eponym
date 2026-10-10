## Issue #63: staged unifier end-to-end (L1 of the tower).
##
## Elaborates every examples/*.ep program ONCE with the `unify` selected
## at compile time (general, or staged with -d:stagedUnify). Prints one
## outcome line per program (for diffing across modes), then cumulative
## unify time (-d:unifyTime) and suite wall time.
##
## Run twice and compare:
##   nim c -r -d:release -d:unifyTime --path:src --path:src/eponym \
##       --path:src/relational --path:src/staging bench/bench_staged_unify_e2e.nim > /tmp/e2e_base.txt
##   nim c -r -d:release -d:unifyTime -d:stagedUnify --path:src --path:src/eponym \
##       --path:src/relational --path:src/staging bench/bench_staged_unify_e2e.nim > /tmp/e2e_staged.txt
##   diff <(grep '^prog ' /tmp/e2e_base.txt) <(grep '^prog ' /tmp/e2e_staged.txt) && echo "OUTCOMES IDENTICAL"

import os
import strutils
import sequtils
import times
import algorithm
import elab
import unify
import ett_init  # `$` for Term

when not defined(unifyTime):
  {.error: "compile with -d:unifyTime".}

unifyNanos = 0
var paths: seq[string] = @[]
for dir in ["examples", "examples/ep"]:
  for kind, path in walkDir(dir):
    if kind == pcFile and path.endsWith(".ep"): paths.add(path)
paths.sort()

var nOk, nFail = 0
let t0 = cpuTime()
for path in paths:
  let prog = readFile(path)
  var lines: seq[string] = @[]
  for line in prog.splitLines():
    if not line.strip().startsWith("#"): lines.add(line)
  let src = lines.join("\n")
  let neg = path.endsWith("-neg.ep")
  try:
    let defs = elabCheck(src)
    inc nOk
    if neg:
      echo "prog ", path, " UNEXPECTED-OK"
    else:
      echo "prog ", path, " ok ",
        defs.mapIt(it.name & ":" & $it.tyTm & "=" & $it.tmTm).join(";")
  except CatchableError as e:
    inc nFail
    if neg: echo "prog ", path, " ok-neg"
    else: echo "prog ", path, " FAIL ", e.msg
let wall = cpuTime() - t0

when defined(stagedUnify):
  echo "mode staged"
else:
  echo "mode general"
echo "programs ok=", nOk, " fail=", nFail
echo "cumulative unify: ", (unifyNanos.float / 1000.0).formatFloat(ffDecimal, 0), "us"
echo "suite wall: ", wall.formatFloat(ffDecimal, 2), "s"
