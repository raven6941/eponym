## Issue #63: how much elaboration time lives in L2 (insertImplicits)?
##
## Elaborates every examples/*.ep program with -d:insertTime and reports
## cumulative insertImplicits time + call count vs suite wall time.
## Decides whether staging L2's loop is worth attempting at all.
##
## Compile:  nim c -r -d:release -d:insertTime --path:src --path:src/eponym \
##               --path:src/relational --path:src/staging bench/bench_insert_time.nim

import os
import strutils
import times
import algorithm
import elab

when not defined(insertTime):
  {.error: "compile with -d:insertTime".}

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
  try:
    discard elabCheck(lines.join("\n"))
    inc nOk
  except CatchableError:
    inc nFail
let wall = cpuTime() - t0

echo "programs: ok=", nOk, " fail=", nFail
echo "insertImplicits calls: ", insertCalls
echo "loop iterations (implicit args inserted): ", insertIters
echo "cumulative insertImplicits time (incl ~2us/call instrumentation): ",
     (insertNanos.float / 1000.0).formatFloat(ffDecimal, 0), "us"
echo "suite wall: ", wall.formatFloat(ffDecimal, 2), "s"
echo "reported share of wall: ",
     (insertNanos.float / 1e9 / wall * 100).formatFloat(ffDecimal, 1), "%"
echo "mean per call: ",
     (if insertCalls > 0: insertNanos.float / insertCalls.float else: 0.0).formatFloat(ffDecimal, 0), "ns"
