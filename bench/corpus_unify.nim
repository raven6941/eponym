## Issue #63: corpus of real elaboration-time unification problems.
##
## Elaborates every .ep example (same loop as tests/run_examples.nim) with
## -d:unifyCorpusLog, recording each unifyElab problem's raw and zonked
## kind-skeleton pair, outcome, and store size. Writes bench/unify_corpus.txt.
##
## Compile:  nim c -r -d:unifyCorpusLog --path:src --path:src/eponym \
##               --path:src/relational --path:src/staging bench/corpus_unify.nim
## Without the flag the log stays empty and the driver reports that.

import os
import strutils
import tables
import algorithm
import elab
import unify

var failed = 0
var elaborated = 0

for dir in ["examples", "examples/ep"]:
  for kind, path in walkDir(dir):
    if kind == pcFile and path.endsWith(".ep"):
      let prog = readFile(path)
      var lines: seq[string] = @[]
      for line in prog.splitLines():
        if not line.strip().startsWith("#"):
          lines.add(line)
      let src = lines.join("\n")
      let neg = path.endsWith("-neg.ep")
      try:
        discard elabCheck(src)
        inc elaborated
        if neg:
          echo "FAIL (should have been rejected): ", path
          inc failed
      except ElabError:
        if not neg:
          echo "FAIL (rejected): ", path
          inc failed

echo "elaborated: ", elaborated, ", failed: ", failed
echo "corpus entries: ", corpusLog.len

when not defined(unifyCorpusLog):
  echo "NOTE: compiled without -d:unifyCorpusLog, corpus is empty"

writeFile("bench/unify_corpus.txt", corpusLog.join("\n") & "\n")

# Distribution summary: outcome x head-kind pair (zonked), plus full shapes.
var dist = initTable[string, int]()
var fullDist = initTable[string, int]()
var stores: seq[int] = @[]
var rawMoved = 0  # problems where zonking changed a side's shape
for e in corpusLog:
  let parts = e.split("  ")
  # parts: [raw-a =?= raw-b, "=> ", zonk-a =?= zonk-b, "[ok|fail] store=N"]
  if parts.len < 4: continue
  let outcome = if "[ok]" in parts[3]: "ok" else: "fail"
  let zp = parts[2].split(" =?= ")
  if zp.len < 2: continue
  let za = zp[0]; let zb = zp[1]
  dist.mgetOrPut(outcome & "  " & $za[0] & " =?= " & $zb[0], 0) += 1
  fullDist.mgetOrPut(outcome & "  " & za & " =?= " & zb, 0) += 1
  let sp = parts[3].split("store=")
  if sp.len == 2: stores.add(parseInt(sp[1]))
  if parts[0] != parts[2]: inc rawMoved

echo "problems where zonk changed a shape: ", rawMoved, " / ", corpusLog.len
if stores.len > 0:
  stores.sort()
  echo "store size (metas created): min=", stores[0], " max=", stores[^1],
       " median=", stores[stores.len div 2]
echo "--- top zonked head-kind pairs (outcome) ---"
var rows: seq[(string, int)] = @[]
for k, v in dist: rows.add((k, v))
rows.sort(proc(x, y: (string, int)): int = cmp(y[1], x[1]))
for i in 0 ..< min(15, rows.len):
  echo rows[i][1], "x  ", rows[i][0]
echo "--- top full zonked shape pairs ---"
rows.setLen(0)
for k, v in fullDist: rows.add((k, v))
rows.sort(proc(x, y: (string, int)): int = cmp(y[1], x[1]))
for i in 0 ..< min(15, rows.len):
  echo rows[i][1], "x  ", rows[i][0]

if failed > 0: quit(1)
