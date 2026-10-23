## Shared harness for the #432 runtime benchmark suite.
##
## Dev-only measurement instrument (NOT a CI gate — see the constraint in
## issue #432): times representative eponym programs across the available
## execution paths and prints per-path wall-clock tables with speedup
## ratios, so a regression in generated-code quality shows up as a number.
##
## Fairness discipline (AGENTS.md benchmarking):
## - Args are built ONCE, outside the timed loop, for every path.
## - Elaboration is warmed (defCache) before timing; the timed interpreter
##   section measures findDef + the ETT interpreter + result decode only.
## - Each driver names what its paths actually do in its header note.
## - A surprising result gets profiled before it gets recorded as a
##   verdict — this harness reports numbers, never verdicts.
## - An accumulator threaded through the timed body keeps the compiler
##   from eliminating the work being measured.

import std/[times, strutils]

const TargetSecs* = 1.5
  ## Per-path target wall-clock; iteration counts are calibrated to land near it.

proc timeIters*(body: proc(acc: var int), iters: int): float =
  ## Run `body` `iters` times (after warmup) and return ms per iteration.
  ## `body` must perturb `acc` so the timed work is not eliminated.
  var acc = 0
  let warm = max(5, iters div 10)
  for _ in 0 ..< warm:
    body(acc)
  let t0 = cpuTime()
  for _ in 0 ..< iters:
    body(acc)
  let dt = cpuTime() - t0
  if acc == low(int):
    # Keep acc observably live without touching the timed section.
    echo ""
  dt / float(iters) * 1000.0

proc calibrateIters*(body: proc(acc: var int),
                     targetSecs = TargetSecs): int =
  ## Pick an iteration count that lands near `targetSecs` of timed work,
  ## from a short pilot run.
  const pilot = 10
  let ms = timeIters(body, pilot)
  if ms <= 0.0:
    return 100_000
  clamp(int(targetSecs * 1000.0 / ms), 10, 200_000)

type
  PathTime* = tuple[name: string, msPerIter: float, iters: int]

proc printProgramHeader*(program, note: string) =
  echo ""
  echo "== ", program, " =="
  for line in note.splitLines():
    echo "   ", line

proc printPathRow*(p: PathTime) =
  echo "   ", p.name.alignLeft(30),
    p.msPerIter.formatFloat(ffDecimal, 4), " ms/iter",
    "  (", p.iters, " iters)"

proc findPath(paths: openArray[PathTime], name: string): PathTime =
  for p in paths:
    if p.name == name:
      return p
  raise newException(ValueError, "unknown path: " & name)

proc printComparisons*(paths: seq[PathTime]) =
  ## Print speedup ratios in #19's framing: each compiled tier against the
  ## one below it, plus the end-to-end compiled-vs-interpreter number.
  ## Ratios only — the table above carries the absolute ms/iter.
  let has = proc(name: string): bool =
    for p in paths:
      if p.name == name:
        return true
    false
  if has("value") and has("interpreter"):
    let v = findPath(paths, "value").msPerIter
    let i = findPath(paths, "interpreter").msPerIter
    if v > 0.0:
      echo "   value vs interpreter: ", (i / v).formatFloat(ffDecimal, 1), "x"
  if has("repr") and has("value"):
    let r = findPath(paths, "repr").msPerIter
    let v = findPath(paths, "value").msPerIter
    if r > 0.0:
      echo "   repr vs value: ", (v / r).formatFloat(ffDecimal, 1), "x"
  if has("repr") and has("interpreter"):
    let r = findPath(paths, "repr").msPerIter
    let i = findPath(paths, "interpreter").msPerIter
    if r > 0.0:
      echo "   repr vs interpreter: ", (i / r).formatFloat(ffDecimal, 1), "x"
