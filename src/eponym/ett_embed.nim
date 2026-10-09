# ett_embed.nim — Embedding dependently-typed sections in Nim programs
#
# The `ett` macro elaborates at compile time (type checking). This module
# provides the runtime support for *calling* elaborated definitions from
# Nim code.
#
# Design: the macro generates a wrapper proc for each `def` of type
# `Int -> ... -> Int`. The wrapper converts Nim ints to ETT values,
# evaluates the elaborated term, and converts back.
#
# The elaborated terms are obtained by re-running the elaborator at
# runtime on the embedded source (cached after first use). Compile-time
# elaboration ensures the code is well-typed; runtime elaboration is
# just for getting the evaluable terms.

import tables
import elab
import ett_init

# Cache: source hash -> elaborated defs
var defCache {.global.}: Table[string, seq[ElabDef]]

proc getDefs*(src: string): seq[ElabDef] =
  ## Get elaborated defs for source, using cache.
  if src in defCache:
    return defCache[src]
  let defs = elabCheck(src)
  defCache[src] = defs
  defs

proc findDef*(defs: seq[ElabDef], name: string): ElabDef =
  for d in defs:
    if d.name == name:
      return d
  raise newException(ValueError, "proc not found: " & name)

proc intToValue*(n: int): Value =
  ## Convert Nim int to ETT primitive Int value.
  Value(syn: Term(kind: tInt, intVal: n),
        whnf: Whnf(kind: wInt, intVal: n))

proc valueToInt*(v: Value): int =
  ## Convert ETT value to Nim int (must be wInt).
  let w = v.whnf
  if w.kind == wInt:
    return w.intVal
  # Force evaluation if it's not yet a wInt
  raise newException(ValueError, "value is not an Int")

proc callIntFunc*(src: string, name: string, args: seq[int]): int =
  ## Call an elaborated `def` of type `Int -> ... -> Int`.
  let defs = getDefs(src)
  let d = findDef(defs, name)
  let t = d.tmTm
  # Evaluate the term to a value
  var fn = eval(t, @[])
  # Apply to each argument
  for a in args:
    let v = intToValue(a)
    let w = applyWhnf(fn, v)
    fn = Value(syn: t, whnf: w)  # syn doesn't matter for result
  valueToInt(fn)
