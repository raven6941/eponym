# eponym_embed.nim — Embedding dependently-typed sections in Nim programs
#
# The `eponym`/`eponymBlock` macros elaborate at compile time (type checking). This module
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
import eponym_init

# Cache: (baseDir, source) key -> elaborated defs
var defCache {.global.}: Table[string, seq[ElabDef]]

proc cacheKey(baseDir, src: string): string =
  baseDir & "\x1f" & src

proc getDefs*(src: string): seq[ElabDef] =
  ## Get elaborated defs for source, using cache.
  if src in defCache:
    return defCache[src]
  let defs = elabCheck(src)
  defCache[src] = defs
  defs

proc getDefsDir*(baseDir, src: string): seq[ElabDef] =
  ## Issue #131: like getDefs, but `import "path.ep"` declarations in `src`
  ## resolve relative to `baseDir` (via elabCheckDir). Used by eponymBlock
  ## wrappers so runtime re-elaboration sees the same modules the
  ## compile-time elaboration did.
  let key = cacheKey(baseDir, src)
  if key in defCache:
    return defCache[key]
  let defs = elabCheckDir(src, baseDir)
  defCache[key] = defs
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

proc callDefInt(d: ElabDef, args: seq[int]): int =
  ## Evaluate an elaborated `def` of type `Int -> ... -> Int` on args.
  ## (shared by callIntFunc and callIntFuncDir)
  let t = d.tmTm
  # Evaluate the term to a value
  var fn = eval(t, @[])
  # Apply to each argument
  for a in args:
    let v = intToValue(a)
    let w = applyWhnf(fn, v)
    fn = Value(syn: t, whnf: w)  # syn doesn't matter for result
  valueToInt(fn)

proc callIntFunc*(src: string, name: string, args: seq[int]): int =
  ## Call an elaborated `def` of type `Int -> ... -> Int`.
  let defs = getDefs(src)
  let d = findDef(defs, name)
  callDefInt(d, args)

proc callIntFuncDir*(baseDir, src: string, name: string,
                     args: seq[int]): int =
  ## Issue #131: like callIntFunc, but `src` may contain `import`
  ## declarations resolved relative to `baseDir`.
  let defs = getDefsDir(baseDir, src)
  let d = findDef(defs, name)
  callDefInt(d, args)

proc getDefsHolesDir*(baseDir, src: string): seq[ElabDef] =
  ## Issue #133: like getDefsDir, but hole-tolerant (elabCheckHolesDir):
  ## embedded sources containing shed holes (`?`) elaborate without
  ## failing on unsolved metas. Used by shedsBlock wrappers so a block
  ## mixing complete defs and shed holes still runs its complete defs.
  let key = cacheKey(baseDir, src) & "\x1eholes"
  if key in defCache:
    return defCache[key]
  let (defs, _, errLoc, errMsg) = elabCheckHolesDir(src, baseDir)
  if errMsg != "":
    raise newException(ValueError,
      "shedsBlock runtime elaboration failed at " &
      $errLoc.line & ":" & $errLoc.col & ": " & errMsg)
  defCache[key] = defs
  defs

proc callIntFuncHolesDir*(baseDir, src: string, name: string,
                          args: seq[int]): int =
  ## Issue #133: like callIntFuncDir, but `src` may contain shed holes.
  let defs = getDefsHolesDir(baseDir, src)
  let d = findDef(defs, name)
  callDefInt(d, args)
