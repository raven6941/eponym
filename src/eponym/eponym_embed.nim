# eponym_embed.nim — Embedding dependently-typed sections in Nim programs
#
# The `eponym`/`eponymBlock` macros elaborate at compile time (type checking). This module
# provides the runtime support for *calling* elaborated definitions from
# Nim code.
#
# Design: the macro currently generates an integer wrapper for each `def`.
# The lower-level call API accepts and returns ETT Values, allowing typed
# Nim adapters to grow without limiting the evaluator to primitive Int.
#
# The elaborated terms are obtained by re-running the elaborator at
# runtime on the embedded source (cached after first use). Compile-time
# elaboration ensures the code is well-typed; runtime elaboration is
# just for getting the evaluable terms.

import tables
import sequtils
import elab
import eponym_init

# Cache: (baseDir, source) key -> checked module state. Retaining globals is
# required for runtime postulate bindings to use the identities assigned by
# the checker rather than resolve by a potentially ambiguous name.
type CheckedRuntime = object
  defs: seq[ElabDef]
  globals: Globals

var defCache {.global.}: Table[string, CheckedRuntime]
var holeDefCache {.global.}: Table[string, seq[ElabDef]]

proc cacheKey(baseDir, src: string): string =
  baseDir & "\x1f" & src

proc getDefs*(src: string): seq[ElabDef] =
  ## Get elaborated defs for source, using cache.
  if src in defCache:
    return defCache[src].defs
  let checked = elabCheckStateG(src)
  defCache[src] = CheckedRuntime(defs: checked.defs,
                                 globals: checked.globals)
  checked.defs

proc getDefsDir*(baseDir, src: string): seq[ElabDef] =
  ## Issue #131: like getDefs, but `import "path.ep"` declarations in `src`
  ## resolve relative to `baseDir` (via elabCheckDir). Used by eponymBlock
  ## wrappers so runtime re-elaboration sees the same modules the
  ## compile-time elaboration did.
  let key = cacheKey(baseDir, src)
  if key in defCache:
    return defCache[key].defs
  let checked = elabCheckDirState(src, baseDir)
  defCache[key] = CheckedRuntime(defs: checked.defs,
                                 globals: checked.globals)
  checked.defs

proc getGlobalsDir*(baseDir, src: string): Globals =
  ## Retrieve the checked globals associated with the same runtime module
  ## state as getDefsDir, including postulates from imported modules.
  discard getDefsDir(baseDir, src) # populate cache on first use
  defCache[cacheKey(baseDir, src)].globals

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

proc natToValue*(n: int): Value = vNatLit(n)

proc valueToNat*(v: Value): int =
  ## Convert a primitive Eponym Nat value to a Nim int.
  if v.whnf.kind == wNatLit:
    return v.whnf.natLitVal
  raise newException(ValueError, "value is not a canonical Nat literal")

proc callDefValue*(d: ElabDef, args: openArray[Value]): Value =
  ## Evaluate an elaborated definition with values from the ETT runtime.
  let t = d.tmTm
  var fn = eval(t, @[])
  for arg in args:
    let w = applyWhnf(fn, arg)
    fn = Value(syn: t, whnf: w)  # syn doesn't matter for result
  fn

proc callValueFunc*(src: string, name: string,
                    args: openArray[Value]): Value =
  ## Low-level runtime entry point over ETT values.
  callDefValue(findDef(getDefs(src), name), args)

proc callValueFuncDir*(baseDir, src: string, name: string,
                       args: openArray[Value]): Value =
  ## Directory-aware low-level runtime entry point over ETT values.
  callDefValue(findDef(getDefsDir(baseDir, src), name), args)

proc callDefInt(d: ElabDef, args: seq[int]): int =
  ## Compatibility bridge for `Int -> ... -> Int` generated wrappers.
  let values = args.mapIt(intToValue(it))
  valueToInt(callDefValue(d, values))

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
  if key in holeDefCache:
    return holeDefCache[key]
  let (defs, _, errLoc, errMsg) = elabCheckHolesDir(src, baseDir)
  if errMsg != "":
    raise newException(ValueError,
      "shedsBlock runtime elaboration failed at " &
      $errLoc.line & ":" & $errLoc.col & ": " & errMsg)
  holeDefCache[key] = defs
  defs

proc callIntFuncHolesDir*(baseDir, src: string, name: string,
                          args: seq[int]): int =
  ## Issue #133: like callIntFuncDir, but `src` may contain shed holes.
  let defs = getDefsHolesDir(baseDir, src)
  let d = findDef(defs, name)
  callDefInt(d, args)
