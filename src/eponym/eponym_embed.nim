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
import preterm  # Quantity constants for validating supported adapter shapes

proc hostIntUnary*(implementation: proc(x: int): int): Value
proc hostOpaqueUnary*[T](implementation: proc(x: T): T): Value
proc hostOpaqueBinary*[A, B, C](implementation: proc(x: A, y: B): C): Value

# Cache: (baseDir, source) key -> checked module state. Retaining globals is
# required for runtime postulate bindings to use the identities assigned by
# the checker rather than resolve by a potentially ambiguous name.
type CheckedRuntime = object
  defs: seq[ElabDef]
  globals: Globals

var defCache {.global.}: Table[string, CheckedRuntime]
var holeDefCache {.global.}: Table[string, seq[ElabDef]]

proc initRuntimeBindings*(): RuntimeBindings =
  ## Create an empty environment for explicit host postulate bindings.
  initTable[int, Value]()

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

proc bindHostValue*(bindings: var RuntimeBindings, globals: Globals,
                    postulateName: string, implementation: Value) =
  ## Bind one checked postulate reference to a runtime ETT value. The host
  ## implementation is trusted to honor the declared contract.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let id = entry.tm.refId
  if id in bindings:
    raise newException(ValueError,
      "duplicate runtime binding for postulate: " & postulateName)
  bindings[id] = implementation

proc validateHostIntUnaryType*(globals: Globals, postulateName: string) =
  ## Require an Eponym postulate with the exact runtime shape `Int -> Int`.
  ## Used at macro expansion and again at runtime before binding.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  if "Int" notin globals:
    raise newException(ValueError,
      "cannot bind Int adapter without an Eponym Int declaration")
  let intId = globals["Int"].tm.refId
  let ty = entry.ty
  if ty.kind != tPi or ty.impl or ty.qty == q0 or ty.dom.kind != tR or
      ty.dom.refId != intId or ty.scope.bdy.kind != tR or
      ty.scope.bdy.refId != intId:
    raise newException(ValueError,
      "Nim proc(int): int requires Eponym postulate '" & postulateName &
      "' to have type Int -> Int")

proc validateHostOpaqueUnaryType*(globals: Globals,
                                  postulateName: string): string =
  ## Validate a first-order `T -> T` contract over a named opaque Eponym type.
  ## Returns that Eponym type's name for an explicit Nim adapter mapping.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let ty = entry.ty
  if ty.kind != tPi or ty.impl or ty.qty == q0 or ty.dom.kind != tR or
      ty.scope.bdy.kind != tR or ty.dom.refId != ty.scope.bdy.refId:
    raise newException(ValueError,
      "opaque unary adapter requires postulate '" & postulateName &
      "' to have type Opaque -> Opaque")
  for typeName, typeEntry in globals.pairs:
    if not typeEntry.tm.isNil and typeEntry.tm.kind == tR and
        typeEntry.tm.refId == ty.dom.refId and typeEntry.ty.kind == tType:
      return typeName
  raise newException(ValueError,
    "opaque adapter type for postulate '" & postulateName &
    "' must be a named postulated type")

proc validateHostOpaqueType*(globals: Globals, typeName: string) =
  ## Ensure an explicit runtimeType mapping refers to an opaque postulated
  ## type, not an Eponym data type whose structure could be inspected.
  if typeName notin globals:
    raise newException(ValueError,
      "opaque runtime type '" & typeName & "' is not declared")
  let entry = globals[typeName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn or
      entry.ty.kind != tType:
    raise newException(ValueError,
      "opaque runtime type mapping '" & typeName &
      "' must name a postulated type")

proc opaqueTypeId(globals: Globals, typeName, postulateName: string): int =
  validateHostOpaqueType(globals, typeName)
  let entry = globals[typeName]
  entry.tm.refId

proc validateHostOpaqueBinaryType*(globals: Globals, postulateName,
                                   firstTypeName, secondTypeName,
                                   resultTypeName: string) =
  ## Validate a curried opaque contract `A -> B -> C`; every Eponym type to
  ## Nim type mapping is named explicitly by the caller.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let firstId = opaqueTypeId(globals, firstTypeName, postulateName)
  let secondId = opaqueTypeId(globals, secondTypeName, postulateName)
  let resultId = opaqueTypeId(globals, resultTypeName, postulateName)
  let outer = entry.ty
  if outer.kind != tPi or outer.impl or outer.qty == q0 or
      outer.dom.kind != tR or outer.dom.refId != firstId:
    raise newException(ValueError,
      "opaque binary adapter requires postulate '" & postulateName &
      "' to have the declared first argument type '" & firstTypeName & "'")
  let inner = outer.scope.bdy
  if inner.kind != tPi or inner.impl or inner.qty == q0 or
      inner.dom.kind != tR or inner.dom.refId != secondId or
      inner.scope.bdy.kind != tR or inner.scope.bdy.refId != resultId:
    raise newException(ValueError,
      "opaque binary adapter requires postulate '" & postulateName &
      "' to have type " & firstTypeName & " -> " & secondTypeName & " -> " &
      resultTypeName)

proc bindHostOpaqueBinary*[A, B, C](bindings: var RuntimeBindings,
                                    globals: Globals, postulateName,
                                    firstTypeName, secondTypeName,
                                    resultTypeName: string,
                                    implementation: proc(x: A, y: B): C) =
  ## Bind Nim `proc(A, B): C` to the explicitly mapped Eponym contract
  ## `E1 -> E2 -> E3`. All payload representations and behavior are trusted.
  validateHostOpaqueBinaryType(globals, postulateName, firstTypeName,
                               secondTypeName, resultTypeName)
  bindHostValue(bindings, globals, postulateName,
                hostOpaqueBinary[A, B, C](implementation))

proc bindHostOpaqueUnary*[T](bindings: var RuntimeBindings, globals: Globals,
                             postulateName, eponymTypeName: string,
                             implementation: proc(x: T): T) =
  ## Bind a Nim `proc(T): T` to an Eponym postulate `E -> E`, with the
  ## opaque mapping E = eponymTypeName made explicit at this boundary.
  let requiredType = validateHostOpaqueUnaryType(globals, postulateName)
  if requiredType != eponymTypeName:
    raise newException(ValueError,
      "postulate '" & postulateName & "' requires opaque Eponym type '" &
      requiredType & "', not '" & eponymTypeName & "'")
  bindHostValue(bindings, globals, postulateName,
                hostOpaqueUnary[T](implementation))

proc bindHostIntUnary*(bindings: var RuntimeBindings, globals: Globals,
                       postulateName: string,
                       implementation: proc(x: int): int) =
  ## Bind a Nim `proc(int): int` only to an Eponym postulate with the exact
  ## runtime shape `Int -> Int`. The implementation's behavior is trusted.
  validateHostIntUnaryType(globals, postulateName)
  bindHostValue(bindings, globals, postulateName, hostIntUnary(implementation))

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

proc hostIntUnary*(implementation: proc(x: int): int): Value =
  ## Adapt a Nim Int -> Int procedure to a runtime postulate value. Nim
  ## checks the adapter's concrete signature; the implementation's behavior
  ## remains trusted relative to the Eponym postulate.
  vHostFunc(proc(value: Value): Value =
    intToValue(implementation(valueToInt(value))))

proc hostOpaqueUnary*[T](implementation: proc(x: T): T): Value =
  ## Adapt an opaque Nim T -> T procedure. Eponym passes the value through
  ## without inspecting it; the callback and its adapter define its meaning.
  vHostFunc(proc(value: Value): Value =
    toHostValue(implementation(valueToHost[T](value))))

proc hostOpaqueBinary*[A, B, C](implementation: proc(x: A, y: B): C): Value =
  ## Adapt a two-argument Nim procedure to a curried Eponym runtime function.
  ## Values remain opaque and concrete Nim types are enforced when unboxing.
  vHostFunc(proc(first: Value): Value =
    vHostFunc(proc(second: Value): Value =
      toHostValue(implementation(valueToHost[A](first),
                                 valueToHost[B](second)))))

proc natToValue*(n: int): Value = vNatLit(n)

proc valueToNat*(v: Value): int =
  ## Convert a primitive Eponym Nat value to a Nim int.
  if v.whnf.kind == wNatLit:
    return v.whnf.natLitVal
  raise newException(ValueError, "value is not a canonical Nat literal")

proc callDefValueWithBindings*(d: ElabDef, args: openArray[Value],
                               bindings: RuntimeBindings): Value =
  ## Evaluate a checked definition with explicit host postulate bindings.
  let t = d.tmTm
  var fn = evalWithBindings(t, @[], bindings)
  for arg in args:
    let w = applyWhnf(fn, arg)
    fn = Value(syn: t, whnf: w)  # syn doesn't matter for result
  fn

proc callDefValue*(d: ElabDef, args: openArray[Value]): Value =
  ## Evaluate an elaborated definition with values from the ETT runtime.
  callDefValueWithBindings(d, args, initTable[int, Value]())

proc callValueFunc*(src: string, name: string,
                    args: openArray[Value]): Value =
  ## Low-level runtime entry point over ETT values.
  callDefValue(findDef(getDefs(src), name), args)

proc callValueFuncDir*(baseDir, src: string, name: string,
                       args: openArray[Value]): Value =
  ## Directory-aware low-level runtime entry point over ETT values.
  callDefValue(findDef(getDefsDir(baseDir, src), name), args)

proc callValueFuncDir*(baseDir, src: string, name: string,
                       args: openArray[Value],
                       bindings: RuntimeBindings): Value =
  ## Directory-aware Value call with block-local host postulate bindings.
  callDefValueWithBindings(findDef(getDefsDir(baseDir, src), name), args,
                           bindings)

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

proc callIntFuncDir*(baseDir, src: string, name: string,
                     args: seq[int], bindings: RuntimeBindings): int =
  ## Directory-aware integer wrapper with explicit host postulate bindings.
  let defs = getDefsDir(baseDir, src)
  let d = findDef(defs, name)
  let values = args.mapIt(intToValue(it))
  valueToInt(callDefValueWithBindings(d, values, bindings))

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
