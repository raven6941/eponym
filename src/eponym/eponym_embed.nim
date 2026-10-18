# eponym_embed.nim — Embedding dependently-typed sections in Nim programs
#
# The `eponym`/`eponymBlock` macros elaborate at compile time (type checking). This module
# provides the runtime support for *calling* elaborated definitions from
# Nim code.
#
# Design: the macro generates typed wrappers for primitive Int/Nat and
# explicitly mapped opaque postulated types. The lower-level call API accepts
# and returns ETT Values, so host adapters are not limited to primitive Int.
#
# Compile-time Nim AST/VM objects cannot be retained as runtime Term values;
# the evaluator also needs runtime closures for checked definitions. The
# embedded source is therefore checked again on the first runtime call and
# the resulting terms and globals are cached by source and base directory.
# Subsequent calls use the cache rather than re-elaborating.

import tables
import sequtils
import elab
import eponym_init
import preterm  # Quantity constants for validating supported adapter shapes

proc hostIntUnary*(implementation: proc(x: int): int): Value
proc hostOpaqueUnary*[T](implementation: proc(x: T): T): Value
proc hostOpaqueBinary*[A, B, C](implementation: proc(x: A, y: B): C): Value
proc hostOpaqueTernary*[A, B, C, D](
  implementation: proc(x: A, y: B, z: C): D): Value
proc hostOpaqueNatUnary*[T](implementation: proc(x: T): int): Value
proc hostNatOpaqueBinary*[T](implementation: proc(n: int, x: T): T): Value

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

proc getGlobals*(src: string): Globals =
  ## Retrieve the checked global table for a non-directory embedded module.
  discard getDefs(src)
  defCache[src].globals

proc getDefsDir*(baseDir, src: string): seq[ElabDef] =
  ## Issue #131: like getDefs, but `import "path.ep"` declarations in `src`
  ## resolve relative to `baseDir` (via elabCheckDir). Used by eponymBlock
  ## wrappers so the one-time runtime elaboration sees the same modules as
  ## compile-time elaboration.
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

proc opaqueTypeHeadId(ty: Term): int
proc opaqueTypeName(globals: Globals, typeId: int,
                    postulateName: string): string
proc opaqueTypeId(globals: Globals, typeName, postulateName: string): int

proc validateHostOpaqueUnaryType*(globals: Globals,
                                  postulateName: string): string =
  ## Validate a first-order `T -> T` contract over an opaque Eponym type or
  ## indexed type family. Returns its name for an explicit Nim mapping.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let ty = entry.ty
  let domainId = if ty.kind == tPi: opaqueTypeHeadId(ty.dom) else: -1
  let resultId = if ty.kind == tPi: opaqueTypeHeadId(ty.scope.bdy) else: -1
  if ty.kind != tPi or ty.impl or ty.qty == q0 or domainId < 0 or
      domainId != resultId:
    raise newException(ValueError,
      "opaque unary adapter requires postulate '" & postulateName &
      "' to have type Opaque -> Opaque")
  opaqueTypeName(globals, domainId, postulateName)

proc validateHostOpaqueType*(globals: Globals, typeName: string) =
  ## Ensure an explicit runtimeType mapping refers to an opaque postulated
  ## type or type family, not an Eponym data type whose structure can compute.
  if typeName notin globals:
    raise newException(ValueError,
      "opaque runtime type '" & typeName & "' is not declared")
  let entry = globals[typeName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn or
      entry.ty.isNil:
    raise newException(ValueError,
      "opaque runtime type mapping '" & typeName &
      "' must name a postulated type or type family")
  var terminalType = entry.ty
  while terminalType.kind == tPi:
    terminalType = terminalType.scope.bdy
  if terminalType.kind != tType:
    raise newException(ValueError,
      "opaque runtime type mapping '" & typeName &
      "' must name a postulated type or type family")

proc opaqueTypeHeadId(ty: Term): int =
  case ty.kind
  of tR: ty.refId
  of tApp: opaqueTypeHeadId(ty.fn)
  else: -1

proc opaqueTypeName(globals: Globals, typeId: int,
                    postulateName: string): string =
  for typeName, typeEntry in globals.pairs:
    if not typeEntry.tm.isNil and typeEntry.tm.kind == tR and
        typeEntry.tm.refId == typeId:
      try:
        validateHostOpaqueType(globals, typeName)
        return typeName
      except ValueError:
        discard
  raise newException(ValueError,
    "opaque adapter type for postulate '" & postulateName &
    "' must be a named postulated type or type family")

proc validateHostOpaqueNatUnaryType*(globals: Globals, postulateName,
                                     opaqueType: string) =
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let opaqueId = opaqueTypeId(globals, opaqueType, postulateName)
  let natId = if "Nat" in globals: globals["Nat"].tm.refId else: -1
  if entry.ty.kind != tPi or entry.ty.impl or entry.ty.qty == q0 or
      opaqueTypeHeadId(entry.ty.dom) != opaqueId or
      entry.ty.scope.bdy.kind != tR or entry.ty.scope.bdy.refId != natId:
    raise newException(ValueError,
      "opaque Nat adapter requires postulate '" & postulateName & "' to have type " &
      opaqueType & " -> Nat")

proc validateHostNatOpaqueBinaryType*(globals: Globals, postulateName,
                                      opaqueArgType, opaqueResultType: string) =
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let argId = opaqueTypeId(globals, opaqueArgType, postulateName)
  let resultId = opaqueTypeId(globals, opaqueResultType, postulateName)
  let natId = if "Nat" in globals: globals["Nat"].tm.refId else: -1
  let outer = entry.ty
  let inner = if outer.kind == tPi: outer.scope.bdy else: nil
  if outer.kind != tPi or outer.impl or outer.qty == q0 or
      outer.dom.kind != tR or outer.dom.refId != natId or inner.isNil or
      inner.kind != tPi or inner.impl or inner.qty == q0 or
      opaqueTypeHeadId(inner.dom) != argId or
      opaqueTypeHeadId(inner.scope.bdy) != resultId:
    raise newException(ValueError,
      "Nat/opaque adapter requires postulate '" & postulateName &
      "' to have type Nat -> " & opaqueArgType & " -> " & opaqueResultType)

proc bindHostOpaqueNatUnary*[T](bindings: var RuntimeBindings,
                                globals: Globals, postulateName,
                                opaqueType: string,
                                implementation: proc(x: T): int) =
  validateHostOpaqueNatUnaryType(globals, postulateName, opaqueType)
  bindHostValue(bindings, globals, postulateName,
                hostOpaqueNatUnary[T](implementation))

proc bindHostNatOpaqueBinary*[T](bindings: var RuntimeBindings,
                                 globals: Globals, postulateName,
                                 opaqueArgType, opaqueResultType: string,
                                 implementation: proc(n: int, x: T): T) =
  validateHostNatOpaqueBinaryType(globals, postulateName, opaqueArgType,
                                  opaqueResultType)
  bindHostValue(bindings, globals, postulateName,
                hostNatOpaqueBinary[T](implementation))

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
      opaqueTypeHeadId(outer.dom) != firstId:
    raise newException(ValueError,
      "opaque binary adapter requires postulate '" & postulateName &
      "' to have the declared first argument type '" & firstTypeName & "'")
  let inner = outer.scope.bdy
  if inner.kind != tPi or inner.impl or inner.qty == q0 or
      opaqueTypeHeadId(inner.dom) != secondId or
      opaqueTypeHeadId(inner.scope.bdy) != resultId:
    raise newException(ValueError,
      "opaque binary adapter requires postulate '" & postulateName &
      "' to have type " & firstTypeName & " -> " & secondTypeName & " -> " &
      resultTypeName)

proc validateHostOpaqueTernaryType*(globals: Globals, postulateName,
                                   firstTypeName, secondTypeName,
                                   thirdTypeName, resultTypeName: string) =
  ## Validate a curried opaque contract `A -> B -> C -> D`.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let firstId = opaqueTypeId(globals, firstTypeName, postulateName)
  let secondId = opaqueTypeId(globals, secondTypeName, postulateName)
  let thirdId = opaqueTypeId(globals, thirdTypeName, postulateName)
  let resultId = opaqueTypeId(globals, resultTypeName, postulateName)
  let outer = entry.ty
  let middle = if outer.kind == tPi: outer.scope.bdy else: nil
  let inner = if not middle.isNil and middle.kind == tPi:
    middle.scope.bdy
  else: nil
  if outer.kind != tPi or outer.impl or outer.qty == q0 or
      opaqueTypeHeadId(outer.dom) != firstId or middle.isNil or
      middle.kind != tPi or middle.impl or middle.qty == q0 or
      opaqueTypeHeadId(middle.dom) != secondId or inner.isNil or
      inner.kind != tPi or inner.impl or inner.qty == q0 or
      opaqueTypeHeadId(inner.dom) != thirdId or
      opaqueTypeHeadId(inner.scope.bdy) != resultId:
    raise newException(ValueError,
      "opaque ternary adapter requires postulate '" & postulateName &
      "' to have type " & firstTypeName & " -> " & secondTypeName & " -> " &
      thirdTypeName & " -> " & resultTypeName)

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

proc bindHostOpaqueTernary*[A, B, C, D](bindings: var RuntimeBindings,
    globals: Globals, postulateName, firstTypeName, secondTypeName,
    thirdTypeName, resultTypeName: string,
    implementation: proc(x: A, y: B, z: C): D) =
  ## Bind a Nim `proc(A, B, C): D` to the explicitly mapped Eponym contract
  ## `E1 -> E2 -> E3 -> E4`. Payload representations and behavior are trusted.
  validateHostOpaqueTernaryType(globals, postulateName, firstTypeName,
    secondTypeName, thirdTypeName, resultTypeName)
  bindHostValue(bindings, globals, postulateName,
                hostOpaqueTernary[A, B, C, D](implementation))

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

proc hostOpaqueTernary*[A, B, C, D](
    implementation: proc(x: A, y: B, z: C): D): Value =
  ## Adapt a three-argument Nim procedure to a curried Eponym runtime function.
  vHostFunc(proc(first: Value): Value =
    vHostFunc(proc(second: Value): Value =
      vHostFunc(proc(third: Value): Value =
        toHostValue(implementation(valueToHost[A](first),
          valueToHost[B](second), valueToHost[C](third))))))

proc natToValue*(n: int): Value = vNatLit(n)

proc valueToNat*(v: Value): int =
  ## Convert a primitive Eponym Nat value to a Nim int.
  if v.whnf.kind == wNatLit:
    return v.whnf.natLitVal
  raise newException(ValueError, "value is not a canonical Nat literal")

proc hostOpaqueNatUnary*[T](implementation: proc(x: T): int): Value =
  ## Adapt an opaque Nim argument and primitive Nat result to a unary Eponym
  ## runtime function.
  vHostFunc(proc(value: Value): Value =
    natToValue(implementation(valueToHost[T](value))))

proc hostNatOpaqueBinary*[T](implementation: proc(n: int, x: T): T): Value =
  ## Adapt primitive Nat and opaque Nim arguments to a curried Eponym function.
  vHostFunc(proc(natValue: Value): Value =
    vHostFunc(proc(opaqueValue: Value): Value =
      toHostValue(implementation(valueToNat(natValue),
                                 valueToHost[T](opaqueValue)))))

proc callDefValueWithBindings*(d: ElabDef, args: openArray[Value],
                               bindings: RuntimeBindings): Value =
  ## Evaluate a checked definition with explicit host postulate bindings.
  let t = d.tmTm
  var fn = evalWithBindings(t, @[], bindings)
  for arg in args:
    let w = applyWhnf(fn, arg)
    fn = Value(syn: t, whnf: w)  # syn doesn't matter for result
  fn

proc callDefValueWithBindings*(d: ElabDef, args: openArray[Value],
                               bindings: RuntimeBindings,
                               globals: Globals): Value =
  ## Binding-aware call with a named diagnostic when an unbound postulate
  ## leaves the result stuck at a neutral reference.
  result = callDefValueWithBindings(d, args, bindings)
  let refId = runtimeReferenceId(result)
  if refId >= 0:
    for name, entry in globals.pairs:
      if not entry.tm.isNil and entry.tm.kind == tR and
          not entry.tm.refIsDefn and entry.tm.refId == refId:
        raise newException(ValueError,
          "unbound runtime postulate '" & name & "' while evaluating '" &
          d.name & "'")

proc callDefValue*(d: ElabDef, args: openArray[Value]): Value =
  ## Evaluate an elaborated definition with values from the ETT runtime.
  callDefValueWithBindings(d, args, initTable[int, Value]())

proc callValueFunc*(src: string, name: string,
                    args: openArray[Value]): Value =
  ## Low-level runtime entry point over ETT values.
  callDefValueWithBindings(findDef(getDefs(src), name), args,
                           initRuntimeBindings(), getGlobals(src))

proc callValueFuncDir*(baseDir, src: string, name: string,
                       args: openArray[Value]): Value =
  ## Directory-aware low-level runtime entry point over ETT values.
  callDefValueWithBindings(findDef(getDefsDir(baseDir, src), name), args,
                           initRuntimeBindings(), getGlobalsDir(baseDir, src))

proc callValueFuncDir*(baseDir, src: string, name: string,
                       args: openArray[Value],
                       bindings: RuntimeBindings): Value =
  ## Directory-aware Value call with block-local host postulate bindings.
  callDefValueWithBindings(findDef(getDefsDir(baseDir, src), name), args,
                           bindings, getGlobalsDir(baseDir, src))

proc callDefInt(d: ElabDef, args: seq[int]): int =
  ## Compatibility bridge for `Int -> ... -> Int` generated wrappers.
  let values = args.mapIt(intToValue(it))
  valueToInt(callDefValue(d, values))

proc callIntFunc*(src: string, name: string, args: seq[int]): int =
  ## Call an elaborated `def` of type `Int -> ... -> Int`.
  let defs = getDefs(src)
  let d = findDef(defs, name)
  let values = args.mapIt(intToValue(it))
  valueToInt(callDefValueWithBindings(d, values, initRuntimeBindings(),
                                      getGlobals(src)))

proc callIntFuncDir*(baseDir, src: string, name: string,
                     args: seq[int]): int =
  ## Issue #131: like callIntFunc, but `src` may contain `import`
  ## declarations resolved relative to `baseDir`.
  let defs = getDefsDir(baseDir, src)
  let d = findDef(defs, name)
  let values = args.mapIt(intToValue(it))
  valueToInt(callDefValueWithBindings(d, values, initRuntimeBindings(),
                                     getGlobalsDir(baseDir, src)))

proc callIntFuncDir*(baseDir, src: string, name: string,
                     args: seq[int], bindings: RuntimeBindings): int =
  ## Directory-aware integer wrapper with explicit host postulate bindings.
  let defs = getDefsDir(baseDir, src)
  let d = findDef(defs, name)
  let values = args.mapIt(intToValue(it))
  valueToInt(callDefValueWithBindings(d, values, bindings,
                                     getGlobalsDir(baseDir, src)))

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
