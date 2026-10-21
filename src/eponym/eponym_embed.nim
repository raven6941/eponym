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
import strutils
import options
import macros  # NimNode fields of HostRuntimeType
import elab
import eponym_init
import preterm  # Quantity constants for validating supported adapter shapes

type
  ## Public aliases for runtime values in generated wrapper signatures. Users
  ## can call raw-value wrappers by importing eponym_embed alone.
  RuntimeValue* = Value
  RuntimeGlobals* = Globals
  RuntimeValueResult* = tuple[value: RuntimeValue, globals: RuntimeGlobals]

type
  HostRuntimeType* = object
    ## One `runtimeType`/`runtimeVector`/`runtimeList`/`runtimeOption`/
    ## `runtimeVariant`/`runtimeCodec` declaration from an `eponymBlock` body:
    ## the host representation the typed wrappers convert to at the boundary.
    ## Issue #330 uses this as the backend's representation spec: the codegen
    ## emitter consults it to compile bodies against host representations
    ## directly instead of `Value`s.
    eponymName*: string
    nimType*: NimNode
    isRuntimeVector*: bool
    isRuntimeList*: bool
    isRuntimeOption*: bool
    isRuntimeVariant*: bool
    isRuntimeCodec*: bool
    isGenericTypeWitnessable*: bool
    encoder*: NimNode
    decoder*: NimNode

proc hostIntUnary*(implementation: proc(x: int): int): Value
proc hostOpaqueUnary*[T](implementation: proc(x: T): T): Value
proc hostOpaqueMapUnary*[A, B](implementation: proc(x: A): B): Value
proc hostOpaqueBinary*[A, B, C](implementation: proc(x: A, y: B): C): Value
proc hostOpaqueTernary*[A, B, C, D](
  implementation: proc(x: A, y: B, z: C): D): Value
proc hostOpaqueQuaternary*[A, B, C, D, E](
  implementation: proc(w: A, x: B, y: C, z: D): E): Value
proc hostOpaqueQuinary*[A, B, C, D, E, F](
  implementation: proc(v: A, w: B, x: C, y: D, z: E): F): Value
proc hostOpaqueNatUnary*[T](implementation: proc(x: T): int): Value
proc hostNatOpaqueBinary*[T](implementation: proc(n: int, x: T): T): Value
proc hostNatOpaqueBinary*[T](globals: Globals,
  implementation: proc(n: int, x: T): T): Value
proc hostNatOpaqueMapBinary*[A, B](
  implementation: proc(n: int, x: A): B): Value
proc hostNatOpaqueMapBinary*[A, B](globals: Globals,
  implementation: proc(n: int, x: A): B): Value
proc hostValueNary*(arity: int,
                    implementation: proc(args: seq[Value],
                                          globals: Globals): Value,
                    globals: Globals): Value
proc validateHostValueNaryType*(globals: Globals,
                                postulateName: string): int
proc callRuntimeValue*(fn: Value, args: openArray[Value]): Value
proc natToValue*(n: int, globals: Globals): Value
proc valueToNat*(v: Value, globals: Globals): int
proc runtimeValueDebugString*(value: RuntimeValue,
                              globals: RuntimeGlobals): string
proc debugEchoRuntimeValue*(args: seq[RuntimeValue],
                            globals: RuntimeGlobals): RuntimeValue

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
  let checked = elabCheckDirStateAll(src, baseDir)
  defCache[key] = CheckedRuntime(defs: checked.allDefs,
                                 globals: checked.globals)
  checked.allDefs

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

proc bindHostValueNary*(bindings: var RuntimeBindings, globals: Globals,
                        postulateName: string,
                        implementation: proc(args: seq[Value],
                                              globals: Globals): Value) =
  let arity = validateHostValueNaryType(globals, postulateName)
  bindHostValue(bindings, globals, postulateName,
                hostValueNary(arity, implementation, globals))

proc opaqueTypeHeadId(ty: Term): int
proc canonicalNatConstructorIds(globals: Globals):
    tuple[zeroId, sucId: int, valid: bool]

proc validateHostSigmaAdapterType*(globals: Globals, postulateName: string,
    argTypeNames: openArray[string], firstTypeName, secondTypeName: string,
    allowDependentIndex = false) =
  ## Validate named arguments followed by a non-dependent Sigma result:
  ## A1 -> ... -> An -> Sig(B, C). The Sigma fields are checked by their
  ## type-family heads; indices on named families remain part of the trusted
  ## host codec boundary.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  for typeName in argTypeNames:
    if typeName notin globals or globals[typeName].tm.isNil or
        globals[typeName].tm.kind != tR:
      raise newException(ValueError,
        "structured adapter type is not a declared Eponym type: " & typeName)
  for typeName in [firstTypeName, secondTypeName]:
    if typeName notin globals or globals[typeName].tm.isNil or
        globals[typeName].tm.kind != tR:
      raise newException(ValueError,
        "structured adapter type is not a declared Eponym type: " & typeName)
  let expectedFirstId = globals[firstTypeName].tm.refId
  let expectedSecondId = globals[secondTypeName].tm.refId
  var current = entry.ty
  var validArguments = true
  for argTypeName in argTypeNames:
    if current.isNil or current.kind != tPi or current.impl or
        current.qty == q0 or
        opaqueTypeHeadId(current.dom) != globals[argTypeName].tm.refId:
      validArguments = false
      break
    current = current.scope.bdy
  let pairTy = current
  var dependent = false
  proc referencesSigmaBinder(term: Term, depth: int): bool =
    if term.isNil: return false
    if term.kind == tV: return term.idx == depth
    case term.kind
    of tPi, tSi, tLam:
      referencesSigmaBinder(term.dom, depth) or
        referencesSigmaBinder(term.scope.bdy, depth + 1)
    of tApp:
      referencesSigmaBinder(term.fn, depth) or
        referencesSigmaBinder(term.arg, depth)
    of tPair:
      referencesSigmaBinder(term.pFst, depth) or
        referencesSigmaBinder(term.pSnd, depth) or
        referencesSigmaBinder(term.pScope.bdy, depth + 1)
    of tFst, tSnd, tAbsurd:
      referencesSigmaBinder(term.sub, depth)
    of tLet:
      referencesSigmaBinder(term.letVal, depth) or
        referencesSigmaBinder(term.letTy, depth) or
        referencesSigmaBinder(term.letScope.bdy, depth + 1)
    of tR, tV, tMeta, tC, tInt, tPrim, tNatLit, tNatSing, tType: false
  if pairTy != nil and pairTy.kind == tSi:
    dependent = referencesSigmaBinder(pairTy.scope.bdy, 0)
  if not validArguments or pairTy.isNil or pairTy.kind != tSi or
      pairTy.impl or (dependent and not allowDependentIndex) or
      opaqueTypeHeadId(pairTy.dom) != expectedFirstId or
      opaqueTypeHeadId(pairTy.scope.bdy) != expectedSecondId:
    let argTypeSig = argTypeNames.join(" -> ")
    raise newException(ValueError,
      "structured pair adapter requires postulate '" & postulateName &
      "' to have type " & argTypeSig & " -> Sig(" & firstTypeName & ", " &
      secondTypeName & ") with " &
      (if allowDependentIndex: "a mapped pair" else: "a non-dependent pair"))

proc validateHostVectorCodec*(globals: Globals, familyName: string) =
  ## Accept the canonical length-indexed vector shape with `nil` and `cons`.
  if familyName notin globals or "Nat" notin globals or
      "nil" notin globals or "cons" notin globals:
    raise newException(ValueError,
      "runtimeVector requires the family, Nat, nil, and cons declarations")
  let family = globals[familyName]
  let nat = globals["Nat"]
  let nilCtor = globals["nil"]
  let consCtor = globals["cons"]
  if family.tm.isNil or family.tm.kind != tR or family.tm.refIsDefn or
      nat.tm.isNil or nat.tm.kind != tR or nilCtor.tm.isNil or
      consCtor.tm.isNil or not nilCtor.isDataConstructor or
      not consCtor.isDataConstructor:
    raise newException(ValueError,
      "runtimeVector requires a declared data family and its constructors")
  let familyId = family.tm.refId
  let natId = nat.tm.refId
  let natConstructors = canonicalNatConstructorIds(globals)
  if not natConstructors.valid:
    raise newException(ValueError,
      "runtimeVector requires canonical zero and suc Nat constructors")
  proc appArgs(term: Term): seq[Term] =
    if term.isNil: return
    if term.kind == tApp:
      result = appArgs(term.fn)
      result.add(term.arg)
  proc isVar(term: Term, index: int): bool =
    not term.isNil and term.kind == tV and term.idx == index
  proc isRef(term: Term, refId: int): bool =
    not term.isNil and term.kind == tR and term.refId == refId
  proc isFamilyApp(term: Term, argCount: int): bool =
    let args = appArgs(term)
    not term.isNil and term.kind == tApp and
      opaqueTypeHeadId(term) == familyId and
      args.len == argCount
  let nilTy = nilCtor.ty
  let consTy = consCtor.ty
  if family.ty.isNil or family.ty.kind != tPi or
      family.ty.dom.kind != tType or family.ty.scope.bdy.isNil or
      family.ty.scope.bdy.kind != tPi or
      opaqueTypeHeadId(family.ty.scope.bdy.dom) != natId or
      family.ty.scope.bdy.scope.bdy.kind != tType:
    raise newException(ValueError,
      "runtimeVector family must have shape Type -> Nat -> Type")
  if nilTy.isNil or nilTy.kind != tPi or nilTy.dom.kind != tType or
      nilTy.impl or nilTy.qty == q0 or
      not isFamilyApp(nilTy.scope.bdy, 2) or
      not isVar(appArgs(nilTy.scope.bdy)[0], 0) or
      not isRef(appArgs(nilTy.scope.bdy)[1],
        natConstructors.zeroId):
    raise newException(ValueError,
      "runtimeVector nil constructor must take a type and return " & familyName)
  if consTy.isNil or consTy.kind != tPi or consTy.dom.kind != tType or
      consTy.impl or consTy.qty == q0:
    raise newException(ValueError,
      "runtimeVector cons constructor must take a type parameter")
  let lengthBinder = consTy.scope.bdy
  if lengthBinder.isNil or lengthBinder.kind != tPi or lengthBinder.impl or
      lengthBinder.qty == q0 or
      opaqueTypeHeadId(lengthBinder.dom) != natId:
    raise newException(ValueError,
      "runtimeVector cons must take a Nat tail length")
  let elementBinder = lengthBinder.scope.bdy
  if elementBinder.isNil or elementBinder.kind != tPi or elementBinder.impl or
      elementBinder.qty == q0 or not isVar(elementBinder.dom, 1):
    raise newException(ValueError,
      "runtimeVector cons must take an element")
  let tailBinder = elementBinder.scope.bdy
  if tailBinder.isNil or tailBinder.kind != tPi or tailBinder.impl or
      tailBinder.qty == q0 or not isFamilyApp(tailBinder.dom, 2) or
      not isVar(appArgs(tailBinder.dom)[0], 2) or
      not isVar(appArgs(tailBinder.dom)[1], 1) or
      not isFamilyApp(tailBinder.scope.bdy, 2) or
      not isVar(appArgs(tailBinder.scope.bdy)[0], 3):
    raise newException(ValueError,
      "runtimeVector cons must take a tail and return " & familyName)

proc validateHostListCodec*(globals: Globals, familyName: string) =
  ## Accept the standard unindexed List family with nil and cons constructors.
  if familyName notin globals or "nil" notin globals or "cons" notin globals:
    raise newException(ValueError,
      "runtimeList requires the family, nil, and cons declarations")
  let family = globals[familyName]
  let nilCtor = globals["nil"]
  let consCtor = globals["cons"]
  if family.tm.isNil or family.tm.kind != tR or family.tm.refIsDefn or
      nilCtor.tm.isNil or consCtor.tm.isNil or
      not nilCtor.isDataConstructor or not consCtor.isDataConstructor:
    raise newException(ValueError,
      "runtimeList requires a declared data family and its constructors")
  let familyId = family.tm.refId
  proc appArgs(term: Term): seq[Term] =
    if term.isNil: return
    if term.kind == tApp:
      result = appArgs(term.fn)
      result.add(term.arg)
  proc isVar(term: Term, index: int): bool =
    not term.isNil and term.kind == tV and term.idx == index
  proc isFamilyApp(term: Term): bool =
    let args = appArgs(term)
    not term.isNil and term.kind == tApp and
      opaqueTypeHeadId(term) == familyId and
      args.len == 1
  let familyTy = family.ty
  if familyTy.isNil or familyTy.kind != tPi or familyTy.dom.kind != tType or
      familyTy.scope.bdy.kind != tType:
    raise newException(ValueError,
      "runtimeList family must have shape Type -> Type")
  let nilTy = nilCtor.ty
  if nilTy.isNil or nilTy.kind != tPi or nilTy.dom.kind != tType or
      nilTy.impl or nilTy.qty == q0 or
      not isFamilyApp(nilTy.scope.bdy) or
      not isVar(appArgs(nilTy.scope.bdy)[0], 0):
    raise newException(ValueError,
      "runtimeList nil constructor must take a type and return " & familyName)
  let consTy = consCtor.ty
  if consTy.isNil or consTy.kind != tPi or consTy.dom.kind != tType or
      consTy.impl or consTy.qty == q0:
    raise newException(ValueError,
      "runtimeList cons constructor must take a type parameter")
  let elementBinder = consTy.scope.bdy
  if elementBinder.isNil or elementBinder.kind != tPi or elementBinder.impl or
      elementBinder.qty == q0 or not isVar(elementBinder.dom, 0):
    raise newException(ValueError,
      "runtimeList cons constructor must take an element")
  let tailBinder = elementBinder.scope.bdy
  if tailBinder.isNil or tailBinder.kind != tPi or tailBinder.impl or
      tailBinder.qty == q0 or not isFamilyApp(tailBinder.dom) or
      not isVar(appArgs(tailBinder.dom)[0], 1) or
      not isFamilyApp(tailBinder.scope.bdy) or
      not isVar(appArgs(tailBinder.scope.bdy)[0], 2):
    raise newException(ValueError,
      "runtimeList cons must take a tail and return " & familyName)

proc validateHostOptionCodec*(globals: Globals, familyName: string) =
  ## Accept the canonical unary Option family with none and some constructors.
  if familyName notin globals or "none" notin globals or "some" notin globals:
    raise newException(ValueError,
      "runtimeOption requires the family, none, and some declarations")
  let family = globals[familyName]
  let noneCtor = globals["none"]
  let someCtor = globals["some"]
  if family.tm.isNil or family.tm.kind != tR or family.tm.refIsDefn or
      noneCtor.tm.isNil or someCtor.tm.isNil or
      not noneCtor.isDataConstructor or not someCtor.isDataConstructor or
      family.ty.isNil or family.ty.kind != tPi or
      family.ty.dom.isNil or family.ty.dom.kind != tType or
      family.ty.scope.bdy.isNil or family.ty.scope.bdy.kind != tType:
    raise newException(ValueError,
      "runtimeOption requires a Type -> Type family and its constructors")
  let familyId = family.tm.refId
  proc appArgs(term: Term): seq[Term] =
    if term.isNil: return
    if term.kind == tApp:
      result = appArgs(term.fn)
      result.add(term.arg)
  proc isVar(term: Term, index: int): bool =
    not term.isNil and term.kind == tV and term.idx == index
  proc isFamilyApp(term: Term, index: int): bool =
    if term.isNil or term.kind != tApp or opaqueTypeHeadId(term) != familyId:
      return false
    let args = appArgs(term)
    args.len == 1 and isVar(args[0], index)
  let noneTy = noneCtor.ty
  let someTy = someCtor.ty
  if noneTy.isNil or noneTy.kind != tPi or noneTy.dom.isNil or
      noneTy.dom.kind != tType or
      noneTy.impl or noneTy.qty == q0 or
      not isFamilyApp(noneTy.scope.bdy, 0):
    raise newException(ValueError,
      "runtimeOption none must take a type and return " & familyName)
  if someTy.isNil or someTy.kind != tPi or someTy.dom.isNil or
      someTy.dom.kind != tType or
      someTy.impl or someTy.qty == q0:
    raise newException(ValueError,
      "runtimeOption some must take a type parameter")
  let valueBinder = someTy.scope.bdy
  if valueBinder.isNil or valueBinder.kind != tPi or valueBinder.dom.isNil or
      valueBinder.dom.kind != tV or
      valueBinder.dom.idx != 0 or valueBinder.impl or valueBinder.qty == q0 or
      not isFamilyApp(valueBinder.scope.bdy, 1):
    raise newException(ValueError,
      "runtimeOption some must take a value and return " & familyName)

proc natIndexSucc*(n: int): int =
  if n < 0 or n == high(int):
    raise newException(ValueError, "Nat index is outside Nim int range")
  n + 1

proc natIndexAdd*(a, b: int): int =
  if a < 0 or b < 0 or b > high(int) - a:
    raise newException(ValueError, "Nat index addition is outside Nim int range")
  a + b

proc natIndexMul*(a, b: int): int =
  if a < 0 or b < 0 or (a != 0 and b > high(int) div a):
    raise newException(ValueError, "Nat index multiplication is outside Nim int range")
  a * b

proc seqToVecValue*[T](items: seq[T], expectedLength: int, globals: Globals,
    familyName: string,
    encode: proc(item: T, globals: Globals): Value,
    elementType: Value = nil): Value =
  if expectedLength < 0:
    raise newException(ValueError, "Vec length cannot be negative")
  if items.len != expectedLength:
    raise newException(ValueError,
      "runtime Vec length mismatch: expected " & $expectedLength &
      ", got " & $items.len)
  validateHostVectorCodec(globals, familyName)
  let representedType = if elementType.isNil: vType(0) else: elementType
  result = callRuntimeValue(eval(globals["nil"].tm, @[]), @[representedType])
  for i in countdown(items.high, 0):
    let encodedItem = encode(items[i], globals)
    let tailLength = natToValue(items.high - i, globals)
    result = callRuntimeValue(eval(globals["cons"].tm, @[]),
      @[representedType, tailLength, encodedItem, result])

proc vecValueToSeq*[T](value: Value, expectedLength: int, globals: Globals,
    familyName: string,
    decode: proc(value: Value, globals: Globals): T): seq[T] =
  if expectedLength < 0:
    raise newException(ValueError, "Vec length cannot be negative")
  validateHostVectorCodec(globals, familyName)
  result = newSeqOfCap[T](expectedLength)
  let nilId = globals["nil"].tm.refId
  let consId = globals["cons"].tm.refId
  var current = value
  for i in 0 ..< expectedLength:
    if current.whnfKind != wRef or current.whnfRefId != consId or
        current.whnfSpineLen != 4:
      raise newException(ValueError,
        "runtime value is not a Vec of the declared length")
    for argIndex in 0 ..< current.whnfSpineLen:
      if current.whnfSpineKind(argIndex) != eApp:
        raise newException(ValueError,
          "runtime Vec constructor has an invalid spine")
    let expectedTailLength = expectedLength - i - 1
    if valueToNat(current.whnfSpineArg(1), globals) != expectedTailLength:
      raise newException(ValueError,
        "runtime Vec tail index does not match its spine")
    result.add(decode(current.whnfSpineArg(2), globals))
    current = current.whnfSpineArg(3)
  if current.whnfKind != wRef or current.whnfRefId != nilId or
      current.whnfSpineLen != 1 or current.whnfSpineKind(0) != eApp:
    raise newException(ValueError,
      "runtime value is not a Vec of the declared length")

proc seqToListValue*[T](items: seq[T], globals: Globals,
    familyName: string,
    encode: proc(item: T, globals: Globals): Value,
    elementType: Value = nil): Value =
  validateHostListCodec(globals, familyName)
  let representedType = if elementType.isNil: vType(0) else: elementType
  result = callRuntimeValue(eval(globals["nil"].tm, @[]), @[representedType])
  for i in countdown(items.high, 0):
    let encodedItem = encode(items[i], globals)
    result = callRuntimeValue(eval(globals["cons"].tm, @[]),
      @[representedType, encodedItem, result])

proc listValueToSeq*[T](value: Value, globals: Globals,
    familyName: string,
    decode: proc(value: Value, globals: Globals): T): seq[T] =
  validateHostListCodec(globals, familyName)
  let nilId = globals["nil"].tm.refId
  let consId = globals["cons"].tm.refId
  var current = value
  while true:
    if current.whnfKind != wRef:
      raise newException(ValueError, "runtime value is not a List")
    if current.whnfRefId == nilId:
      if current.whnfSpineLen != 1 or current.whnfSpineKind(0) != eApp:
        raise newException(ValueError, "runtime List nil constructor has invalid spine")
      return
    if current.whnfRefId != consId or current.whnfSpineLen != 3:
      raise newException(ValueError, "runtime value is not a List")
    for argIndex in 0 ..< current.whnfSpineLen:
      if current.whnfSpineKind(argIndex) != eApp:
        raise newException(ValueError,
          "runtime List constructor has an invalid spine")
    result.add(decode(current.whnfSpineArg(1), globals))
    current = current.whnfSpineArg(2)

proc optionToValue*[T](hostValue: Option[T], globals: Globals,
    familyName: string,
    encode: proc(item: T, globals: Globals): Value,
    elementType: Value = nil): Value =
  validateHostOptionCodec(globals, familyName)
  let representedType = if elementType.isNil: vType(0) else: elementType
  if hostValue.isSome:
    let encoded = encode(hostValue.get, globals)
    return callRuntimeValue(eval(globals["some"].tm, @[]),
      @[representedType, encoded])
  callRuntimeValue(eval(globals["none"].tm, @[]), @[representedType])

proc valueToOption*[T](value: Value, globals: Globals,
    familyName: string,
    decode: proc(value: Value, globals: Globals): T): Option[T] =
  validateHostOptionCodec(globals, familyName)
  if value.whnfKind != wRef:
    raise newException(ValueError, "runtime value is not an Option")
  let noneId = globals["none"].tm.refId
  let someId = globals["some"].tm.refId
  if value.whnfRefId == noneId:
    if value.whnfSpineLen != 1 or value.whnfSpineKind(0) != eApp:
      raise newException(ValueError,
        "runtime Option none constructor has invalid spine")
    return none(T)
  if value.whnfRefId != someId or value.whnfSpineLen != 2 or
      value.whnfSpineKind(0) != eApp or value.whnfSpineKind(1) != eApp:
    raise newException(ValueError, "runtime value is not an Option")
  some(decode(value.whnfSpineArg(1), globals))

proc validateHostMappedNaryType*(globals: Globals, postulateName: string,
                                 typeNames: openArray[string]) =
  ## Validate `A1 -> ... -> An -> R` against the explicitly named Eponym
  ## type heads used by a typed arbitrary-arity Nim adapter.
  if typeNames.len < 2:
    raise newException(ValueError,
      "typed n-ary adapter needs at least one argument and a result type")
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  var expectedIds: seq[int] = @[]
  for typeName in typeNames:
    if typeName notin globals or globals[typeName].tm.isNil or
        globals[typeName].tm.kind != tR:
      raise newException(ValueError,
        "typed n-ary adapter type is not a declared Eponym type: " & typeName)
    expectedIds.add(globals[typeName].tm.refId)
  var current = entry.ty
  for i in 0 ..< typeNames.len - 1:
    if current.isNil or current.kind != tPi or current.impl or
        current.qty == q0 or opaqueTypeHeadId(current.dom) != expectedIds[i]:
      raise newException(ValueError,
        "typed n-ary adapter requires postulate '" & postulateName &
        "' to have type " & typeNames.join(" -> "))
    current = current.scope.bdy
  if current.isNil or opaqueTypeHeadId(current) != expectedIds[^1]:
    raise newException(ValueError,
      "typed n-ary adapter requires postulate '" & postulateName &
      "' to have type " & typeNames.join(" -> "))

proc validateHostValueNaryType*(globals: Globals,
                                postulateName: string): int =
  ## Validate the deliberately low-level Value adapter target and return its
  ## curried arity. The adapter receives raw Values and is responsible for
  ## honoring every domain and result in the checked postulate type.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  var current = entry.ty
  while not current.isNil and current.kind == tPi:
    if current.impl or current.qty == q0:
      raise newException(ValueError,
        "raw Value adapter requires runtime-visible Pi binders for '" &
        postulateName & "'")
    inc result
    current = current.scope.bdy
  if result == 0:
    raise newException(ValueError,
      "raw Value adapter requires a postulate with at least one argument: " &
      postulateName)

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

proc validateHostOpaqueMapUnaryType*(globals: Globals, postulateName,
                                     argTypeName, resultTypeName: string) =
  ## Validate a unary opaque contract `A -> B`, where the Nim representations
  ## may differ (for example, a handle mapped to a Future result).
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let argId = opaqueTypeId(globals, argTypeName, postulateName)
  let resultId = opaqueTypeId(globals, resultTypeName, postulateName)
  let ty = entry.ty
  if ty.kind != tPi or ty.impl or ty.qty == q0 or
      opaqueTypeHeadId(ty.dom) != argId or
      opaqueTypeHeadId(ty.scope.bdy) != resultId:
    raise newException(ValueError,
      "opaque unary adapter requires postulate '" & postulateName &
      "' to have type " & argTypeName & " -> " & resultTypeName)

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

proc validateHostRuntimeCodecType*(globals: Globals, typeName: string) =
  ## A user codec may describe any named Eponym type or family, including
  ## transparent data whose constructors the adapter translates itself.
  if typeName notin globals:
    raise newException(ValueError,
      "runtime codec type '" & typeName & "' is not declared")
  let entry = globals[typeName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.ty.isNil:
    raise newException(ValueError,
      "runtime codec mapping '" & typeName & "' must name an Eponym type")
  var terminalType = entry.ty
  while not terminalType.isNil and terminalType.kind == tPi:
    terminalType = terminalType.scope.bdy
  if terminalType.isNil or terminalType.kind != tType:
    raise newException(ValueError,
      "runtime codec mapping '" & typeName & "' must name an Eponym type")

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
                hostNatOpaqueBinary[T](globals, implementation))

proc bindHostNatOpaqueMapBinary*[A, B](bindings: var RuntimeBindings,
    globals: Globals, postulateName, opaqueArgType, opaqueResultType: string,
    implementation: proc(n: int, x: A): B) =
  ## Bind `Nat -> A -> B` where A and B use distinct Nim representations.
  validateHostNatOpaqueBinaryType(globals, postulateName, opaqueArgType,
                                  opaqueResultType)
  bindHostValue(bindings, globals, postulateName,
                hostNatOpaqueMapBinary[A, B](globals, implementation))

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

proc validateHostOpaqueQuaternaryType*(globals: Globals, postulateName,
    firstTypeName, secondTypeName, thirdTypeName, fourthTypeName,
    resultTypeName: string) =
  ## Validate a curried opaque contract `A -> B -> C -> D -> E`.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let ids = [opaqueTypeId(globals, firstTypeName, postulateName),
    opaqueTypeId(globals, secondTypeName, postulateName),
    opaqueTypeId(globals, thirdTypeName, postulateName),
    opaqueTypeId(globals, fourthTypeName, postulateName),
    opaqueTypeId(globals, resultTypeName, postulateName)]
  var current = entry.ty
  for i in 0 ..< 4:
    if current.isNil or current.kind != tPi or current.impl or
        current.qty == q0 or opaqueTypeHeadId(current.dom) != ids[i]:
      raise newException(ValueError,
        "opaque quaternary adapter requires postulate '" & postulateName &
        "' to have type " & firstTypeName & " -> " & secondTypeName &
        " -> " & thirdTypeName & " -> " & fourthTypeName & " -> " &
        resultTypeName)
    current = current.scope.bdy
  if current.isNil or opaqueTypeHeadId(current) != ids[4]:
    raise newException(ValueError,
      "opaque quaternary adapter requires postulate '" & postulateName &
      "' to have type " & firstTypeName & " -> " & secondTypeName & " -> " &
      thirdTypeName & " -> " & fourthTypeName & " -> " & resultTypeName)

proc validateHostOpaqueQuinaryType*(globals: Globals, postulateName,
    firstTypeName, secondTypeName, thirdTypeName, fourthTypeName,
    fifthTypeName, resultTypeName: string) =
  ## Validate a curried opaque contract `A -> B -> C -> D -> E -> F`.
  if postulateName notin globals:
    raise newException(ValueError, "postulate not found: " & postulateName)
  let entry = globals[postulateName]
  if entry.tm.isNil or entry.tm.kind != tR or entry.tm.refIsDefn:
    raise newException(ValueError,
      "runtime binding target is not a postulate: " & postulateName)
  let names = [firstTypeName, secondTypeName, thirdTypeName,
               fourthTypeName, fifthTypeName, resultTypeName]
  var ids: array[6, int]
  for i, typeName in names:
    ids[i] = opaqueTypeId(globals, typeName, postulateName)
  var current = entry.ty
  for i in 0 ..< 5:
    if current.isNil or current.kind != tPi or current.impl or
        current.qty == q0 or opaqueTypeHeadId(current.dom) != ids[i]:
      raise newException(ValueError,
        "opaque quinary adapter requires postulate '" & postulateName &
        "' to have type " & names.join(" -> "))
    current = current.scope.bdy
  if current.isNil or opaqueTypeHeadId(current) != ids[5]:
    raise newException(ValueError,
      "opaque quinary adapter requires postulate '" & postulateName &
      "' to have type " & names.join(" -> "))

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

proc bindHostOpaqueQuaternary*[A, B, C, D, E](bindings: var RuntimeBindings,
    globals: Globals, postulateName, firstTypeName, secondTypeName,
    thirdTypeName, fourthTypeName, resultTypeName: string,
    implementation: proc(w: A, x: B, y: C, z: D): E) =
  ## Bind a Nim `proc(A, B, C, D): E` to a four-argument opaque contract.
  validateHostOpaqueQuaternaryType(globals, postulateName, firstTypeName,
    secondTypeName, thirdTypeName, fourthTypeName, resultTypeName)
  bindHostValue(bindings, globals, postulateName,
    hostOpaqueQuaternary[A, B, C, D, E](implementation))

proc bindHostOpaqueQuinary*[A, B, C, D, E, F](bindings: var RuntimeBindings,
    globals: Globals, postulateName, firstTypeName, secondTypeName,
    thirdTypeName, fourthTypeName, fifthTypeName, resultTypeName: string,
    implementation: proc(v: A, w: B, x: C, y: D, z: E): F) =
  ## Bind a Nim `proc(A, B, C, D, E): F` to a five-argument opaque contract.
  validateHostOpaqueQuinaryType(globals, postulateName, firstTypeName,
    secondTypeName, thirdTypeName, fourthTypeName, fifthTypeName,
    resultTypeName)
  bindHostValue(bindings, globals, postulateName,
    hostOpaqueQuinary[A, B, C, D, E, F](implementation))

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

proc bindHostOpaqueMapUnary*[A, B](bindings: var RuntimeBindings,
    globals: Globals, postulateName, argTypeName, resultTypeName: string,
    implementation: proc(x: A): B) =
  ## Bind a Nim `proc(A): B` to a mapped opaque Eponym contract `E1 -> E2`.
  validateHostOpaqueMapUnaryType(globals, postulateName, argTypeName,
                                 resultTypeName)
  bindHostValue(bindings, globals, postulateName,
                hostOpaqueMapUnary[A, B](implementation))

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

proc runtimePairFirst*(value: Value): Value =
  if value.whnfKind != wPair:
    raise newException(ValueError, "runtime value is not a pair")
  value.whnfFst

proc runtimePairSecond*(value: Value): Value =
  if value.whnfKind != wPair:
    raise newException(ValueError, "runtime value is not a pair")
  value.whnfSnd

proc valueToInt*(v: Value): int =
  ## Convert ETT value to Nim int (must be wInt).
  let w = v.whnf
  if w.kind == wInt:
    return w.intVal
  # Force evaluation if it's not yet a wInt
  raise newException(ValueError, "value is not an Int")

proc boolToValue*(value: bool, globals: Globals): Value =
  ## Encode a Nim bool using the checked Bool constructors from this module.
  let constructorName = if value: "true" else: "false"
  if constructorName notin globals:
    raise newException(ValueError,
      "runtime Bool constructors are unavailable (import bool.ep)")
  eval(globals[constructorName].tm, @[])

proc valueToBool*(value: Value, globals: Globals): bool =
  ## Decode only the canonical `true` and `false` constructors.
  if "true" notin globals or "false" notin globals:
    raise newException(ValueError,
      "runtime Bool constructors are unavailable (import bool.ep)")
  let valueId = runtimeReferenceId(value)
  let trueId = globals["true"].tm.refId
  let falseId = globals["false"].tm.refId
  if valueId == trueId: return true
  if valueId == falseId: return false
  raise newException(ValueError, "runtime value is not a canonical Bool")

proc enumToValue*[T: enum](hostValue: T, globals: Globals,
                            constructors: openArray[string]): Value =
  ## Encode a Nim enum using same-named, nullary Eponym constructors.
  let constructorName = $hostValue
  if constructorName notin constructors or constructorName notin globals or
      not globals[constructorName].isDataConstructor:
    raise newException(ValueError,
      "Nim enum member '" & constructorName &
      "' has no matching Eponym data constructor")
  eval(globals[constructorName].tm, @[])

proc valueToEnum*[T: enum](value: Value, globals: Globals,
                           constructors: openArray[string]): T =
  ## Decode only the mapped nullary Eponym constructors.
  let valueId = runtimeReferenceId(value)
  for constructorName in constructors:
    if constructorName in globals and
        globals[constructorName].tm.refId == valueId and
        globals[constructorName].isDataConstructor:
      try:
        return parseEnum[T](constructorName)
      except ValueError:
        raise newException(ValueError,
          "Nim enum type has no member named '" & constructorName & "'")
  raise newException(ValueError,
    "runtime value is not one of the mapped Eponym constructors")

proc validateRuntimeValueType*(value, expectedType: Value,
                               globals: Globals)
proc validateRuntimeValueAgainstType*(value, expectedType: Value,
                                      globals: Globals)

type RuntimeVariant* = object
  ## Generic structural view of an Eponym data constructor application.
  ## Payloads stay as Values so callers can recursively decode only the fields
  ## they understand. Extraction checks constructor identity and spine shape;
  ## callers crossing an untrusted raw-Value boundary should also validate the
  ## value against its expected Eponym type.
  constructor*: string
  arguments*: seq[Value]

proc runtimeVariantArity(entry: GEntry): int =
  var ty = entry.ty
  while not ty.isNil and ty.kind == tPi:
    inc result
    ty = ty.scope.bdy

proc validateRuntimeVariantArguments(constructorName: string,
    arguments: openArray[Value], globals: Globals) =
  ## Check constructor payloads against each successive Pi domain. Applying
  ## each prior argument first preserves dependencies between constructor
  ## fields, such as an index field followed by a value indexed by it.
  var currentType = eval(globals[constructorName].ty, @[])
  for index, argument in arguments:
    if currentType.isNil or currentType.whnfKind != wPi:
      raise newException(ValueError,
        "runtime variant constructor '" & constructorName &
        "' has no domain for argument " & $index)
    try:
      validateRuntimeValueAgainstType(argument, currentType.whnfDom, globals)
    except ValueError as error:
      raise newException(ValueError,
        "runtime variant constructor '" & constructorName &
        "' argument " & $index & " has the wrong type: " & error.msg)
    currentType = whnfScopeApply(currentType, argument)

proc validateRuntimeConstructorValue(value, expectedType: Value,
    globals: Globals): bool =
  ## Runtime primitive terms do not carry their Eponym type in their syntax.
  ## Validate constructor applications through their checked Pi domains so
  ## those terms cannot be smuggled into an unrelated constructor field.
  if value.isNil or value.whnfKind != wRef: return false
  for name, entry in globals.pairs:
    if not entry.isDataConstructor or entry.tm.isNil or
        entry.tm.kind != tR or entry.tm.refId != value.whnfRefId:
      continue
    if value.whnfSpineLen != runtimeVariantArity(entry):
      raise newException(ValueError,
        "runtime constructor '" & name & "' has an invalid spine")
    var currentType = eval(entry.ty, @[])
    for index in 0 ..< value.whnfSpineLen:
      if value.whnfSpineKind(index) != eApp:
        raise newException(ValueError,
          "runtime constructor '" & name &
          "' spine contains a non-argument field")
      let argument = value.whnfSpineArg(index)
      if currentType.isNil or currentType.whnfKind != wPi:
        raise newException(ValueError,
          "runtime constructor '" & name &
          "' has no domain for argument " & $index)
      validateRuntimeValueAgainstType(argument, currentType.whnfDom, globals)
      currentType = whnfScopeApply(currentType, argument)
    var supply = Supply()
    for _, globalEntry in globals.pairs:
      if not globalEntry.tm.isNil and globalEntry.tm.kind == tR:
        reserveFreshIdsThrough(supply, globalEntry.tm.refId)
    areEqual(supply, vStar(), currentType, expectedType)
    return true
  false

proc validateRuntimeVariantConstructors*(globals: Globals,
    familyName: string, constructors: openArray[string]) =
  if familyName notin globals or constructors.len == 0:
    raise newException(ValueError,
      "runtimeVariant requires a declared family and constructors")
  let family = globals[familyName]
  if family.tm.isNil or family.tm.kind != tR or family.tm.refIsDefn:
    raise newException(ValueError,
      "runtimeVariant requires a declared data family")
  for name in constructors:
    if name notin globals:
      raise newException(ValueError,
        "runtimeVariant constructor '" & name & "' is not declared")
    let ctor = globals[name]
    if not ctor.isDataConstructor or ctor.ty.isNil:
      raise newException(ValueError,
        "runtimeVariant member '" & name & "' is not a data constructor")
    var resultType = ctor.ty
    while not resultType.isNil and resultType.kind == tPi:
      resultType = resultType.scope.bdy
    if resultType.isNil or opaqueTypeHeadId(resultType) != family.tm.refId:
      raise newException(ValueError,
        "runtimeVariant constructor '" & name &
        "' does not return family '" & familyName & "'")

proc runtimeVariantConstructorNames*(globals: Globals,
                                     familyName: string): seq[string] =
  if familyName notin globals:
    raise newException(ValueError,
      "runtimeVariant family '" & familyName & "' is not declared")
  let familyId = globals[familyName].tm.refId
  for name, entry in globals.pairs:
    if not entry.isDataConstructor or entry.ty.isNil: continue
    var resultType = entry.ty
    while not resultType.isNil and resultType.kind == tPi:
      resultType = resultType.scope.bdy
    if not resultType.isNil and opaqueTypeHeadId(resultType) == familyId:
      result.add(name)

proc runtimeVariantToValue*(variant: RuntimeVariant, globals: Globals,
    familyName: string, constructors: openArray[string]): Value =
  validateRuntimeVariantConstructors(globals, familyName, constructors)
  if variant.constructor notin constructors or
      variant.constructor notin globals:
    raise newException(ValueError,
      "runtime variant constructor is not a member of '" & familyName & "'")
  let ctor = globals[variant.constructor]
  let expectedArity = runtimeVariantArity(ctor)
  if variant.arguments.len != expectedArity:
    raise newException(ValueError,
      "runtime variant constructor '" & variant.constructor &
      "' expects " & $expectedArity & " arguments, got " &
      $variant.arguments.len)
  validateRuntimeVariantArguments(variant.constructor, variant.arguments,
    globals)
  result = callRuntimeValue(eval(ctor.tm, @[]), variant.arguments)
  if result.whnfKind != wRef or result.whnfRefId != ctor.tm.refId or
      result.whnfSpineLen != expectedArity:
    raise newException(ValueError,
      "runtime variant constructor application has an invalid spine")

proc valueToRuntimeVariant*(value: Value, globals: Globals,
    familyName: string, constructors: openArray[string]): RuntimeVariant =
  validateRuntimeVariantConstructors(globals, familyName, constructors)
  if value.whnfKind != wRef:
    raise newException(ValueError,
      "runtime value is not a constructor of '" & familyName & "'")
  for name in constructors:
    let ctor = globals[name]
    if value.whnfRefId != ctor.tm.refId: continue
    let expectedArity = runtimeVariantArity(ctor)
    if value.whnfSpineLen != expectedArity:
      raise newException(ValueError,
        "runtime variant constructor '" & name & "' has an invalid spine")
    result.constructor = name
    for i in 0 ..< value.whnfSpineLen:
      if value.whnfSpineKind(i) != eApp:
        raise newException(ValueError,
          "runtime variant constructor spine contains a non-argument field")
      result.arguments.add(value.whnfSpineArg(i))
    return
  raise newException(ValueError,
    "runtime value is not a constructor of '" & familyName & "'")

proc validateRuntimeValueType*(value: Value, globals: Globals,
                               typeName: string) =
  ## Check an unmapped generic Value against a named Eponym type. This is a
  ## runtime type check, not a host representation mapping.
  if typeName notin globals or value.isNil or value.syn.isNil:
    raise newException(ValueError,
      "cannot validate runtime Value against Eponym type '" & typeName & "'")
  let expected = eval(globals[typeName].tm, @[])
  validateRuntimeValueType(value, expected, globals)

proc runtimeGlobalValue*(globals: Globals, name: string): Value =
  if name notin globals or globals[name].tm.isNil:
    raise newException(ValueError,
      "runtime type expression refers to unknown Eponym name '" & name & "'")
  eval(globals[name].tm, @[])

proc runtimeDependentArrowType*(domain: Value, globals: Globals,
    codomainFn: proc(argument: Value): Value {.closure.},
    priorArguments: openArray[Value] = []): Value =
  ## Build a dependent Pi type, reserving IDs used by checked globals and
  ## earlier binders before introducing the new parameter.
  if domain.isNil or codomainFn.isNil:
    raise newException(ValueError, "cannot build an incomplete dependent Pi")
  var supply = Supply()
  for _, entry in globals.pairs:
    if not entry.tm.isNil and entry.tm.kind == tR:
      reserveFreshIdsThrough(supply, entry.tm.refId)
  for prior in priorArguments:
    if not prior.isNil and prior.whnfKind == wRef:
      reserveFreshIdsThrough(supply, prior.whnfRefId)
  let argument = freshPara(supply, domain)
  let codomain = codomainFn(argument)
  runtimeDependentPiType(domain, argument, codomain, codomainFn)

proc runtimeDependentSigmaType*(domain: Value, globals: Globals,
    codomainFn: proc(argument: Value): Value {.closure.},
    priorArguments: openArray[Value] = []): Value =
  ## Build a dependent Sigma type, reserving IDs used by checked globals and
  ## earlier binders before introducing the new field.
  if domain.isNil or codomainFn.isNil:
    raise newException(ValueError,
      "cannot build an incomplete dependent Sigma")
  var supply = Supply()
  for _, entry in globals.pairs:
    if not entry.tm.isNil and entry.tm.kind == tR:
      reserveFreshIdsThrough(supply, entry.tm.refId)
  for prior in priorArguments:
    if not prior.isNil and prior.whnfKind == wRef:
      reserveFreshIdsThrough(supply, prior.whnfRefId)
  let argument = freshPara(supply, domain)
  let codomain = codomainFn(argument)
  runtimeDependentSigmaType(domain, argument, codomain, codomainFn)

proc runtimeGlobalTypeWitness*(globals: Globals, name: string): Value =
  ## Return a generic type witness only for a named, unindexed Eponym type.
  ## A mapped indexed family needs its indices as well as its Nim type mapping.
  if name notin globals or globals[name].tm.isNil or
      globals[name].ty.isNil:
    return nil
  let declaredType = eval(globals[name].ty, @[])
  if declaredType.whnfKind != wType: return nil
  eval(globals[name].tm, @[])

proc runtimeTypeWitnessOrUniverse*(witness: Value): Value =
  if witness.isNil: vType(0) else: witness

proc runtimeValueTerm(value: Value, globals: Globals): Term =
  if value.isNil: return nil
  case value.whnfKind
  of wInt: return tmInt(value.whnfIntVal)
  of wNatLit: return tmNatLit(value.whnfNatLitVal)
  of wRef:
    for _, entry in globals.pairs:
      if not entry.tm.isNil and entry.tm.kind == tR and
          entry.tm.refId == value.whnfRefId:
        result = entry.tm
        for i in 0 ..< value.whnfSpineLen:
          if value.whnfSpineKind(i) != eApp: return value.syn
          let argument = runtimeValueTerm(value.whnfSpineArg(i), globals)
          if argument.isNil: return value.syn
          result = tmApp(result, argument)
        return
    return value.syn
  of wLam, wLam0:
    if not value.whnf.hostFunctionType.isNil:
      return Term(kind: tR, refId: -1,
        refTyp: value.whnf.hostFunctionType, refIsDefn: false, refVal: nil)
    if value.syn.isNil:
      raise newException(ValueError,
        "runtime Value has no syntax for type inference")
    return value.syn
  of wHost:
    if not value.whnf.hostEponymType.isNil:
      return Term(kind: tR, refId: -1,
        refTyp: value.whnf.hostEponymType, refIsDefn: false, refVal: nil)
    return value.syn
  else:
    value.syn

proc inferRuntimeValueType(value: Value, globals: Globals,
                          supply: var Supply): Value =
  if value.isNil:
    raise newException(ValueError, "cannot infer the type of a nil runtime Value")
  case value.whnfKind
  of wInt:
    if "Int" notin globals:
      raise newException(ValueError,
        "cannot infer an Int Value without the Int declaration")
    return eval(globals["Int"].tm, @[])
  of wNatLit:
    if "Nat" notin globals:
      raise newException(ValueError,
        "cannot infer a Nat Value without the Nat declaration")
    return eval(globals["Nat"].tm, @[])
  of wRef:
    let natConstructors = canonicalNatConstructorIds(globals)
    if natConstructors.valid and
        value.whnfRefId in [natConstructors.zeroId, natConstructors.sucId]:
      # `infer` recursively checks every `suc` argument. Recognize canonical
      # Nat constructor chains iteratively so large runtime indices do not
      # exhaust the Nim call stack just to recover their type.
      discard valueToNat(value, globals)
      return eval(globals["Nat"].tm, @[])
    var term: Term = nil
    for _, entry in globals.pairs:
      if not entry.tm.isNil and entry.tm.kind == tR and
          entry.tm.refId == value.whnfRefId:
        term = entry.tm
        break
    if term.isNil:
      raise newException(ValueError,
        "runtime Value reference is not present in checked globals")
    for i in 0 ..< value.whnfSpineLen:
      if value.whnfSpineKind(i) != eApp:
        raise newException(ValueError,
          "cannot infer runtime Value type through a non-application spine")
      let argument = runtimeValueTerm(value.whnfSpineArg(i), globals)
      if argument.isNil:
        raise newException(ValueError,
          "runtime Value argument has no syntax for type inference")
      term = tmApp(term, argument)
    return infer(supply, term)
  of wLam, wLam0:
    if not value.whnf.hostFunctionType.isNil:
      return value.whnf.hostFunctionType
    if value.syn.isNil:
      raise newException(ValueError,
        "runtime Value has no syntax for type inference")
    return infer(supply, value.syn)
  of wHost:
    if not value.whnf.hostEponymType.isNil:
      return value.whnf.hostEponymType
    if value.syn.isNil:
      raise newException(ValueError,
        "runtime Value has no syntax for type inference")
    return infer(supply, value.syn)
  else:
    if value.syn.isNil:
      raise newException(ValueError,
        "runtime Value has no syntax for type inference")
    infer(supply, value.syn)

proc runtimeValueTypeOf*(value: Value, globals: Globals): Value =
  ## Infer a runtime Value's Eponym type while keeping generated IDs clear of
  ## the checked globals in its environment.
  if value.isNil:
    raise newException(ValueError,
      "cannot infer the type of a nil runtime Value")
  var supply = Supply()
  for _, entry in globals.pairs:
    if not entry.tm.isNil and entry.tm.kind == tR:
      reserveFreshIdsThrough(supply, entry.tm.refId)
  result = inferRuntimeValueType(value, globals, supply)
  if result.isNil:
    raise newException(ValueError,
      "runtime Value has no inferable Eponym type witness")

proc validateRuntimeValueType*(value, expectedType: Value,
                               globals: Globals) =
  if value.isNil or expectedType.isNil:
    raise newException(ValueError, "cannot validate an incomplete runtime Value")
  var supply = Supply()
  for _, entry in globals.pairs:
    if not entry.tm.isNil and entry.tm.kind == tR:
      reserveFreshIdsThrough(supply, entry.tm.refId)
  let inferred = inferRuntimeValueType(value, globals, supply)
  areEqual(supply, vStar(), inferred, expectedType)

proc validateRuntimeValueAgainstType*(value, expectedType: Value,
    globals: Globals) =
  ## Validate pair values structurally against Sigma types. Other values use
  ## ordinary checked runtime type inference, including Pi-valued callbacks.
  if value.isNil or expectedType.isNil:
    raise newException(ValueError, "cannot validate an incomplete runtime Value")
  var expectedInt = false
  var expectedNat = false
  if expectedType.whnfKind == wRef and expectedType.whnfSpineLen == 0:
    if "Int" in globals:
      let intType = runtimeGlobalValue(globals, "Int")
      if intType.whnfKind == wRef and
          expectedType.whnfRefId == intType.whnfRefId:
        expectedInt = true
    if "Nat" in globals:
      let natType = runtimeGlobalValue(globals, "Nat")
      if natType.whnfKind == wRef and
          expectedType.whnfRefId == natType.whnfRefId:
        expectedNat = true
  if value.whnfKind == wInt:
    if expectedInt: return
    raise newException(ValueError,
      "runtime value type mismatch: Int does not match the expected Eponym type")
  if value.whnfKind == wNatLit:
    if expectedNat:
      discard valueToNat(value, globals)
      return
    raise newException(ValueError,
      "runtime value type mismatch: Nat does not match the expected Eponym type")
  if expectedInt:
    raise newException(ValueError, "runtime value type mismatch for Int")
  if expectedNat:
    discard valueToNat(value, globals)
    return
  if expectedType.whnfKind == wSi:
    if value.whnfKind != wPair:
      raise newException(ValueError,
        "runtime value is not a pair for the expected Sigma type")
    let first = runtimePairFirst(value)
    validateRuntimeValueAgainstType(first, expectedType.whnfDom, globals)
    let codomain = whnfScopeApply(expectedType, first)
    validateRuntimeValueAgainstType(runtimePairSecond(value), codomain, globals)
    return
  if validateRuntimeConstructorValue(value, expectedType, globals): return
  validateRuntimeValueType(value, expectedType, globals)

proc runtimePiDomainAfterArgs*(piType: Value,
    priorArguments: openArray[Value]): Value =
  ## Return the next argument domain after consuming preceding Pi arguments.
  var current = piType
  for argument in priorArguments:
    if current.isNil or current.whnfKind != wPi:
      raise newException(ValueError,
        "runtime callback Pi witness has fewer arguments than supplied")
    current = whnfScopeApply(current, argument)
  if current.isNil or current.whnfKind != wPi:
    raise newException(ValueError,
      "runtime callback Pi witness has no remaining argument domain")
  current.whnfDom

proc runtimePiResultAfterArgs*(piType: Value,
    arguments: openArray[Value]): Value =
  ## Apply a runtime Pi witness to all callback arguments to get its result.
  result = piType
  for argument in arguments:
    if result.isNil or result.whnfKind != wPi:
      raise newException(ValueError,
        "runtime callback Pi witness has fewer arguments than supplied")
    result = whnfScopeApply(result, argument)

proc prependErasedTypeArgs*(typeArgCount: int,
                            args: openArray[Value]): seq[Value] =
  ## Runtime computation does not inspect type-level generic binders. Supply
  ## one inert universe value for each such binder before the term arguments.
  result = newSeqOfCap[Value](typeArgCount + args.len)
  for _ in 0 ..< typeArgCount:
    result.add(vType(0))
  for arg in args:
    result.add(arg)

proc prependRuntimeArgs*(genericArgs: openArray[Value],
                         args: openArray[Value]): seq[Value] =
  ## Add explicitly represented generic arguments (type and static value
  ## indices) before the ordinary runtime values.
  result = newSeqOfCap[Value](genericArgs.len + args.len)
  for arg in genericArgs:
    result.add(arg)
  for arg in args:
    result.add(arg)

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

proc hostOpaqueMapUnary*[A, B](implementation: proc(x: A): B): Value =
  ## Adapt a unary Nim callback between distinct opaque Eponym mappings.
  vHostFunc(proc(value: Value): Value =
    toHostValue(implementation(valueToHost[A](value))))

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

proc hostOpaqueQuaternary*[A, B, C, D, E](
    implementation: proc(w: A, x: B, y: C, z: D): E): Value =
  ## Adapt four typed Nim arguments to a curried Eponym runtime function.
  vHostFunc(proc(first: Value): Value =
    vHostFunc(proc(second: Value): Value =
      vHostFunc(proc(third: Value): Value =
        vHostFunc(proc(fourth: Value): Value =
          toHostValue(implementation(valueToHost[A](first),
            valueToHost[B](second), valueToHost[C](third),
            valueToHost[D](fourth)))))))

proc hostOpaqueQuinary*[A, B, C, D, E, F](
    implementation: proc(v: A, w: B, x: C, y: D, z: E): F): Value =
  ## Adapt five typed Nim arguments to a curried Eponym runtime function.
  vHostFunc(proc(first: Value): Value =
    vHostFunc(proc(second: Value): Value =
      vHostFunc(proc(third: Value): Value =
        vHostFunc(proc(fourth: Value): Value =
          vHostFunc(proc(fifth: Value): Value =
            toHostValue(implementation(valueToHost[A](first),
              valueToHost[B](second), valueToHost[C](third),
              valueToHost[D](fourth), valueToHost[E](fifth))))))))

proc natToValue*(n: int): Value = vNatLit(n)

proc canonicalNatConstructorIds(globals: Globals):
    tuple[zeroId, sucId: int, valid: bool] =
  if "Nat" notin globals or "zero" notin globals or "suc" notin globals:
    return
  let natType = globals["Nat"]
  let zero = globals["zero"]
  let suc = globals["suc"]
  if natType.tm.isNil or natType.tm.kind != tR or zero.tm.isNil or
      suc.tm.isNil or not zero.isDataConstructor or
      not suc.isDataConstructor or zero.ty.isNil or suc.ty.isNil or
      zero.ty.kind != tR or zero.ty.refId != natType.tm.refId or
      suc.ty.kind != tPi or suc.ty.dom.kind != tR or
      suc.ty.dom.refId != natType.tm.refId or
      suc.ty.scope.bdy.kind != tR or
      suc.ty.scope.bdy.refId != natType.tm.refId:
    return
  (zero.tm.refId, suc.tm.refId, true)

proc natToValue*(n: int, globals: Globals): Value =
  ## Prefer checked zero/suc constructors when available so Eponym definitions
  ## that eliminate Nat values can compute; retain literals for opaque Nat.
  if n < 0:
    raise newException(ValueError, "Nat cannot be negative")
  let constructors = canonicalNatConstructorIds(globals)
  if not constructors.valid:
    return natToValue(n)
  result = eval(globals["zero"].tm, @[])
  for _ in 0 ..< n:
    result = callRuntimeValue(eval(globals["suc"].tm, @[]), @[result])

proc valueToNat*(v: Value): int =
  ## Convert a primitive Eponym Nat value to a Nim int.
  if v.whnf.kind == wNatLit:
    return v.whnf.natLitVal
  raise newException(ValueError, "value is not a canonical Nat literal")

proc valueToNat*(v: Value, globals: Globals): int =
  ## Decode either a canonical Nat literal or its checked zero/suc constructor
  ## representation using the constructor identities from the same module.
  if v.whnfKind == wNatLit:
    return v.whnfNatLitVal
  let constructors = canonicalNatConstructorIds(globals)
  if not constructors.valid:
    raise newException(ValueError, "runtime Nat constructors are unavailable")
  var current = v
  while true:
    case current.whnfKind
    of wNatLit:
      if current.whnfNatLitVal > high(int) - result:
        raise newException(ValueError, "runtime Nat does not fit Nim int")
      result += current.whnfNatLitVal
      return
    of wRef:
      let id = current.whnfRefId
      if id == constructors.zeroId:
        if current.whnfSpineLen != 0:
          raise newException(ValueError, "runtime value is not a Nat")
        return
      if id != constructors.sucId or current.whnfSpineLen != 1 or
          current.whnfSpineKind(0) != eApp:
        raise newException(ValueError, "runtime value is not a Nat")
      if result == high(int):
        raise newException(ValueError, "runtime Nat does not fit Nim int")
      inc result
      current = current.whnfSpineArg(0)
    else:
      raise newException(ValueError, "runtime value is not a Nat")

proc runtimeValueDebugString*(value: RuntimeValue,
                              globals: RuntimeGlobals): string =
  ## Render a checked runtime value for an explicitly bound debug postulate.
  ## Opaque Nim objects are identified by their mapped Nim type, without
  ## exposing their payload.
  if value.isNil:
    return "<nil runtime value>"
  if value.whnf.isNil:
    return "<runtime value without a weak-head form>"
  if value.whnf.kind == wHost:
    return "<opaque Nim " & value.whnf.hostTypeName & ">"
  var refNames = initTable[int, string]()
  for name, entry in globals:
    if not entry.tm.isNil and entry.tm.kind == tR:
      refNames[entry.tm.refId] = name
  if value.syn.isNil:
    return "<runtime value without syntax>"
  prettyTerm(value.syn, @[], refNames)

proc debugEchoRuntimeValue*(args: seq[RuntimeValue],
                            globals: RuntimeGlobals): RuntimeValue =
  ## Runtime adapter for the generic `debugEcho` postulate in `lib/debug.ep`.
  ## Its first argument is the explicit Eponym type parameter, followed by
  ## the value to display. The debug operation returns that value unchanged.
  if args.len != 2:
    raise newException(ValueError,
      "debugEcho runtime adapter expects a type and a value")
  echo runtimeValueDebugString(args[1], globals)
  args[1]

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

proc hostNatOpaqueBinary*[T](globals: Globals,
    implementation: proc(n: int, x: T): T): Value =
  ## Decode constructor-based Nat values using the bound module's constructors.
  vHostFunc(proc(natValue: Value): Value =
    vHostFunc(proc(opaqueValue: Value): Value =
      toHostValue(implementation(valueToNat(natValue, globals),
                                 valueToHost[T](opaqueValue)))))

proc hostNatOpaqueMapBinary*[A, B](
    implementation: proc(n: int, x: A): B): Value =
  ## Adapt a Nat and opaque argument to a potentially different opaque result.
  vHostFunc(proc(natValue: Value): Value =
    vHostFunc(proc(opaqueValue: Value): Value =
      toHostValue(implementation(valueToNat(natValue),
                                 valueToHost[A](opaqueValue)))))

proc hostNatOpaqueMapBinary*[A, B](globals: Globals,
    implementation: proc(n: int, x: A): B): Value =
  ## Decode constructor-based Nat arguments using the bound module's
  ## constructors.
  vHostFunc(proc(natValue: Value): Value =
    vHostFunc(proc(opaqueValue: Value): Value =
      toHostValue(implementation(valueToNat(natValue, globals),
                                 valueToHost[A](opaqueValue)))))

proc hostValueNary*(arity: int,
                    implementation: proc(args: seq[Value],
                                         globals: Globals): Value,
                    globals: Globals): Value =
  ## Explicit raw-Value escape hatch. Eponym checks callers against the full
  ## postulate, while the host adapter owns conversion and semantics.
  if arity < 1:
    raise newException(ValueError, "raw Value adapter arity must be positive")
  proc curry(args: seq[Value]): Value =
    if args.len == arity:
      return implementation(args, globals)
    vHostFunc(proc(arg: Value): Value = curry(args & @[arg]))
  curry(@[])

proc callRuntimeValue*(fn: Value, args: openArray[Value]): Value =
  ## Apply a checked runtime callback. A wLam retains the binding environment
  ## from its definition, including block-local postulate adapters.
  result = fn
  for arg in args:
    result = vAppWithBindings(result, arg, initRuntimeBindings())

proc callDefValueWithBindings*(d: ElabDef, args: openArray[Value],
                               bindings: RuntimeBindings): Value =
  ## Evaluate a checked definition with explicit host postulate bindings.
  let t = d.tmTm
  var fn = evalWithBindings(t, @[], bindings)
  for arg in args:
    fn = vAppWithBindings(fn, arg, bindings)
  fn

proc callDefValueWithBindings*(d: ElabDef, args: openArray[Value],
                               bindings: RuntimeBindings,
                               globals: Globals): Value =
  ## Binding-aware call with a named diagnostic when an unbound postulate
  ## leaves the result stuck at a neutral reference. A postulate that IS
  ## bound — even deliberately to a neutral value, as the #329 differential
  ## harness does — legitimately leaves a neutral-headed result, so the
  ## diagnostic only fires when the result's head is absent from `bindings`.
  result = callDefValueWithBindings(d, args, bindings)
  let refId = runtimeReferenceId(result)
  if refId >= 0 and refId notin bindings:
    for name, entry in globals.pairs:
      if not entry.tm.isNil and entry.tm.kind == tR and
          not entry.tm.refIsDefn and entry.tm.refId == refId and
          not entry.isDataConstructor:
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

proc defnValue*(baseDir, src: string, refId: int,
                bindings: RuntimeBindings): Value =
  ## Issue #329: interpreter-faithful value for a `tR` reference to a
  ## definition with no compiled proc in this block (an imported def, a
  ## synthetic def such as a record projection, or a block-local def outside
  ## the compilable fragment). Mirrors `evalWhnf`'s `tR`/defn case, resolving
  ## the definition by refId in the runtime globals: unlike the name-based
  ## `findDef`, this also resolves synthetic definitions that never appear
  ## in `allDefs` (e.g. `Pt.x`). Callers apply arguments themselves.
  if refId in bindings:
    let r = Term(kind: tR, refId: refId, refTyp: nil, refIsDefn: true,
                 refVal: nil)
    return Value(syn: r, whnf: bindings[refId].whnf)
  let g = getGlobalsDir(baseDir, src)
  for _, e in g.pairs:
    if e.tm != nil and e.tm.kind == tR and e.tm.refId == refId:
      let t = e.tm
      if not t.refIsDefn:
        return neutralRefValue(t, refId)
      if t.refVal.isNil:
        raise newException(ValueError,
          "codegen: no cached value for definition refId " & $refId)
      if bindings.len > 0 and t.refVal.whnf.kind != wRed:
        return evalWithBindings(t.refVal.syn, @[], bindings)
      return t.refVal
  raise newException(ValueError,
    "codegen: unknown definition refId " & $refId & " in " & src)

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
