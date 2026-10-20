## Runtime bridge checks for Eponym values that do not use the generated Int ABI.

import std/[os, tables, strutils, asyncdispatch, options]
import falsify
import eponym_mac
import eponym_embed
import elab
import eponym_init

const program = """
postulate Int : Type 0
proc double : Int -> Int = lam (n : Int). addInt n n
postulate Nat : Type 0
proc idNat : Nat -> Nat = lam (n : Nat). n
"""

proc hostStepNim(value: int): int = value + 7
proc hostTripleNim(value: int): int = value * 3
proc hostAddTwoNim(left, right: int): int = left + right
proc hostString(value: string): string = value
proc hostFailureNim(value: int): int =
  raise newException(IOError, "host adapter failed")
proc rawRuntimeIdentity(value: Value): Value = value
proc rawRuntimeWrongToken(value: Value): Value = intToValue(42)
proc rawRuntimeReturnLength(length, values: Value): Value = length
proc rawRuntimeBadHandle(args: seq[Value], globals: Globals): Value =
  intToValue(0)
var runtimeHandleDecodeCalls = 0
proc makeIndexedRuntimeValues(length: int): seq[int] =
  for i in 0 ..< length: result.add(i - length)
proc makeWrongIndexedRuntimeValues(length: int): seq[int] =
  newSeq[int](length + 1)
proc checkDependentVectorCallback(length: int, values: seq[int]): int =
  if values.len != length:
    raise newException(ValueError, "callback Vec length mismatch")
  length
proc runtimeTreePayloads(value: Value, globals: Globals): seq[int] =
  var current = value
  while true:
    let variant = valueToRuntimeVariant(current, globals, "RuntimeTree",
      ["treeEmpty", "treeNode"])
    if variant.constructor == "treeEmpty": return
    result.add(valueToInt(variant.arguments[0]))
    current = variant.arguments[1]

proc encodeRuntimeSizedTree(value: RuntimeStructuredVariant,
                           globals: Globals): Value =
  runtimeStructuredVariantToValue(value, globals, "SizedTree", ["sizedTree"])

proc decodeRuntimeSizedTree(value: Value,
                           globals: Globals): RuntimeStructuredVariant =
  valueToRuntimeStructuredVariant(value, globals, "SizedTree", ["sizedTree"])

proc runtimeIntVector(values: seq[int], globals: Globals): Value =
  let intType = runtimeGlobalValue(globals, "Int")
  result = callRuntimeValue(eval(globals["nil"].tm, @[]), [intType])
  for i in countdown(values.high, 0):
    result = callRuntimeValue(eval(globals["cons"].tm, @[]),
      [intType, natToValue(values.high - i, globals),
       intToValue(values[i]), result])

proc runtimeIntMatrix(values: seq[seq[int]], globals: Globals): Value =
  var rows: seq[Value] = @[]
  for row in values:
    rows.add(runtimeIntVector(row, globals))
  seqToVecValue[Value](rows, rows.len, globals, "Vec",
    proc(value: Value, globals: Globals): Value = value)

type ChannelHandle = object
  id: int
  label: string

proc rawRuntimeDropTypeWitness(args: seq[Value],
                               globals: Globals): Value =
  toHostValue(valueToHost[ChannelHandle](args[0]))

proc rawRuntimeChangeTypeWitness(args: seq[Value],
                                 globals: Globals): Value =
  let hostValue = valueToHost[ChannelHandle](args[0])
  toHostValueAtRuntimeType(hostValue,
    eval(globals["RuntimeOtherToken"].tm, @[]), globals)

type MutableCounter = ref object
  value: int

type ValueCounter = object
  value: int

proc incrementCounterNim(counter: var MutableCounter): MutableCounter =
  inc counter.value
  counter

proc inspectCounterNim(counter: MutableCounter): MutableCounter = counter

proc incrementValueCounterNim(counter: var ValueCounter): ValueCounter =
  inc counter.value
  counter

proc encodeRuntimeHandle(value: ChannelHandle, globals: Globals): Value =
  runtimeVariantToValue(RuntimeVariant(constructor: "runtimeHandle",
    arguments: @[intToValue(value.id)]), globals, "RuntimeHandle",
    ["runtimeHandle"])

proc decodeRuntimeHandle(value: Value, globals: Globals): ChannelHandle =
  let variant = valueToRuntimeVariant(value, globals, "RuntimeHandle",
    ["runtimeHandle"])
  let id = valueToInt(variant.arguments[0])
  ChannelHandle(id: id, label: "decoded-" & $id)

proc decodeRuntimeScalar(value: Value, globals: Globals): int =
  valueToHostAtRuntimeType[int](value,
    runtimeGlobalValue(globals, "RuntimeScalar"), globals)

proc hostRuntimeHandleAdapter(value: ChannelHandle): ChannelHandle =
  ChannelHandle(id: value.id + 1, label: value.label & "/adapter")

proc hostRuntimeHandleOptionAdapter(
    value: Option[ChannelHandle]): Option[ChannelHandle] = value

proc hostIntOptionIdentity(value: Option[int]): Option[int] = value

proc hostIndexedIntVectorIdentity(length: int,
    values: seq[int]): seq[int] = values

proc hostInvokeIndexedVectorCallback(length: int,
    callback: proc(index: int): seq[int] {.closure.}): seq[int] =
  callback(length)

proc hostInvokeFutureCallback(callback: proc(channel: ChannelHandle):
    Future[int] {.closure.}, channel: ChannelHandle): Future[int] =
  callback(channel)

proc hostAsyncChannelResult(channel: ChannelHandle): Future[int] {.async.} =
  return channel.id

proc hostInvokeVoidCallback(callback: proc(value: int) {.closure.},
                            value: int) = callback(value)
proc hostInvokeNullaryCallback(callback: proc(): int {.closure.}): int =
  callback()
proc hostInvokeRawNullaryCallback(
    callback: proc(): Value {.closure.}): int = valueToInt(callback())
proc hostMakeFourSigma(seed: int): tuple[a: int, b: int, c: int,
    flag: bool] = (seed, seed mod 101, -seed, (seed mod 2) == 0)

proc hostIncrementRuntimeHandles(length: int,
    values: seq[ChannelHandle]): seq[ChannelHandle] =
  result = values
  for value in result.mitems:
    inc value.id

proc decodedRuntimeHandles(values: openArray[ChannelHandle]):
    seq[ChannelHandle] =
  for value in values:
    result.add(ChannelHandle(id: value.id, label: "decoded-" & $value.id))

proc decodeTrackingRuntimeHandle(value: Value,
                                 globals: Globals): ChannelHandle =
  inc runtimeHandleDecodeCalls
  decodeRuntimeHandle(value, globals)

proc encodeWrongRuntimeHandle(value: ChannelHandle, globals: Globals): Value =
  intToValue(value.id)

type NimIntCallback = proc(value: int): int {.closure.}
type RawRuntimeCallback = proc(value: Value): Value {.closure.}
type RawIndexedRuntimeCallback = proc(length, values: Value): Value {.closure.}

type RuntimePoint = object
  x: int
  channel: ChannelHandle

type RuntimeEnvelope = object
  point: RuntimePoint
  note: string

type RuntimeCallbackRecord = object
  callback: NimIntCallback

type RuntimeSizedVec = object
  prefixLength: int
  suffixLength: int
  values: seq[int]

type RuntimeDependentPairEnvelope = object
  base: int
  payload: tuple[count: int, values: seq[int]]

type IndexedChannelHandle = object
  index: int
  label: string

type RuntimeSignal = enum
  signalStop, signalCaution, signalGo

type ImportedToken = enum
  importedTokenRed, importedTokenBlue

proc hostWrongFour(channel: ChannelHandle, message: string,
                   requestId, phase: int): int = channel.id + requestId + phase

proc hostRotateChannel(channel: ChannelHandle): ChannelHandle =
  result = channel
  inc result.id
  result.label.add("*")

proc hostSplitChannel(channel: ChannelHandle): tuple[count: int,
    remainder: ChannelHandle] =
  result.count = channel.id
  result.remainder = channel
  inc result.remainder.id
  result.remainder.label.add("/split")

proc hostSplitChannelWithNat(n: int, channel: ChannelHandle):
    tuple[count: int, remainder: ChannelHandle] =
  result.count = n + channel.id
  result.remainder = channel
  inc result.remainder.id
  result.remainder.label.add("/split-nat")

proc hostSplitChannelWithTwoNats(first, second: int, channel: ChannelHandle):
    tuple[count: int, remainder: ChannelHandle] =
  result.count = first + second + channel.id
  result.remainder = channel
  inc result.remainder.id
  result.remainder.label.add("/split-two")

proc hostRouteChannel(channel: ChannelHandle,
                      message: string): ChannelHandle =
  result = channel
  result.label.add(":" & message)

proc hostRouteChannelWithId(channel: ChannelHandle, message: string,
                            requestId: int): ChannelHandle =
  result = channel
  result.label.add(":" & message & "#" & $requestId)

proc hostRouteChannelWithPhase(channel: ChannelHandle, message: string,
                               requestId, phase: int): ChannelHandle =
  result = channel
  result.label.add(":" & message & "#" & $requestId & "/" & $phase)

proc hostRouteChannelWithSample(channel: ChannelHandle, message: string,
                                requestId, phase, sample: int): ChannelHandle =
  result = channel
  result.label.add(":" & message & "#" & $requestId & "/" & $phase &
    "/" & $sample)

proc hostFutureForChannel(channel: ChannelHandle): Future[int] =
  result = newFuture[int]("hostFutureForChannel")
  result.complete(channel.id)

proc hostFutureIdentity(value: Future[int]): Future[int] = value

proc hostInvokeCallback(callback: NimIntCallback, value: int): int =
  callback(value)

proc hostInvokeCheckedIntCallback(callback: NimIntCallback,
                                  value: int): int = callback(value)

proc hostWrongRoute(channel: int, message: string): int = channel + message.len

proc hostSumSix(a, b, c, d, e, f: int): int = a + b + c + d + e + f
proc hostBoolPredicateNim(value: int): bool =
  value mod 2 == 0

type TestIntArray = array[3, int]
type TestIntMatrixArray = array[3, array[2, int]]
type TestChannelArray = array[3, ChannelHandle]

static:
  doAssert compiles(hostIntUnary(hostStepNim))
  doAssert not compiles(hostIntUnary(hostString))
  doAssert compiles(hostOpaqueUnary[ChannelHandle](hostRotateChannel))
  doAssert not compiles(hostOpaqueUnary[ChannelHandle](hostString))
  doAssert compiles(hostOpaqueBinary[ChannelHandle, string, ChannelHandle](
    hostRouteChannel))
  doAssert not compiles(hostOpaqueBinary[ChannelHandle, string, ChannelHandle](
    hostWrongRoute))
  doAssert compiles(hostOpaqueTernary[ChannelHandle, string, int,
    ChannelHandle](hostRouteChannelWithId))
  doAssert compiles(hostOpaqueQuaternary[ChannelHandle, string, int, int,
    ChannelHandle](hostRouteChannelWithPhase))
  doAssert not compiles(hostOpaqueQuaternary[ChannelHandle, string, int, int,
    ChannelHandle](hostWrongFour))
  doAssert compiles(hostOpaqueMapUnary[ChannelHandle, Future[int]](
    hostFutureForChannel))
  doAssert compiles(hostOpaqueBinary[NimIntCallback, int, int](
    hostInvokeCallback))

eponymBlock:
  import "../lib/bool.ep"
  postulate(Int, Univ)
  postulate(Nat, Univ)
  postulate(IntIndexed, Int -> Univ)
  postulate(IntIndexedOneIdentity, IntIndexed[1] -> IntIndexed[1])
  postulate(hostBoolTick, Int -> Bool)
  bindPostulate(hostBoolTick, hostBoolPredicateNim, Int, Bool)
  postulate(hostPlusSeven, Int -> Int)
  bindPostulate(hostPlusSeven, hostStepNim)
  proc generatedCheckedRole(value: Int): Int = hostPlusSeven(value)
  proc generatedDefault(value: Int = 42): Int = value
  proc generatedDefaultThenValue(value: Int = 42,
      adjustment: Int): Int = addInt(value, adjustment)
  proc generatedNestedDefault(): Int = generatedDefault()
  proc generatedNamedDefaultGap(adjustment: Int): Int =
    generatedDefaultThenValue(adjustment = adjustment)
  proc generatedAdd(left: Int, right: Int): Int = addInt(left, right)
  proc generatedNamedAdd(left: Int, right: Int): Int =
    generatedAdd(right = right, left = left)
  proc generatedNamedCallback(
      callback: Pi(left: Int, Pi(right: Int, Int)),
      left: Int, right: Int): Int = callback(right = right, left = left)
  proc generatedNatId(value: Nat): Nat = value
  proc generatedBoolXor(left: Bool, right: Bool): Bool = left xor right
  proc generatedIntOne(): Int = 1
  proc generatedBoolXorWithNimCalls(): Bool =
    hostBoolTick(0) xor hostBoolTick(1)
  proc generatedSigmaId(value: Sig(Nat, Int)): Sig(Nat, Int) = value
  proc generatedArithmetic(left: Int, right: Int, scale: Int): Int =
    let difference = left - right
    let subtotal = difference + -right
    subtotal * scale
  proc generatedChooseTrue(): Int =
    if true: addInt(19, 0) else: addInt(17, 0)
  proc generatedChooseFalse(): Int =
    if false: addInt(19, 0) else: addInt(17, 0)
  runtimeValue(generatedAdd)

eponymBlock:
  import "fixtures/runtime_imported_value.ep"
  bindPostulate(importedStep, hostStepNim)
  runtimeValue(importedIdentity)
  runtimeValue(importedApply)
  proc namedImportedApply(value: Int): Int = importedApply(value = value)

eponymBlock:
  import "fixtures/runtime_imported_vec.ep"
  runtimeVector(Vec)
  runtimeValue(importedVectorIdentity)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  postulate(Channel, Univ)
  runtimeVectorArray(Vec)
  runtimeType(Channel, ChannelHandle)
  proc generatedTypeAwareSingleton[A: Univ](value: A): Vec[A, suc(zero)] =
    cons[A, zero](value, vecnil[A]())
  proc generatedArrayVecIdentity[n: Nat](values: Vec[Int, n]): Vec[Int, n] =
    values
  proc generatedArrayMatrixIdentity(
      values: Vec[Vec[Int, 2], 3]): Vec[Vec[Int, 2], 3] = values
  proc generatedChannelArrayIdentity[n: Nat](
      values: Vec[Channel, n]): Vec[Channel, n] = values
  proc generatedArrayVecCallback(
      callback: proc(values: Vec[Int, 3]): Vec[Int, 3] {.closure.},
      values: Vec[Int, 3]): Vec[Int, 3] = callback(values)
  runtimeValue(generatedArrayVecIdentity)
  runtimeValue(generatedTypeAwareSingleton)
  runtimeValue(generatedArrayMatrixIdentity)
  runtimeValue(generatedChannelArrayIdentity)

eponymBlock:
  import "fixtures/runtime_imported_option.ep"
  runtimeOption(Option)
  bindPostulate(useIntOption, hostIntOptionIdentity,
    Option[Int], Option[Int])
  proc importedOptionIdentity(value: Option[Int]): Option[Int] =
    useIntOption(value)
  runtimeValue(importedOptionIdentity)

eponymBlock:
  import "fixtures/runtime_imported_callback.ep"
  bindPostulate(applyCallback, hostInvokeCheckedIntCallback,
    proc(value: Int): Int {.closure.}, Int, Int)
  proc importedApplyCheckedIntCallback(
      callback: proc(value: Int): Int {.closure.}, value: Int): Int =
    applyCallback(callback, value)
  runtimeValue(importedApplyCheckedIntCallback)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  postulate(indexedIntVectorIdentity,
    Pi(length: Nat, values: Vec[Int, length], Vec[Int, length]))
  bindPostulate(indexedIntVectorIdentity, hostIndexedIntVectorIdentity,
    Nat, Vec[Int, length], Vec[Int, length])
  proc generatedIndexedIntVectorIdentity(length: Nat,
      values: Vec[Int, length]): Vec[Int, length] =
    indexedIntVectorIdentity(values)
  runtimeValue(generatedIndexedIntVectorIdentity)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  postulate(callIndexedVectorCallback,
    Pi(length: Nat,
       callback: proc(index: Nat): Vec[Int, length] {.closure.},
       Vec[Int, length]))
  bindPostulate(callIndexedVectorCallback, hostInvokeIndexedVectorCallback,
    Nat, proc(index: Nat): Vec[Int, length] {.closure.},
    Vec[Int, length])
  proc generatedApplyIndexedVectorCallback(length: Nat,
      callback: proc(index: Nat): Vec[Int, length] {.closure.}):
      Vec[Int, length] = callIndexedVectorCallback(callback)
  runtimeValue(generatedApplyIndexedVectorCallback)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  import "../lib/vec.ep"
  runtimeVector(Vec)
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  proc generatedCodecTypeAwareSingleton[A: Univ](value: A):
      Vec[A, suc(zero)] = cons[A, zero](value, vecnil[A]())
  runtimeValue(generatedCodecTypeAwareSingleton)
  postulate(indexedRuntimeHandleVectorAdapter,
    Pi(length: Nat, values: Vec[RuntimeHandle, length],
       Vec[RuntimeHandle, length]))
  bindPostulate(indexedRuntimeHandleVectorAdapter,
    hostIncrementRuntimeHandles, Nat, Vec[RuntimeHandle, length],
    Vec[RuntimeHandle, length])
  proc generatedIndexedRuntimeHandleVectorAdapter(length: Nat,
      values: Vec[RuntimeHandle, length]): Vec[RuntimeHandle, length] =
    indexedRuntimeHandleVectorAdapter(values)
  runtimeValue(generatedIndexedRuntimeHandleVectorAdapter)

eponymBlock:
  import "fixtures/runtime_imported_generic.ep"
  runtimeVector(Vec)
  runtimeOption(Option)
  runtimeType(Token, ImportedToken)
  runtimeType(RuntimeScalar, int)
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  runtimeValue(importedIntIdentity)
  runtimeValue(importedNullaryInt)
  runtimeValue(importedGenericIdentity)
  runtimeValue(importedGenericCallbackApply)
  runtimeValue(importedGenericDependentVectorCallbackApply)
  runtimeValue(importedGenericOptionCallbackApply)
  runtimeValue(importedGenericNestedOptionVectorCallbackApply)
  runtimeValue(importedGenericSigmaCallbackApply)
  runtimePairTrusted(importedGenericDependentPairCallbackApply)
  runtimeValue(importedGenericDependentPairCallbackApply)
  runtimeValue(importedGenericSingleton)
  runtimeValue(importedImplicitGenericIdentity)
  runtimeValue(importedImplicitNatVecIdentity)
  runtimeValue(importedImplicitBoolIdentity)
  runtimeValue(importedImplicitIntIdentity)
  runtimeValue(importedImplicitTokenIdentity)

  runtimeValue(importedCallbackApply)
  runtimeValue(importedCallbackApply2)
  runtimeValue(importedCallbackIdentity)
  runtimeValue(applyNullaryCallback)
  runtimeValue(nullaryCallbackIdentity)
  runtimeValue(importedDependentCallbackApply)
  runtimePairTrusted(importedDependentPairIdentity)
  runtimeValue(importedDependentPairIdentity)

eponymBlock:
  import "fixtures/runtime_imported_generic_list.ep"
  runtimeList(List)
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  runtimeValue(importedGenericListCallbackApply)

eponymBlock:
  import "fixtures/runtime_imported_generic_variant.ep"
  runtimeDataVariant(RuntimeBox)
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  runtimeValue(importedGenericBoxCallbackApply)

eponymBlock:
  import "fixtures/runtime_imported_generic_variant.ep"
  runtimeDataVariant(SizedTree)
  runtimeValue(importedGenericIndexedVariantCallbackApply)

eponymBlock:
  import "fixtures/runtime_imported_generic.ep"
  runtimeOption(Option)
  runtimeDataVariant(SizedTree)
  runtimeValue(importedGenericIndexedOptionCallbackApply)
  runtimeValue(importedGenericIndexedNestedOptionCallbackApply)
  runtimeValue(importedGenericIndexedSigmaCallbackApply)

eponymBlock:
  import "fixtures/runtime_imported_generic.ep"
  runtimeVector(Vec)
  runtimeOption(Option)
  runtimeDataVariant(SizedTree)
  runtimeValue(importedGenericIndexedNestedOptionVectorCallbackApply)
  runtimeValue(importedGenericIndexedEmptyOptionVectorCallbackApply)
  runtimeValue(importedGenericIndexedVectorCallbackApply)
  runtimeValue(importedGenericIndexedEmptyVectorCallbackApply)

eponymBlock:
  import "fixtures/runtime_imported_generic_list.ep"
  runtimeList(List)
  runtimeOption(Option)
  runtimeDataVariant(SizedTree)
  runtimeValue(importedGenericIndexedListCallbackApply)
  runtimeValue(importedGenericIndexedOptionListCallbackApply)

eponymBlock:
  import "fixtures/runtime_imported_generic_variant.ep"
  runtimeCodec(SizedTree, RuntimeStructuredVariant, encodeRuntimeSizedTree,
    decodeRuntimeSizedTree)
  runtimeValue(importedGenericIndexedCodecCallbackApply)

eponymBlock:
  import "fixtures/runtime_imported_generic_array.ep"
  runtimeVectorArray(Vec)
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  runtimeValue(importedGenericArrayCallbackApply)

eponymBlock:
  postulate(Counter, Univ)
  postulate(incrementCounter, Counter -> Counter)
  postulate(inspectCounter, Counter -> Counter)
  runtimeType(Counter, MutableCounter)
  bindPostulate(incrementCounter, incrementCounterNim, Counter)
  bindPostulate(inspectCounter, inspectCounterNim, Counter)
  proc incrementChecked(counter: Counter): Counter =
    incrementCounter(counter)
  proc inspectChecked(counter: Counter): Counter = inspectCounter(counter)
  runtimeValue(incrementChecked)
  runtimeValue(inspectChecked)

eponymBlock:
  postulate(ValueCounterType, Univ)
  postulate(incrementValueCounter, ValueCounterType -> ValueCounterType)
  runtimeType(ValueCounterType, ValueCounter)
  bindPostulate(incrementValueCounter, incrementValueCounterNim,
    ValueCounterType)
  proc incrementValueCounterChecked(counter: ValueCounterType):
      ValueCounterType = incrementValueCounter(counter)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  import "../lib/option.ep"
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  postulate(runtimeHandleAdapter, RuntimeHandle -> RuntimeHandle)
  bindPostulate(runtimeHandleAdapter, hostRuntimeHandleAdapter,
    RuntimeHandle, RuntimeHandle)
  proc generatedRuntimeHandleAdapter(value: RuntimeHandle): RuntimeHandle =
    runtimeHandleAdapter(value)
  runtimeValue(generatedRuntimeHandleAdapter)
  runtimeOption(Option)
  postulate(runtimeHandleOptionAdapter,
    Option[RuntimeHandle] -> Option[RuntimeHandle])
  bindPostulate(runtimeHandleOptionAdapter, hostRuntimeHandleOptionAdapter,
    Option[RuntimeHandle], Option[RuntimeHandle])
  proc generatedRuntimeHandleOptionAdapter(
      value: Option[RuntimeHandle]): Option[RuntimeHandle] =
    runtimeHandleOptionAdapter(value)
  runtimeValue(generatedRuntimeHandleOptionAdapter)
  runtimeType(RuntimeOpaqueToken, ChannelHandle)
  runtimeType(RuntimeOtherToken, ChannelHandle)
  runtimeType(RuntimeIndexedToken, ChannelHandle)
  runtimeDataVariant(RuntimeTree)
  runtimeDataVariant(SizedTree)
  runtimeDataVariant(IndexedEnvelope)
  runtimeDataVariant(DecisionTree)
  runtimeDataVariant(HandleEnvelope)
  runtimeValue(treeIdentity)
  runtimeValue(decisionIdentity)
  runtimeValue(handleEnvelopeIdentity)
  proc generatedRuntimeHandleOptionIdentity(
      value: Option[RuntimeHandle]): Option[RuntimeHandle] = value
  runtimeValue(generatedRuntimeHandleOptionIdentity)
  proc generatedGenericRuntimeValueIdentity[A: Univ](value: A): A = value
  runtimeValue(generatedGenericRuntimeValueIdentity)
  proc generatedSizedTreeRawIdentity(length: Nat,
      tree: SizedTree[length]): SizedTree[length] = tree
  runtimeValue(generatedSizedTreeRawIdentity)
  proc genericIndexedTreeProjection[length: Nat,
      tree: SizedTree[length]](ignored: Int): SizedTree[length] = tree
  runtimeValue(genericIndexedTreeProjection)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  import "../lib/vec.ep"
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  runtimeVector(Vec)
  proc generatedRuntimeHandleVectorIdentity(length: Nat,
      values: Vec[RuntimeHandle, length]): Vec[RuntimeHandle, length] = values
  runtimeValue(generatedRuntimeHandleVectorIdentity)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  import "../lib/list.ep"
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  runtimeList(List)
  proc generatedRuntimeHandleListIdentity(
      values: List[RuntimeHandle]): List[RuntimeHandle] = values
  runtimeValue(generatedRuntimeHandleListIdentity)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  proc genericUnmappedSizedTreeProjection[length: Nat,
      tree: SizedTree[length]](ignored: Int): SizedTree[length] = tree
  runtimeValue(genericUnmappedSizedTreeProjection)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeWrongRuntimeHandle,
    decodeRuntimeHandle)
  proc runtimeHandleConstant(value: RuntimeHandle): RuntimeHandle =
    runtimeHandle(0)
  runtimeValue(runtimeHandleConstant)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeTrackingRuntimeHandle)
  postulate(malformedRuntimeHandle, RuntimeHandle -> RuntimeHandle)
  bindPostulateValue(malformedRuntimeHandle, rawRuntimeBadHandle)
  proc checkedMalformedRuntimeHandle(value: RuntimeHandle): RuntimeHandle =
    malformedRuntimeHandle(value)
  runtimeValue(checkedMalformedRuntimeHandle)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  runtimeType(RuntimeOpaqueToken, ChannelHandle)
  runtimeType(RuntimeOtherToken, ChannelHandle)
  postulate(dropOpaqueTypeWitness,
    RuntimeOpaqueToken -> RuntimeOpaqueToken)
  bindPostulateValue(dropOpaqueTypeWitness, rawRuntimeDropTypeWitness)
  proc checkedOpaqueTypeWitness(value: RuntimeOpaqueToken):
      RuntimeOpaqueToken = dropOpaqueTypeWitness(value)
  postulate(changeOpaqueTypeWitness,
    RuntimeOpaqueToken -> RuntimeOpaqueToken)
  bindPostulateValue(changeOpaqueTypeWitness, rawRuntimeChangeTypeWitness)
  proc checkedOpaqueTypeWitnessType(value: RuntimeOpaqueToken):
      RuntimeOpaqueToken = changeOpaqueTypeWitness(value)

eponymBlock:
  postulate(Int, Univ)
  data(RuntimeToken, Univ):
    proc runtimeTokenValue(): RuntimeToken
  proc makeRuntimeToken(): RuntimeToken = runtimeTokenValue()
  runtimeValue(makeRuntimeToken)
  proc genericRuntimeTokenProjection[token: RuntimeToken](ignored: Int):
      RuntimeToken = token
  runtimeValue(genericRuntimeTokenProjection)

eponymBlock:
  postulate(Nat, Univ)
  data(Tree, Univ):
    proc leaf(): Tree
    proc node(n: Nat, rest: Tree): Tree
  proc sampleTree(): Tree = node(37, leaf())
  proc sampleTreeWith(n: Nat): Tree = node(n, leaf())
  runtimeValue(sampleTree)
  runtimeValue(sampleTreeWith)

eponymBlock:
  postulate(Int, Univ)
  postulate(hostPlusSeven, Int -> Int)
  bindPostulate(hostPlusSeven, hostStepNim)
  proc runtimeResult(): Int = hostPlusSeven(35)
  runtimeValue(runtimeResult)

eponymBlock:
  import "../lib/bool.ep"
  proc generatedBoolNot(value: Bool): Bool =
    not value

eponymBlock:
  import "../lib/nat.ep"
  def(generatedClauseNatIdentity, Nat -> Nat):
    clause([zero], zero)
    clause([suc(n)], suc(n))

eponymBlock:
  proc generatedGenericIdentity[A: Univ](value: A): A = value
  runtimeValue(generatedGenericIdentity)

eponymBlock:
  import "../lib/nat.ep"
  postulate(Int, Univ)
  postulate(Channel, Nat -> Univ)
  runtimeType(Channel, IndexedChannelHandle)
  proc generatedGenericIndexedChannelIdentity[n: Nat](
      channel: Channel[n]): Channel[n] = channel
  runtimeValue(generatedGenericIndexedChannelIdentity)
  proc generatedGenericNatValue[n: Nat](ignored: Int): Nat = n
  runtimeValue(generatedGenericNatValue)

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/bool.ep"
  postulate(Int, Univ)
  postulate(makeFourSigma,
    Int -> Sig(a: Int, Sig(b: Nat, Sig(c: Int, Bool))))
  bindPostulate(makeFourSigma, hostMakeFourSigma, Int,
    Sig(a: Int, Sig(b: Nat, Sig(c: Int, Bool))))
  proc generatedMakeFourSigma(seed: Int):
      Sig(a: Int, Sig(b: Nat, Sig(c: Int, Bool))) = makeFourSigma(seed)
  runtimeValue(generatedMakeFourSigma)
  proc generatedFourFieldSigmaIdentity(
      value: Sig(a: Int, Sig(b: Nat, Sig(c: Int, Bool)))):
      Sig(a: Int, Sig(b: Nat, Sig(c: Int, Bool))) = value
  runtimeValue(generatedFourFieldSigmaIdentity)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  proc generatedVectorIdentity[A: Univ, n: Nat](
      values: Vec[A, n]): Vec[A, n] = values
  proc generatedVectorSucIndex[n: Nat](
      values: Vec[Int, suc(n)]): Nat = n
  proc generatedVectorAddIndex[m, n: Nat](
      values: Vec[Int, add(m, n)]): Int = addInt(0, 0)
  proc generatedNestedVectorIdentity[m, n: Nat](
      values: Vec[Vec[Int, m], n]): Vec[Vec[Int, m], n] = values
  runtimeValue(generatedNestedVectorIdentity)
  proc generatedDependentPairVecIdentity(
      value: Sig(length: Nat, Sig(marker: Int, Vec[Int, length]))):
      Sig(length: Nat, Sig(marker: Int, Vec[Int, length])) = value
  runtimePairTrusted(generatedDependentPairVecIdentity)
  runtimeValue(generatedDependentPairVecIdentity)
  proc generatedShadowedDependentPairVecIdentity(
      value: Sig(length: Nat, Sig(length: Nat, Vec[Int, length]))):
      Sig(length: Nat, Sig(length: Nat, Vec[Int, length])) = value
  runtimePairTrusted(generatedShadowedDependentPairVecIdentity)
  record(SizedVec):
    field(prefixLength, Nat)
    field(suffixLength, Nat)
    field(values, Vec[Int, add(prefixLength, suffixLength)])
  runtimeType(SizedVec, RuntimeSizedVec)
  runtimeRecordTrusted(SizedVec)
  proc generatedSizedVecIdentity(value: SizedVec): SizedVec = value
  runtimeValue(generatedSizedVecIdentity)

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  record(DependentPairEnvelope):
    field(base, Nat)
    field(payload, Sig(count: Nat, Vec[Int, add(base, count)]))
  runtimeType(DependentPairEnvelope, RuntimeDependentPairEnvelope)
  runtimeRecordTrusted(DependentPairEnvelope)
  proc generatedDependentPairEnvelopeIdentity(
      value: DependentPairEnvelope): DependentPairEnvelope = value

eponymBlock:
  import "../lib/list.ep"
  postulate(Int, Univ)
  runtimeList(List)
  proc generatedIntListIdentity(values: List[Int]): List[Int] = values
  runtimeValue(generatedIntListIdentity)
  proc generatedListIdentity[A: Univ](values: List[A]): List[A] = values
  runtimeValue(generatedListIdentity)

eponymBlock:
  import "../lib/option.ep"
  postulate(Int, Univ)
  runtimeOption(Option)
  proc generatedPrimitiveOptionIdentity(value: Option[Int]): Option[Int] = value
  runtimeValue(generatedPrimitiveOptionIdentity)
  proc generatedNestedOptionIdentity(
      value: Option[Option[Int]]): Option[Option[Int]] = value
  proc generatedOptionIdentity[A: Univ](value: Option[A]): Option[A] = value
  runtimeValue(generatedOptionIdentity)

eponymBlock:
  import "../lib/bool.ep"
  postulate(Int, Univ)
  proc generatedGenericBoolValue[b: Bool](ignored: Int): Bool = b
  runtimeValue(generatedGenericBoolValue)
  proc generatedGenericIntValue[index: Int](ignored: Int): Int = index
  runtimeValue(generatedGenericIntValue)

eponymBlock:
  postulate(Int, Univ)
  postulate(Channel, Univ)
  runtimeType(Channel, ChannelHandle)
  proc generatedGenericChannelValue[channel: Channel](ignored: Int):
      Channel = channel
  runtimeValue(generatedGenericChannelValue)

eponymBlock:
  postulate(Int, Univ)
  proc generatedRuntimeIncrementValue(): proc(value: Int): Int {.closure.} =
    lam(value, Int, addInt(value, 1))
  proc generatedApplyGenericFunction[callback: Int -> Int](value: Int): Int =
    callback(value)
  runtimeValue(generatedRuntimeIncrementValue)
  runtimeValue(generatedApplyGenericFunction)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  proc generatedDependentTypeAnchor(): Univ = Int
  proc generatedApplyDependentVectorFunction[
      callback: Pi(n: Nat, Vec[Int, n])](length: Nat): Vec[Int, length] =
    callback(length)
  proc generatedApplyComputedVectorFunction[
      callback: Pi(n: Nat, Vec[Int, add(n, 1)])](length: Nat):
      Vec[Int, add(length, 1)] = callback(length)
  proc generatedApplyTwoIndexVectorFunction[
      callback: Pi(left: Nat, right: Nat, Vec[Int, add(left, right)])](
      left, right: Nat): Vec[Int, add(left, right)] = callback(left, right)
  proc generatedApplyGenericBinaryFunction[
      callback: Pi(x: Int, y: Int, Int)](x: Int, y: Int): Int =
    callback(x, y)
  runtimeValue(generatedDependentTypeAnchor)
  runtimeValue(generatedApplyDependentVectorFunction)
  runtimeValue(generatedApplyComputedVectorFunction)
  runtimeValue(generatedApplyTwoIndexVectorFunction)
  runtimeValue(generatedApplyGenericBinaryFunction)

eponymBlock:
  postulate(Nat, Univ)
  proc generatedGenericNatProjection[n: Nat](): Nat = n
  runtimeValue(generatedGenericNatProjection)

proc rawGenericNatAt(index: int): bool =
  let runtime = generatedGenericNatProjectionRuntimeValueRaw(
    [vNatLit(index)], [])
  let dynamicRuntime = generatedGenericNatProjectionRuntimeValueDynamic(index)
  valueToNat(runtime.value, runtime.globals) == index and
    valueToNat(dynamicRuntime.value, dynamicRuntime.globals) == index and
    generatedGenericNatProjectionDynamic(index) == index

proc checkGenericChannelValueAt[channel: static[ChannelHandle]](
    ignored: int): bool =
  let typedResult = generatedGenericChannelValue[channel](ignored)
  let runtime = generatedGenericChannelValueRuntimeValue[channel](ignored)
  let rawRuntime = generatedGenericChannelValueRuntimeValue[channel](
    [intToValue(ignored)])
  typedResult == channel and
    generatedGenericChannelValueDynamic(channel, ignored) == channel and
    valueToHost[ChannelHandle](runtime.value) == channel and
    valueToHost[ChannelHandle](rawRuntime.value) == channel

proc checkGenericIntValueAt[index: static[int]](ignored: int): bool =
  let typedResult = generatedGenericIntValue[index](ignored)
  let runtime = generatedGenericIntValueRuntimeValue[index](ignored)
  let rawRuntime = generatedGenericIntValueRuntimeValue[index](
    [intToValue(ignored)])
  var wrongRawArgumentRejected = false
  try:
    discard generatedGenericIntValueRuntimeValue[index]([natToValue(ignored)])
  except ValueError:
    wrongRawArgumentRejected = true
  typedResult == index and valueToInt(runtime.value) == index and
    valueToInt(rawRuntime.value) == index and
    generatedGenericIntValueDynamic(index, ignored) == index and
    wrongRawArgumentRejected

proc decodeRuntimeIntVector(value: Value, length: int,
                            globals: Globals): seq[int] =
  vecValueToSeq[int](value, length, globals, "Vec",
    proc(item: Value, _: Globals): int = valueToInt(item))

proc decodeRuntimeIntMatrix(value: Value, rows: int,
                            globals: Globals): seq[seq[int]] =
  vecValueToSeq[seq[int]](value, rows, globals, "Vec",
    proc(row: Value, nestedGlobals: Globals): seq[int] =
      decodeRuntimeIntVector(row, 2, nestedGlobals))

proc decodeRuntimeIntList(value: Value, globals: Globals): seq[int] =
  listValueToSeq[int](value, globals, "List",
    proc(item: Value, _: Globals): int = valueToInt(item))

proc decodeRuntimeHostList[T](value: Value,
                              globals: Globals): seq[T] =
  listValueToSeq[T](value, globals, "List",
    proc(item: Value, _: Globals): T = valueToHost[T](item))

proc decodeRuntimeChannelList(value: Value,
                              globals: Globals): seq[ChannelHandle] =
  decodeRuntimeHostList[ChannelHandle](value, globals)

proc encodeRuntimeTree(values: seq[int], globals: Globals): Value =
  result = eval(globals["treeEmpty"].tm, @[])
  for i in countdown(values.high, 0):
    result = callRuntimeValue(eval(globals["treeNode"].tm, @[]),
      @[intToValue(values[i]), result])

proc decodeRuntimeTree(value: Value, globals: Globals): seq[int] =
  let emptyId = globals["treeEmpty"].tm.refId
  let nodeId = globals["treeNode"].tm.refId
  var current = value
  while true:
    if current.whnfKind != wRef:
      raise newException(ValueError, "runtime value is not a Tree")
    if current.whnfRefId == emptyId:
      if current.whnfSpineLen != 0:
        raise newException(ValueError,
          "Tree empty constructor has invalid spine")
      return
    if current.whnfRefId != nodeId or current.whnfSpineLen != 2 or
        current.whnfSpineKind(0) != eApp or
        current.whnfSpineKind(1) != eApp:
      raise newException(ValueError, "runtime value is not a Tree")
    result.add(valueToInt(current.whnfSpineArg(0)))
    current = current.whnfSpineArg(1)

proc reverseRuntimeTree(values: seq[int]): seq[int] =
  for i in countdown(values.high, 0):
    result.add(values[i])

eponymBlock:
  postulate(Int, Univ)
  data(Tree, Univ):
    proc treeEmpty(): Tree
    proc treeNode(value: Int, tail: Tree): Tree
  runtimeCodec(Tree, seq[int], encodeRuntimeTree, decodeRuntimeTree)
  postulate(treeReverse, Tree -> Tree)
  bindPostulate(treeReverse, reverseRuntimeTree, Tree)
  proc generatedTreeIdentity(value: Tree): Tree = value
  runtimeValue(generatedTreeIdentity)
  proc generatedBoundTreeReverse(value: Tree): Tree = treeReverse(value)

eponymBlock:
  postulate(Int, Univ)
  proc generatedApplyNimCallback(
      callback: proc(value: Int): Int {.closure.}, value: Int): Int =
    callback(value)
  proc generatedAdder(seed: Int): proc(value: Int): Int {.closure.} =
    lam(value, Int, addInt(seed, value))
  proc generatedApplyTwoArgumentCallback(
      callback: proc(left, right: Int): Int {.closure.},
      left, right: Int): Int = callback(left, right)
  proc generatedTwoArgumentAdder(seed: Int):
      proc(left, right: Int): Int {.closure.} =
    lam(left, Int, lam(right, Int, addInt(seed, addInt(left, right))))

eponymBlock:
  data(Token, Univ):
    proc runtimeTokenRed(): Token
    proc runtimeTokenBlue(): Token
  runtimeVariant(Token)
  proc generatedRawTokenCallbackEcho(
      callback: proc(value: Token): Token {.closure, rawValue.}):
      proc(value: Token): Token {.closure, rawValue.} = callback
  runtimeValue(generatedRawTokenCallbackEcho)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  proc generatedApplyIndexedCallback(
      callback: proc(length: Nat): Vec[Int, length] {.closure.},
      length: Nat): Vec[Int, length] =
    let selected = callback
    selected()
  runtimeValue(generatedApplyIndexedCallback)
  proc generatedApplyTrailingIndexedCallback(
      callback: proc(seed: Int, length: Nat): Vec[Int, length] {.closure.},
      seed: Int, length: Nat): Vec[Int, length] =
    let selected = callback
    selected(seed)
  runtimeValue(generatedApplyTrailingIndexedCallback)
  proc generatedApplyDependentVectorCallback(
      callback: proc(length: Nat, values: Vec[Int, length]): Nat {.closure.},
      length: Nat, values: Vec[Int, length]): Nat = callback(values)
  proc generatedDependentVectorCallback():
      proc(length: Nat, values: Vec[Int, length]): Nat {.closure.} =
    lam(length, Nat, lam(values, Vec[Int, length], length))
  runtimeValue(generatedApplyDependentVectorCallback)
  runtimeValue(generatedDependentVectorCallback)
  proc generatedRawIndexedCallbackEcho(
      callback: proc(length: Nat, values: Vec[Int, length]): Nat
        {.closure, rawValue.}):
      proc(length: Nat, values: Vec[Int, length]): Nat
        {.closure, rawValue.} = callback
  runtimeValue(generatedRawIndexedCallbackEcho)

eponymBlock:
  postulate(Int, Univ)
  postulate(applyCheckedIntCallback,
    Pi(callback: proc(value: Int): Int {.closure.}, value: Int, Int))
  bindPostulate(applyCheckedIntCallback, hostInvokeCheckedIntCallback,
    proc(value: Int): Int {.closure.}, Int, Int)
  proc generatedApplyCheckedIntCallback(
      callback: proc(value: Int): Int {.closure.}, value: Int): Int =
    applyCheckedIntCallback(callback, value)
  runtimeValue(generatedApplyCheckedIntCallback)

eponymBlock:
  postulate(Channel, Univ)
  postulate(PendingResult, Univ)
  runtimeType(Channel, ChannelHandle)
  runtimeType(PendingResult, Future[int])
  postulate(invokeFutureCallback,
    Pi(callback: proc(channel: Channel): PendingResult {.closure.},
       channel: Channel, PendingResult))
  bindPostulate(invokeFutureCallback, hostInvokeFutureCallback,
    proc(channel: Channel): PendingResult {.closure.}, Channel, PendingResult)
  proc generatedInvokeFutureCallback(
      callback: proc(channel: Channel): PendingResult {.closure.},
      channel: Channel): PendingResult = invokeFutureCallback(callback, channel)
  runtimeValue(generatedInvokeFutureCallback)
  proc generatedApplyGenericFutureCallback[
      callback: Pi(channel: Channel, PendingResult)](
      channel: Channel): PendingResult = callback(channel)
  runtimeValue(generatedApplyGenericFutureCallback)

eponymBlock:
  postulate(Int, Univ)
  postulate(invokeVoidCallback,
    Pi(callback: proc(value: Int) {.closure.}, value: Int, unitTy))
  bindPostulate(invokeVoidCallback, hostInvokeVoidCallback,
    proc(value: Int) {.closure.}, Int, unitTy)
  proc generatedInvokeVoidCallback(callback: proc(value: Int) {.closure.},
                                   value: Int): unitTy =
    invokeVoidCallback(callback, value)
  runtimeValue(generatedInvokeVoidCallback)
eponymBlock:
  postulate(Int, Univ)
  postulate(invokeNullaryCallback,
    Pi(callback: proc(): Int {.closure.}, Int))
  bindPostulate(invokeNullaryCallback, hostInvokeNullaryCallback,
    proc(): Int {.closure.}, Int)
  proc generatedInvokeNullaryCallback(
      callback: proc(): Int {.closure.}): Int =
    invokeNullaryCallback(callback)
  runtimeValue(generatedInvokeNullaryCallback)
  proc generatedReturnNullaryInt(): proc(): Int {.closure.} =
    lam(unit, unitTy, addInt(17, 0))
  runtimeValue(generatedReturnNullaryInt)
  postulate(invokeRawNullaryCallback,
    Pi(callback: proc(): Int {.closure, rawValue.}, Int))
  bindPostulate(invokeRawNullaryCallback, hostInvokeRawNullaryCallback,
    proc(): Int {.closure, rawValue.}, Int)
  proc generatedInvokeRawNullaryCallback(
      callback: proc(): Int {.closure, rawValue.}): Int =
    invokeRawNullaryCallback(callback)
  runtimeValue(generatedInvokeRawNullaryCallback)

eponymBlock:
  postulate(Int, Univ)
  postulate(sumSix, Int -> Int -> Int -> Int -> Int -> Int -> Int)
  bindPostulate(sumSix, hostSumSix, Int, Int, Int, Int, Int, Int, Int)
  proc generatedSumSix(a, b, c, d, e, f: Int): Int =
    sumSix(a, b, c, d, e, f)

eponymBlock:
  postulate(Int, Univ)
  data(Signal, Univ):
    proc signalStop(): Signal
    proc signalCaution(): Signal
    proc signalGo(): Signal
  runtimeType(Signal, RuntimeSignal)
  proc generatedSignalIdentity(value: Signal): Signal = value
  proc generatedGenericSignalValue[signal: Signal](ignored: Int): Signal =
    signal
  runtimeValue(generatedGenericSignalValue)

proc checkGenericSignalValueAt[signal: static[RuntimeSignal]](
    ignored: int): bool =
  let typedResult = generatedGenericSignalValue[signal](ignored)
  let runtime = generatedGenericSignalValueRuntimeValue[signal](ignored)
  let rawRuntime = generatedGenericSignalValueRuntimeValue[signal](
    [intToValue(ignored)])
  let names = @["signalStop", "signalCaution", "signalGo"]
  typedResult == signal and
    valueToEnum[RuntimeSignal](runtime.value, runtime.globals, names) == signal and
    valueToEnum[RuntimeSignal](rawRuntime.value, rawRuntime.globals, names) == signal

static:
  doAssert compiles(sampleTreeWithRuntimeValue(2))
  doAssert not compiles(sampleTreeWithRuntimeValue("not a Nat"))
  doAssert compiles(generatedBoolNot(true))
  doAssert not compiles(generatedBoolNot(1))
  doAssert compiles(generatedGenericIdentity(1))
  doAssert compiles(generatedGenericIdentity("opaque"))
  doAssert compiles(generatedGenericIndexedChannelIdentity[17](
    IndexedChannelHandle(index: 3, label: "generic-index")))
  doAssert compiles(generatedGenericIndexedChannelIdentityRuntimeValue[17](
    IndexedChannelHandle(index: 3, label: "generic-index")))
  doAssert compiles(generatedGenericNatValue[17](3))
  doAssert compiles(generatedGenericNatValueRuntimeValue[17](3))
  doAssert compiles(generatedVectorIdentity[int, 4](@[1, 2, 3, 4]))
  doAssert compiles(generatedVectorSucIndex[3](@[1, 2, 3, 4]))
  doAssert compiles(generatedVectorAddIndex[2, 3](@[1, 2, 3, 4, 5]))
  doAssert compiles(generatedNestedVectorIdentity[2, 3](
    @[@[1, 2], @[3, 4], @[5, 6]]))
  doAssert compiles(generatedSizedVecIdentity(
    RuntimeSizedVec(prefixLength: 1, suffixLength: 1, values: @[7, 8])))
  doAssert compiles(generatedListIdentity[int](@[1, 2, 3]))
  doAssert compiles(generatedListIdentity[ChannelHandle](@[
    ChannelHandle(id: 2, label: "list")]))
  doAssert compiles(generatedGenericBoolValue[true](1))
  doAssert compiles(generatedGenericBoolValue[false](1))
  doAssert compiles(generatedGenericBoolValueRuntimeValue[true](1))
  doAssert compiles(generatedGenericIntValue[-17](1))
  doAssert compiles(generatedGenericIntValueRuntimeValue[-17](1))
  doAssert compiles(generatedGenericChannelValue[
    ChannelHandle(id: 7, label: "generic")](1))
  doAssert not compiles(generatedGenericChannelValue[17](1))
  doAssert compiles(generatedTypeAwareSingleton(
    ChannelHandle(id: 8, label: "type-witness")))
  doAssert not compiles(generatedTypeAwareSingleton(8))
  doAssert compiles(generatedApplyNimCallback(proc(value: int): int = value, 1))
  doAssert not compiles(generatedApplyNimCallback(
    proc(value: string): string = value, 1))
  doAssert compiles(importedGenericCallbackApply(
    proc(value: ImportedToken): ImportedToken = value, importedTokenRed))
  doAssert not compiles(importedGenericCallbackApply(hostStepNim,
    importedTokenRed))
  doAssert compiles(generatedAdder(3)(4))
  doAssert compiles(generatedApplyTwoArgumentCallback(
    proc(left, right: int): int = left + right, 1, 2))
  doAssert compiles(generatedTwoArgumentAdder(3)(4, 5))
  doAssert compiles(generatedSumSix(1, 2, 3, 4, 5, 6))
  doAssert not compiles(generatedSumSix(1, 2, 3, 4, 5))
  doAssert compiles(generatedSignalIdentity(signalGo))
  doAssert not compiles(generatedSignalIdentity(1))
  doAssert compiles(generatedGenericSignalValue[signalGo](1))

eponymBlock:
  postulate(Int, Univ)
  postulate(hostFailure, Int -> Int)
  bindPostulate(hostFailure, hostFailureNim)
  proc generatedFailureRole(value: Int): Int = hostFailure(value)

eponymBlock:
  postulate(Int, Univ)
  record(CallbackRecord):
    field(callback, Int -> Int)
  runtimeType(CallbackRecord, RuntimeCallbackRecord)
  proc generatedApplyRecordCallback(box: CallbackRecord,
                                   value: Int): Int =
    box.callback(value)
  runtimeValue(generatedApplyRecordCallback)

eponymBlock:
  postulate(Nat, Univ)
  postulate(Channel, Univ)
  postulate(Message, Univ)
  postulate(RequestId, Univ)
  postulate(Phase, Univ)
  postulate(PendingResult, Univ)
  postulate(Callback, Univ)
  postulate(Sample, Univ)
  runtimeType(Channel, ChannelHandle)
  runtimeType(Message, string)
  runtimeType(RequestId, int)
  runtimeType(Phase, int)
  runtimeType(PendingResult, Future[int])
  runtimeType(Callback, NimIntCallback)
  runtimeType(Sample, int)
  postulate(splitChannel, Channel -> Sig(Nat, Channel))
  bindPostulatePair(splitChannel, hostSplitChannel, Channel, Nat, Channel)
  proc generatedSplitChannel(channel: Channel): Sig(Nat, Channel) =
    splitChannel(channel)
  postulate(splitChannelWithNat,
    Nat -> Channel -> Sig(Nat, Channel))
  bindPostulatePair(splitChannelWithNat, hostSplitChannelWithNat,
    Nat, Channel, Nat, Channel)
  proc generatedSplitChannelWithNat(n: Nat, channel: Channel):
      Sig(Nat, Channel) = splitChannelWithNat(n, channel)
  postulate(splitChannelWithTwoNats,
    Nat -> Nat -> Channel -> Sig(Nat, Channel))
  bindPostulatePair(splitChannelWithTwoNats, hostSplitChannelWithTwoNats,
    Nat, Nat, Channel, Nat, Channel)
  proc generatedSplitChannelWithTwoNats(first, second: Nat,
      channel: Channel): Sig(Nat, Channel) =
    splitChannelWithTwoNats(first, second, channel)
  record(Point):
    field(x, Nat)
    field(channel, Channel)
  runtimeType(Point, RuntimePoint)
  proc generatedPointId(value: Point): Point = value
  runtimeValue(generatedPointId)
  record(Envelope):
    field(point, Point)
    field(note, Message)
  runtimeType(Envelope, RuntimeEnvelope)
  proc generatedEnvelopeId(value: Envelope): Envelope = value
  postulate(rotateChannel, Channel -> Channel)
  bindPostulate(rotateChannel, hostRotateChannel, Channel)
  postulate(routeChannel, Channel -> Message -> Channel)
  bindPostulate(routeChannel, hostRouteChannel, Channel, Message, Channel)
  postulate(routeChannelWithId,
    Channel -> Message -> RequestId -> Channel)
  bindPostulate(routeChannelWithId, hostRouteChannelWithId,
    Channel, Message, RequestId, Channel)
  postulate(routeChannelWithPhase,
    Channel -> Message -> RequestId -> Phase -> Channel)
  bindPostulate(routeChannelWithPhase, hostRouteChannelWithPhase,
    Channel, Message, RequestId, Phase, Channel)
  postulate(routeChannelWithSample,
    Channel -> Message -> RequestId -> Phase -> Sample -> Channel)
  bindPostulate(routeChannelWithSample, hostRouteChannelWithSample,
    Channel, Message, RequestId, Phase, Sample, Channel)
  postulate(startFuture, Channel -> PendingResult)
  bindPostulate(startFuture, hostFutureForChannel, Channel, PendingResult)
  postulate(passFuture, PendingResult -> PendingResult)
  bindPostulate(passFuture, hostFutureIdentity, PendingResult)
  postulate(invokeCallback, Callback -> Sample -> Sample)
  bindPostulate(invokeCallback, hostInvokeCallback,
    Callback, Sample, Sample)
  proc generatedRotateRole(channel: Channel): Channel =
    rotateChannel(channel)
  proc generatedRouteRole(channel: Channel, message: Message): Channel =
    routeChannel(channel, message)
  proc generatedRouteWithIdRole(channel: Channel, message: Message,
                                requestId: RequestId): Channel =
    routeChannelWithId(channel, message, requestId)
  proc generatedRouteWithPhaseRole(channel: Channel, message: Message,
                                   requestId: RequestId,
                                   phase: Phase): Channel =
    routeChannelWithPhase(channel, message, requestId, phase)
  proc generatedRouteWithSampleRole(channel: Channel, message: Message,
                                    requestId: RequestId, phase: Phase,
                                    sample: Sample): Channel =
    routeChannelWithSample(channel, message, requestId, phase, sample)
  proc generatedFutureRole(channel: Channel): PendingResult =
    startFuture(channel)
  proc generatedFutureInput(value: PendingResult): PendingResult =
    passFuture(value)
  proc generatedOpaqueSigmaId(value: Sig(Nat, Channel)): Sig(Nat, Channel) =
    value
  proc generatedCallbackRole(callback: Callback, value: Sample): Sample =
    invokeCallback(callback, value)
  proc generatedApplyMappedCallback(
      callback: proc(channel: Channel, message: Message): Channel {.closure.},
      channel: Channel, message: Message): Channel =
    callback(channel, message)
  proc generatedReturnMappedCallback():
      proc(channel: Channel, message: Message): Channel {.closure.} =
    lam(channel, Channel, lam(message, Message,
      routeChannel(channel, message)))

proc hostIndexedChannelParts(channel: IndexedChannelHandle):
    tuple[index: int, next: IndexedChannelHandle] =
  (channel.index, IndexedChannelHandle(index: channel.index,
    label: channel.label & "/indexed"))

proc hostRepeatIndexedChannel(index: int, channel: IndexedChannelHandle):
    tuple[first: IndexedChannelHandle, second: IndexedChannelHandle] =
  (channel, IndexedChannelHandle(index: index, label: channel.label & "/copy"))

proc hostMakeIndexedVector(seed: int): tuple[count: int, values: seq[int]] =
  result.count = abs(seed mod 20)
  for i in 0 ..< result.count:
    result.values.add(seed + i)
  if seed == low(int):
    if result.values.len > 0: result.values.setLen(result.values.len - 1)
    else: result.values.add(seed)

proc hostMakeVectorForIndex(index, seed: int):
    tuple[marker: int, values: seq[int]] =
  result.marker = seed
  for i in 0 ..< index:
    result.values.add(seed + i)
  if seed == low(int):
    if result.values.len > 0: result.values.setLen(result.values.len - 1)
    else: result.values.add(seed)

eponymBlock:
  import "../lib/nat.ep"
  postulate(Channel, Nat -> Univ)
  runtimeType(Channel, IndexedChannelHandle)
  postulate(splitIndexedChannel,
    Channel[0] -> Sig(index: Nat, Channel[index]))
  bindPostulatePairTrusted(splitIndexedChannel, hostIndexedChannelParts,
    Channel, Nat, Channel)
  runtimePairTrusted(generatedSplitIndexedChannel)
  postulate(repeatIndexedChannel,
    Pi(index: Nat, channel: Channel[index],
       Sig(first: Channel[index], Channel[index])))
  bindPostulatePair(repeatIndexedChannel, hostRepeatIndexedChannel,
    Nat, Channel, Channel, Channel)
  proc generatedIndexedChannelIndex(channel: Channel[0]): Nat =
    fst(splitIndexedChannel(channel))
  proc generatedSplitIndexedChannel(channel: Channel[0]):
      Sig(index: Nat, Channel[index]) =
    splitIndexedChannel(channel)
  proc generatedRepeatIndexedChannel(index: Nat, channel: Channel[index]):
      Sig(first: Channel[index], Channel[index]) =
    repeatIndexedChannel(channel)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  postulate(makeIndexedVector,
    Int -> Sig(count: Nat, Vec[Int, count]))
  bindPostulatePairTrusted(makeIndexedVector, hostMakeIndexedVector,
    Int, Nat, Vec)
  proc generatedMakeIndexedVector(seed: Int):
      Sig(count: Nat, Vec[Int, count]) = makeIndexedVector(seed)
  runtimePairTrusted(generatedMakeIndexedVector)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  postulate(makeVectorForIndex,
    Pi(index: Nat, seed: Int, Sig(marker: Int, Vec[Int, index])))
  bindPostulatePairTrusted(makeVectorForIndex, hostMakeVectorForIndex,
    Nat, Int, Int, Vec)
  proc generatedVectorArgIdentity(index: Nat,
      values: Vec[Int, index]): Vec[Int, index] = values
  runtimeValue(generatedVectorArgIdentity)
  proc generatedVectorForIndex(index: Nat, seed: Int):
      Sig(marker: Int, Vec[Int, index]) = makeVectorForIndex(seed)
  runtimePairTrusted(generatedVectorForIndex)

eponymBlock:
  import "fixtures/runtime_pair_postulate.ep"
  runtimeVector(Vec)
  bindPostulatePairTrusted(makeVectorForIndex, hostMakeVectorForIndex,
    Nat, Int, Int, Vec)
  proc generatedImportedVectorForIndex(index: Nat, seed: Int):
      Sig(marker: Int, Vec[Int, index]) = makeVectorForIndex(seed)
  runtimePairTrusted(generatedImportedVectorForIndex)

static:
  doAssert compiles(importedImplicitNatVecIdentity[3](@[1, 2, 3]))
  doAssert compiles(importedImplicitNatVecIdentityRuntimeValue[3](@[1, 2, 3]))
  doAssert compiles(importedImplicitBoolIdentity[true]())
  doAssert compiles(importedImplicitIntIdentity[17]())
  doAssert compiles(importedImplicitTokenIdentity[importedTokenRed]())
  doAssert compiles(importedImplicitBoolIdentityRuntimeValue[false]())
  doAssert compiles(importedImplicitIntIdentityRuntimeValue[17]())
  doAssert compiles(importedImplicitTokenIdentityRuntimeValue[importedTokenBlue]())
  doAssert compiles(generatedCheckedRole(35))
  doAssert compiles(generatedDefault())
  doAssert compiles(generatedDefault(7))
  doAssert compiles(generatedDefault(value = 7))
  doAssert compiles(generatedAdd(left = 20, right = 22))
  doAssert compiles(generatedAdd(20, 22))
  doAssert not compiles(generatedAdd(42))
  doAssert not compiles(generatedAdd("20", 22))
  doAssert compiles(generatedNatId(17))
  doAssert compiles(generatedSigmaId((17, -9)))
  doAssert not compiles(generatedSigmaId((17, "wrong field type")))
  doAssert compiles(generatedArithmetic(1, 2, 3))
  doAssert compiles(generatedChooseTrue())
  doAssert compiles(generatedChooseFalse())
  doAssert compiles(generatedRotateRole(ChannelHandle(id: 1)))
  doAssert not compiles(generatedRotateRole("not a channel"))
  doAssert compiles(generatedRouteRole(ChannelHandle(id: 1), "hello"))
  doAssert not compiles(generatedRouteRole("not a channel", "hello"))
  doAssert compiles(generatedRouteWithIdRole(ChannelHandle(id: 1), "hello", 2))
  doAssert compiles(generatedRouteWithPhaseRole(ChannelHandle(id: 1),
    "hello", 2, 3))
  doAssert compiles(generatedFutureRole(ChannelHandle(id: 1)))
  doAssert compiles(generatedFutureInput(newFuture[int]("typedFuture")))
  doAssert compiles(generatedOpaqueSigmaId((17, ChannelHandle(id: 1))))
  doAssert compiles(generatedPointId(RuntimePoint(x: 17,
    channel: ChannelHandle(id: 1))))
  doAssert compiles(generatedSplitChannel(ChannelHandle(id: 17)))
  doAssert compiles(generatedSplitChannelWithNat(3,
    ChannelHandle(id: 17)))
  doAssert compiles(generatedSplitChannelWithTwoNats(3, 4,
    ChannelHandle(id: 17)))
  doAssert compiles(generatedEnvelopeId(RuntimeEnvelope(
    point: RuntimePoint(x: 17, channel: ChannelHandle(id: 1)),
    note: "ok")))
  doAssert compiles(generatedCallbackRole(proc(value: int): int = value + 1, 1))
  doAssert not compiles(generatedCallbackRole(42, 1))
  doAssert compiles(generatedApplyMappedCallback(
    proc(channel: ChannelHandle, message: string): ChannelHandle = channel,
    ChannelHandle(id: 1), "mapped"))
  doAssert compiles(generatedReturnMappedCallback()(
    ChannelHandle(id: 1), "mapped"))
  doAssert compiles(generatedIndexedChannelIndex(
    IndexedChannelHandle(index: 17, label: "indexed")))
  doAssert compiles(generatedSplitIndexedChannel(
    IndexedChannelHandle(index: 17, label: "indexed")))
  doAssert compiles(generatedRepeatIndexedChannel(17,
    IndexedChannelHandle(index: 17, label: "indexed")))

when isMainModule:
  let treeRuntime = sampleTreeRuntimeValue()
  let nodeId = treeRuntime.globals["node"].tm.refId
  let leafId = treeRuntime.globals["leaf"].tm.refId
  doAssert treeRuntime.value.whnfRefId == nodeId
  doAssert treeRuntime.value.whnfSpineLen == 2
  doAssert treeRuntime.value.whnfSpineArg(0).whnfNatLitVal == 37
  doAssert treeRuntime.value.whnfSpineArg(1).whnfRefId == leafId
  let parameterizedTree = sampleTreeWithRuntimeValue(91)
  doAssert parameterizedTree.value.whnfRefId == nodeId
  doAssert parameterizedTree.value.whnfSpineArg(0).whnfNatLitVal == 91
  let rawParameterizedTree = sampleTreeWithRuntimeValue([natToValue(91)])
  doAssert rawParameterizedTree.value.whnfRefId == nodeId
  var wrongRuntimeArityRejected = false
  try:
    discard sampleTreeWithRuntimeValue([])
  except ValueError as error:
    wrongRuntimeArityRejected = "argument count mismatch" in error.msg
  doAssert wrongRuntimeArityRejected
  let rawAddRuntime = generatedAddRuntimeValue(
    [intToValue(20), intToValue(22)])
  doAssert valueToInt(rawAddRuntime.value) == 42
  var wrongRawRuntimeArgumentRejected = false
  try:
    discard generatedAddRuntimeValue([natToValue(20), intToValue(22)])
  except ValueError:
    wrongRawRuntimeArgumentRejected = true
  doAssert wrongRawRuntimeArgumentRejected
  let boundRuntime = runtimeResultRuntimeValue()
  doAssert boundRuntime.value.whnfKind == wInt
  doAssert boundRuntime.value.whnfIntVal == 42
  let baseDir = currentSourcePath().parentDir.parentDir
  var r = initRng(424242'u64)

  let variantSrc = readFile(baseDir / "tests/fixtures/runtime_variant.ep")
  let variantGlobals = getGlobalsDir(baseDir, variantSrc)
  let importedGenericVariantSrc = readFile(
    baseDir / "tests/fixtures/runtime_imported_generic_variant.ep")
  let importedGenericVariantGlobals = getGlobalsDir(
    baseDir / "tests/fixtures", importedGenericVariantSrc)
  const runtimeTreeConstructors = ["treeEmpty", "treeNode"]
  let rawVariantCases = forAll(
    "generic structural codecs preserve payload-bearing data constructors",
    r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      var tree = runtimeVariantToValue(RuntimeVariant(
        constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
        runtimeTreeConstructors)
      for i in 0 ..< length:
        tree = runtimeVariantToValue(RuntimeVariant(
          constructor: "treeNode",
          arguments: @[intToValue(i), tree]), variantGlobals,
          "RuntimeTree", runtimeTreeConstructors)
      let typedRoundTrip = runtimeStructuredVariantToValue(
        treeIdentity(valueToRuntimeStructuredVariant(tree, variantGlobals,
          "RuntimeTree", runtimeTreeConstructors)), variantGlobals,
        "RuntimeTree", runtimeTreeConstructors)
      var decoded: seq[int] = @[]
      var current = tree
      while true:
        let variant = valueToRuntimeVariant(current, variantGlobals,
          "RuntimeTree", runtimeTreeConstructors)
        if variant.constructor == "treeEmpty":
          return decoded == runtimeTreePayloads(typedRoundTrip,
            variantGlobals)
        if variant.constructor != "treeNode" or
            variant.arguments.len != 2:
          return false
        decoded.add(valueToInt(variant.arguments[0]))
        current = variant.arguments[1]
      false,
    shrinkInt)
  if not rawVariantCases:
    quit(1)
  let structuredBoolCases = forAll(
    "runtimeDataVariant recursively maps Bool and data payloads", r, 200,
    proc(r: var Rng): int = r.genInt(0, 1),
    proc(bit: int): bool =
      let emptyTree = runtimeVariantToValue(RuntimeVariant(
        constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
        runtimeTreeConstructors)
      let decision = runtimeVariantToValue(RuntimeVariant(
        constructor: "decisionNode",
        arguments: @[boolToValue(bit == 1, variantGlobals), emptyTree]),
        variantGlobals, "DecisionTree", ["decisionNode"])
      let hostDecision = valueToRuntimeStructuredVariant(decision,
        variantGlobals, "DecisionTree", ["decisionNode"])
      let returned = runtimeStructuredVariantToValue(
        decisionIdentity(hostDecision), variantGlobals, "DecisionTree",
        ["decisionNode"])
      let decoded = valueToRuntimeStructuredVariant(returned, variantGlobals,
        "DecisionTree", ["decisionNode"])
      decoded.arguments.len == 2 and
        decoded.arguments[0].kind == rsvBool and
        decoded.arguments[0].boolValue == (bit == 1) and
        decoded.arguments[1].kind == rsvVariant and
        decoded.arguments[1].variantValue.constructor == "treeEmpty",
    shrinkInt)
  if not structuredBoolCases:
    quit(1)
  let opaqueStructuredCases = forAll(
    "runtimeDataVariant composes mapped opaque host fields", r, 200,
    proc(r: var Rng): tuple[id: int, count: int] =
      (r.genInt(-100, 100), r.genInt(-100, 100)),
    proc(sample: tuple[id: int, count: int]): bool =
      let input = RuntimeStructuredVariant(constructor: "handleEnvelope",
        arguments: @[runtimeStructuredOpaque(ChannelHandle(id: sample.id,
          label: "channel-" & $sample.id)),
          runtimeStructuredOpaque(ChannelHandle(id: sample.id + 1,
            label: "opaque-" & $sample.id)),
          RuntimeStructuredValue(kind: rsvInt, intValue: sample.count)])
      let output = handleEnvelopeIdentity(input)
      output.constructor == "handleEnvelope" and
        output.arguments.len == 3 and
        runtimeStructuredOpaqueAs[ChannelHandle](output.arguments[0]) ==
          ChannelHandle(id: sample.id, label: "decoded-" & $sample.id) and
        runtimeStructuredOpaqueAs[ChannelHandle](output.arguments[1]) ==
          ChannelHandle(id: sample.id + 1, label: "opaque-" & $sample.id) and
        output.arguments[2].kind == rsvInt and
        output.arguments[2].intValue == sample.count,
    proc(value: tuple[id: int, count: int]): seq[tuple[id: int, count: int]] =
      @[])
  if not opaqueStructuredCases:
    quit(1)
  let indexedOpaqueStructuredCases = forAll(
    "runtimeDataVariant checks indices on mapped opaque family fields", r,
    200,
    proc(r: var Rng): tuple[length, id: int] =
      (r.genInt(0, 100), r.genInt(-1000, 1000)),
    proc(sample: tuple[length, id: int]): bool =
      let host = ChannelHandle(id: sample.id, label: $sample.id)
      let codec = [runtimeStructuredHostCodec[ChannelHandle](
        "RuntimeIndexedToken")]
      let encoded = runtimeStructuredVariantToValue(
        RuntimeStructuredVariant(constructor: "indexedEnvelope",
          arguments: @[RuntimeStructuredValue(kind: rsvNat,
            natValue: sample.length), runtimeStructuredOpaque(host)]),
        variantGlobals, "IndexedEnvelope", ["indexedEnvelope"], codec)
      let decoded = valueToRuntimeStructuredVariant(encoded, variantGlobals,
        "IndexedEnvelope", ["indexedEnvelope"], codec)
      var wrongIndexRejected = false
      try:
        let wrongType = callRuntimeValue(
          eval(variantGlobals["RuntimeIndexedToken"].tm, @[]),
          [natToValue(sample.length + 1, variantGlobals)])
        let wrongToken = toHostValueAtRuntimeType(host, wrongType,
          variantGlobals)
        let malformed = callRuntimeValue(
          eval(variantGlobals["indexedEnvelope"].tm, @[]),
          [natToValue(sample.length, variantGlobals), wrongToken])
        discard valueToRuntimeStructuredVariant(malformed, variantGlobals,
          "IndexedEnvelope", ["indexedEnvelope"], codec)
      except ValueError:
        wrongIndexRejected = true
      decoded.constructor == "indexedEnvelope" and
        decoded.arguments.len == 2 and
        decoded.arguments[0].natValue == sample.length and
        runtimeStructuredOpaqueAs[ChannelHandle](decoded.arguments[1]) == host and
        wrongIndexRejected,
    proc(value: tuple[length, id: int]): seq[tuple[length, id: int]] = @[])
  if not indexedOpaqueStructuredCases:
    quit(1)
  let malformedHandleEnvelope = callRuntimeValue(
    eval(variantGlobals["handleEnvelope"].tm, @[]),
    [intToValue(23),
      toHostValue(ChannelHandle(id: 24, label: "malformed")),
      intToValue(25)])
  var malformedOpaqueFieldRejected = false
  try:
    discard valueToRuntimeStructuredVariant(malformedHandleEnvelope,
      variantGlobals, "HandleEnvelope", ["handleEnvelope"],
      [runtimeStructuredCustomCodec[ChannelHandle]("RuntimeHandle",
        encodeRuntimeHandle, decodeRuntimeHandle)])
  except ValueError:
    malformedOpaqueFieldRejected = true
  doAssert malformedOpaqueFieldRejected
  let wrongWitnessHandle = toHostValueAtRuntimeType(
    ChannelHandle(id: 24, label: "wrong-witness"),
    eval(variantGlobals["RuntimeOtherToken"].tm, @[]), variantGlobals)
  let validEnvelopeHandle = callRuntimeValue(
    eval(variantGlobals["runtimeHandle"].tm, @[]), [intToValue(23)])
  let missingWitnessEnvelope = callRuntimeValue(
    eval(variantGlobals["handleEnvelope"].tm, @[]),
    [validEnvelopeHandle,
     toHostValue(ChannelHandle(id: 24, label: "missing-witness")),
     intToValue(25)])
  var nestedMissingWitnessRejected = false
  try:
    discard valueToRuntimeStructuredVariant(missingWitnessEnvelope,
      variantGlobals, "HandleEnvelope", ["handleEnvelope"],
      [runtimeStructuredCustomCodec[ChannelHandle]("RuntimeHandle",
        encodeRuntimeHandle, decodeRuntimeHandle),
       runtimeStructuredHostCodec[ChannelHandle]("RuntimeOpaqueToken")])
  except ValueError:
    nestedMissingWitnessRejected = true
  doAssert nestedMissingWitnessRejected
  let wrongWitnessEnvelope = callRuntimeValue(
    eval(variantGlobals["handleEnvelope"].tm, @[]),
    [validEnvelopeHandle, wrongWitnessHandle, intToValue(25)])
  var nestedOpaqueWitnessRejected = false
  try:
    discard valueToRuntimeStructuredVariant(wrongWitnessEnvelope,
      variantGlobals, "HandleEnvelope", ["handleEnvelope"],
      [runtimeStructuredCustomCodec[ChannelHandle]("RuntimeHandle",
        encodeRuntimeHandle, decodeRuntimeHandle),
       runtimeStructuredHostCodec[ChannelHandle]("RuntimeOpaqueToken")])
  except ValueError:
    nestedOpaqueWitnessRejected = true
  doAssert nestedOpaqueWitnessRejected
  var wrongOpaqueEncodingRejected = false
  try:
    discard runtimeStructuredVariantToValue(
      RuntimeStructuredVariant(constructor: "handleEnvelope",
        arguments: @[runtimeStructuredOpaque(ChannelHandle(id: 1,
          label: "wrong")),
          runtimeStructuredOpaque(ChannelHandle(id: 2, label: "token")),
          RuntimeStructuredValue(kind: rsvInt, intValue: 3)]),
      variantGlobals, "HandleEnvelope", ["handleEnvelope"],
      [runtimeStructuredCustomCodec[ChannelHandle]("RuntimeHandle",
        encodeWrongRuntimeHandle, decodeRuntimeHandle),
       runtimeStructuredHostCodec[ChannelHandle]("RuntimeOpaqueToken")])
  except ValueError:
    wrongOpaqueEncodingRejected = true
  doAssert wrongOpaqueEncodingRejected
  let wrongTopLevelCodecCases = forAll(
    "custom runtimeCodec rejects wrongly typed top-level encodings", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let value = ChannelHandle(id: id, label: $id)
      var wrapperRejected = false
      try:
        discard runtimeHandleConstant(value)
      except ValueError:
        wrapperRejected = true
      var runtimeValueRejected = false
      try:
        discard runtimeHandleConstantRuntimeValue(value)
      except ValueError:
        runtimeValueRejected = true
      wrapperRejected and runtimeValueRejected,
    shrinkInt)
  if not wrongTopLevelCodecCases:
    quit(1)
  let wrongTopLevelDecodeCases = forAll(
    "custom runtimeCodec validates Values before decoding", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      runtimeHandleDecodeCalls = 0
      var rejected = false
      try:
        discard checkedMalformedRuntimeHandle(ChannelHandle(id: id,
          label: $id))
      except ValueError:
        rejected = true
      rejected and runtimeHandleDecodeCalls == 0,
    shrinkInt)
  if not wrongTopLevelDecodeCases:
    quit(1)
  let missingOpaqueWitnessCases = forAll(
    "typed opaque mappings reject missing Eponym type witnesses", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      var rejected = false
      try:
        discard checkedOpaqueTypeWitness(ChannelHandle(id: id,
          label: $id))
      except ValueError:
        rejected = true
      rejected,
    shrinkInt)
  if not missingOpaqueWitnessCases:
    quit(1)
  let mismatchedOpaqueWitnessCases = forAll(
    "typed opaque mappings reject a different Eponym type witness", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      var rejected = false
      try:
        discard checkedOpaqueTypeWitnessType(ChannelHandle(id: id,
          label: $id))
      except ValueError:
        rejected = true
      rejected,
    shrinkInt)
  if not mismatchedOpaqueWitnessCases:
    quit(1)
  let appliedGenericTypeCases = forAll(
    "mapped applied generic domains check their runtime indices", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let tree = runtimeVariantToValue(RuntimeVariant(
        constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
        runtimeTreeConstructors)
      let indexed = runtimeVariantToValue(RuntimeVariant(
        constructor: "sizedTree",
        arguments: @[natToValue(length, variantGlobals), tree]),
        variantGlobals, "SizedTree", ["sizedTree"])
      let inferredType = runtimeValueTypeOf(indexed, variantGlobals)
      let expectedType = callRuntimeValue(
        eval(variantGlobals["SizedTree"].tm, @[]),
        [natToValue(length, variantGlobals)])
      validateRuntimeValueType(indexed, inferredType, variantGlobals)
      validateRuntimeValueType(indexed, expectedType, variantGlobals)
      let rawIdentity = generatedGenericRuntimeValueIdentityRuntimeValueRaw(
        [inferredType], [indexed])
      validateRuntimeValueType(rawIdentity.value, expectedType,
        rawIdentity.globals)
      var wrongIndexRejected = false
      try:
        validateRuntimeValueType(indexed,
          callRuntimeValue(eval(variantGlobals["SizedTree"].tm, @[]),
            [natToValue(length + 1, variantGlobals)]), variantGlobals)
      except ValueError:
        wrongIndexRejected = true
      let projected = genericIndexedTreeProjectionRuntimeValueDynamic(
        length, valueToRuntimeStructuredVariant(indexed, variantGlobals,
          "SizedTree", ["sizedTree"]), 0)
      let decoded = valueToRuntimeStructuredVariant(projected.value,
        variantGlobals,
        "SizedTree", ["sizedTree"])
      not inferredType.isNil and wrongIndexRejected and
      valueToRuntimeStructuredVariant(rawIdentity.value,
        rawIdentity.globals, "SizedTree", ["sizedTree"]).arguments[0].natValue ==
          length and
      decoded.constructor == "sizedTree" and
      decoded.arguments.len == 2 and
        decoded.arguments[0].kind == rsvNat and
        decoded.arguments[0].natValue == length and
        decoded.arguments[1].kind == rsvVariant and
        decoded.arguments[1].variantValue.constructor == "treeEmpty",
    shrinkInt)
  if not appliedGenericTypeCases:
    quit(1)
  let indexedVariantCallbackCases = forAll(
    "generic callbacks infer and enforce indexed variant type arguments", r,
    200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let empty = RuntimeStructuredValue(kind: rsvVariant,
        variantValue: RuntimeStructuredVariant(constructor: "treeEmpty"))
      let value = RuntimeStructuredVariant(constructor: "sizedTree",
        arguments: @[RuntimeStructuredValue(kind: rsvNat,
          natValue: length), empty])
      let callback: proc(value: RuntimeStructuredVariant):
          RuntimeStructuredVariant {.closure.} =
        proc(value: RuntimeStructuredVariant): RuntimeStructuredVariant =
          value
      let typed = importedGenericIndexedVariantCallbackApply(callback, value)
      let runtime = importedGenericIndexedVariantCallbackApplyRuntimeValue(
        callback, value)
      let decoded = valueToRuntimeStructuredVariant(runtime.value,
        runtime.globals, "SizedTree", ["sizedTree"])
      let wrongIndexCallback: proc(value: RuntimeStructuredVariant):
          RuntimeStructuredVariant {.closure.} =
        proc(value: RuntimeStructuredVariant): RuntimeStructuredVariant =
          result = value
          inc result.arguments[0].natValue
      var typedMismatchRejected = false
      try:
        discard importedGenericIndexedVariantCallbackApply(
          wrongIndexCallback, value)
      except ValueError:
        typedMismatchRejected = true
      var runtimeMismatchRejected = false
      try:
        discard importedGenericIndexedVariantCallbackApplyRuntimeValue(
          wrongIndexCallback, value)
      except ValueError:
        runtimeMismatchRejected = true
      typed.constructor == "sizedTree" and typed.arguments.len == 2 and
        typed.arguments[0].kind == rsvNat and
        typed.arguments[0].natValue == length and
        typed.arguments[1].variantValue.constructor == "treeEmpty" and
        decoded.constructor == "sizedTree" and decoded.arguments.len == 2 and
        decoded.arguments[0].kind == rsvNat and
        decoded.arguments[0].natValue == length and
        decoded.arguments[1].variantValue.constructor == "treeEmpty" and
        typedMismatchRejected and
        runtimeMismatchRejected,
    shrinkInt)
  if not indexedVariantCallbackCases:
    quit(1)
  let indexedCodecCallbackCases = forAll(
    "generic callbacks infer indexed custom-codec type arguments", r, 50,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let value = RuntimeStructuredVariant(constructor: "sizedTree",
        arguments: @[
          RuntimeStructuredValue(kind: rsvNat, natValue: length),
          RuntimeStructuredValue(kind: rsvVariant,
            variantValue: RuntimeStructuredVariant(constructor: "treeEmpty"))])
      let callback: proc(value: RuntimeStructuredVariant):
          RuntimeStructuredVariant {.closure.} =
        proc(value: RuntimeStructuredVariant): RuntimeStructuredVariant =
          value
      let typed = importedGenericIndexedCodecCallbackApply(callback, value)
      let runtime = importedGenericIndexedCodecCallbackApplyRuntimeValue(
        callback, value)
      let decoded = decodeRuntimeSizedTree(runtime.value, runtime.globals)
      let wrongIndexCallback: proc(value: RuntimeStructuredVariant):
          RuntimeStructuredVariant {.closure.} =
        proc(value: RuntimeStructuredVariant): RuntimeStructuredVariant =
          result = value
          inc result.arguments[0].natValue
      var typedMismatchRejected = false
      try:
        discard importedGenericIndexedCodecCallbackApply(
          wrongIndexCallback, value)
      except ValueError:
        typedMismatchRejected = true
      var runtimeMismatchRejected = false
      try:
        discard importedGenericIndexedCodecCallbackApplyRuntimeValue(
          wrongIndexCallback, value)
      except ValueError:
        runtimeMismatchRejected = true
      typed.arguments[0].natValue == length and
        decoded.arguments[0].natValue == length and typedMismatchRejected and
        runtimeMismatchRejected,
    shrinkInt)
  if not indexedCodecCallbackCases:
    quit(1)
  let indexedOptionCallbackCases = forAll(
    "generic callbacks infer indexed witnesses from Option.some", r, 50,
    proc(r: var Rng): tuple[length: int, present: bool] =
      (r.genInt(0, 100), r.genBool),
    proc(input: tuple[length: int, present: bool]): bool =
      let treeValue = RuntimeStructuredVariant(constructor: "sizedTree",
        arguments: @[
          RuntimeStructuredValue(kind: rsvNat, natValue: input.length),
          RuntimeStructuredValue(kind: rsvVariant,
            variantValue: RuntimeStructuredVariant(constructor: "treeEmpty"))])
      let value = if input.present: some(treeValue)
        else: none[RuntimeStructuredVariant]()
      let callback: proc(value: Option[RuntimeStructuredVariant]):
          Option[RuntimeStructuredVariant] {.closure.} =
        proc(value: Option[RuntimeStructuredVariant]):
            Option[RuntimeStructuredVariant] = value
      if not input.present:
        var typedRejected = false
        try:
          discard importedGenericIndexedOptionCallbackApply(callback, value)
        except ValueError as error:
          typedRejected = "cannot infer indexed Eponym type argument" in error.msg
        var runtimeRejected = false
        try:
          discard importedGenericIndexedOptionCallbackApplyRuntimeValue(
            callback, value)
        except ValueError as error:
          runtimeRejected = "cannot infer indexed Eponym type argument" in error.msg
        return typedRejected and runtimeRejected
      let typed = importedGenericIndexedOptionCallbackApply(callback, value)
      let runtime = importedGenericIndexedOptionCallbackApplyRuntimeValue(
        callback, value)
      let treeType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "SizedTree"),
        [natToValue(input.length, runtime.globals)])
      let expectedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Option"), [treeType])
      validateRuntimeValueType(runtime.value, expectedType, runtime.globals)
      let decoded = valueToOption(runtime.value, runtime.globals, "Option",
        proc(item: Value, globals: Globals): RuntimeStructuredVariant =
          valueToRuntimeStructuredVariant(item, globals, "SizedTree",
            ["sizedTree"]))
      let wrongIndexCallback: proc(value: Option[RuntimeStructuredVariant]):
          Option[RuntimeStructuredVariant] {.closure.} =
        proc(value: Option[RuntimeStructuredVariant]):
            Option[RuntimeStructuredVariant] =
          if value.isNone: return none[RuntimeStructuredVariant]()
          var resultValue = value.get
          inc resultValue.arguments[0].natValue
          some(resultValue)
      var typedMismatchRejected = false
      try:
        discard importedGenericIndexedOptionCallbackApply(wrongIndexCallback,
          value)
      except ValueError:
        typedMismatchRejected = true
      var runtimeMismatchRejected = false
      try:
        discard importedGenericIndexedOptionCallbackApplyRuntimeValue(
          wrongIndexCallback, value)
      except ValueError:
        runtimeMismatchRejected = true
      typed.isSome and typed.get.arguments[0].natValue == input.length and
        decoded.isSome and decoded.get.arguments[0].natValue == input.length and
        typedMismatchRejected and runtimeMismatchRejected,
    proc(input: tuple[length: int, present: bool]):
        seq[tuple[length: int, present: bool]] = @[])
  if not indexedOptionCallbackCases:
    quit(1)
  let nestedOptionWitnessCases = forAll(
    "generic callbacks infer indexed witnesses through nested Options", r, 50,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let tree = RuntimeStructuredVariant(constructor: "sizedTree",
        arguments: @[
          RuntimeStructuredValue(kind: rsvNat, natValue: length),
          RuntimeStructuredValue(kind: rsvVariant,
            variantValue: RuntimeStructuredVariant(constructor: "treeEmpty"))])
      let value = some(some(tree))
      let callback: proc(value: Option[Option[RuntimeStructuredVariant]]):
          Option[Option[RuntimeStructuredVariant]] {.closure.} =
        proc(value: Option[Option[RuntimeStructuredVariant]]):
            Option[Option[RuntimeStructuredVariant]] = value
      let typed = importedGenericIndexedNestedOptionCallbackApply(callback,
        value)
      let runtime = importedGenericIndexedNestedOptionCallbackApplyRuntimeValue(
        callback, value)
      let treeType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "SizedTree"),
        [natToValue(length, runtime.globals)])
      let nestedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Option"),
        [callRuntimeValue(runtimeGlobalValue(runtime.globals, "Option"),
          [treeType])])
      var typedMismatchRejected = false
      var badTree = tree
      inc badTree.arguments[0].natValue
      let wrongIndexCallback:
          proc(value: Option[Option[RuntimeStructuredVariant]]):
            Option[Option[RuntimeStructuredVariant]] {.closure.} =
        proc(value: Option[Option[RuntimeStructuredVariant]]):
            Option[Option[RuntimeStructuredVariant]] = some(some(badTree))
      try:
        discard importedGenericIndexedNestedOptionCallbackApply(
          wrongIndexCallback, value)
      except ValueError:
        typedMismatchRejected = true
      var runtimeMismatchRejected = false
      try:
        discard importedGenericIndexedNestedOptionCallbackApplyRuntimeValue(
          wrongIndexCallback, value)
      except ValueError:
        runtimeMismatchRejected = true
      var missingWitnessRejected = false
      try:
        discard importedGenericIndexedNestedOptionCallbackApply(callback,
          none[Option[RuntimeStructuredVariant]]())
      except ValueError as error:
        missingWitnessRejected = "cannot infer indexed Eponym type argument" in
          error.msg
      var missingRuntimeWitnessRejected = false
      try:
        discard importedGenericIndexedNestedOptionCallbackApplyRuntimeValue(
          callback, some(none[RuntimeStructuredVariant]()))
      except ValueError as error:
        missingRuntimeWitnessRejected =
          "cannot infer indexed Eponym type argument" in error.msg
      validateRuntimeValueType(runtime.value, nestedType, runtime.globals)
      typed.isSome and typed.get.isSome and
        typed.get.get.arguments[0].natValue == length and
        typedMismatchRejected and runtimeMismatchRejected and
        missingWitnessRejected and missingRuntimeWitnessRejected,
    shrinkInt)
  if not nestedOptionWitnessCases:
    quit(1)
  let indexedSigmaWitnessCases = forAll(
    "generic callbacks infer indexed witnesses from Sigma fields", r, 50,
    proc(r: var Rng): tuple[tag, length: int] =
      (r.genInt(-1000, 1000), r.genInt(0, 100)),
    proc(input: tuple[tag, length: int]): bool =
      let tree = RuntimeStructuredVariant(constructor: "sizedTree",
        arguments: @[
          RuntimeStructuredValue(kind: rsvNat, natValue: input.length),
          RuntimeStructuredValue(kind: rsvVariant,
            variantValue: RuntimeStructuredVariant(constructor: "treeEmpty"))])
      let value = (input.tag, tree)
      let callback: proc(value: tuple[tag: int,
          payload: RuntimeStructuredVariant]): tuple[tag: int,
          payload: RuntimeStructuredVariant] {.closure.} =
        proc(value: tuple[tag: int, payload: RuntimeStructuredVariant]):
            tuple[tag: int, payload: RuntimeStructuredVariant] = value
      let typed = importedGenericIndexedSigmaCallbackApply(callback, value)
      let runtime = importedGenericIndexedSigmaCallbackApplyRuntimeValue(
        callback, value)
      let expectedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "SizedTree"),
        [natToValue(input.length, runtime.globals)])
      validateRuntimeValueType(runtimePairSecond(runtime.value), expectedType,
        runtime.globals)
      let badCallback: proc(value: tuple[tag: int,
          payload: RuntimeStructuredVariant]): tuple[tag: int,
          payload: RuntimeStructuredVariant] {.closure.} =
        proc(value: tuple[tag: int, payload: RuntimeStructuredVariant]):
            tuple[tag: int, payload: RuntimeStructuredVariant] =
          var payload = value.payload
          inc payload.arguments[0].natValue
          (value.tag, payload)
      var typedWrongIndexRejected = false
      try:
        discard importedGenericIndexedSigmaCallbackApply(badCallback, value)
      except ValueError:
        typedWrongIndexRejected = true
      var runtimeWrongIndexRejected = false
      try:
        discard importedGenericIndexedSigmaCallbackApplyRuntimeValue(
          badCallback, value)
      except ValueError:
        runtimeWrongIndexRejected = true
      typed[0] == input.tag and
        typed[1].arguments[0].natValue == input.length and
        valueToInt(runtimePairFirst(runtime.value)) == input.tag and
        typedWrongIndexRejected and runtimeWrongIndexRejected,
    proc(input: tuple[tag, length: int]): seq[tuple[tag, length: int]] = @[])
  if not indexedSigmaWitnessCases:
    quit(1)
  let nestedIndexedOptionCallbackCases = forAll(
    "generic callbacks infer indexed witnesses inside Option and Vec", r, 50,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      proc tree(index: int): RuntimeStructuredVariant =
        RuntimeStructuredVariant(constructor: "sizedTree", arguments: @[
          RuntimeStructuredValue(kind: rsvNat, natValue: index),
          RuntimeStructuredValue(kind: rsvVariant,
            variantValue: RuntimeStructuredVariant(
              constructor: "treeEmpty"))])
      let value = some(@[tree(length), tree(length)])
      let callback: proc(value: Option[seq[RuntimeStructuredVariant]]):
          Option[seq[RuntimeStructuredVariant]] {.closure.} =
        proc(value: Option[seq[RuntimeStructuredVariant]]):
            Option[seq[RuntimeStructuredVariant]] = value
      let typed = importedGenericIndexedNestedOptionVectorCallbackApply(
        callback, value)
      let runtime =
        importedGenericIndexedNestedOptionVectorCallbackApplyRuntimeValue(
          callback, value)
      let treeType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "SizedTree"),
        [natToValue(length, runtime.globals)])
      let vectorType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Vec"),
        [treeType, natToValue(2, runtime.globals)])
      let expectedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Option"), [vectorType])
      validateRuntimeValueType(runtime.value, expectedType, runtime.globals)
      let decoded = valueToOption(runtime.value, runtime.globals, "Option",
        proc(item: Value, globals: Globals): seq[RuntimeStructuredVariant] =
          vecValueToSeq[RuntimeStructuredVariant](item, 2, globals, "Vec",
            proc(element: Value, elementGlobals: Globals):
                RuntimeStructuredVariant =
              valueToRuntimeStructuredVariant(element, elementGlobals,
                "SizedTree", ["sizedTree"])))
      let wrongIndexCallback:
          proc(value: Option[seq[RuntimeStructuredVariant]]):
            Option[seq[RuntimeStructuredVariant]] {.closure.} =
        proc(value: Option[seq[RuntimeStructuredVariant]]):
            Option[seq[RuntimeStructuredVariant]] =
          if value.isNone: return none[seq[RuntimeStructuredVariant]]()
          var changed = value.get
          inc changed[0].arguments[0].natValue
          some(changed)
      var typedMismatchRejected = false
      try:
        discard importedGenericIndexedNestedOptionVectorCallbackApply(
          wrongIndexCallback, value)
      except ValueError:
        typedMismatchRejected = true
      var runtimeMismatchRejected = false
      try:
        discard importedGenericIndexedNestedOptionVectorCallbackApplyRuntimeValue(
          wrongIndexCallback, value)
      except ValueError:
        runtimeMismatchRejected = true
      let noneValue = none[seq[RuntimeStructuredVariant]]()
      var noneRejected = false
      try:
        discard importedGenericIndexedNestedOptionVectorCallbackApply(
          callback, noneValue)
      except ValueError as error:
        noneRejected = "cannot infer indexed Eponym type argument" in error.msg
      var noneRuntimeRejected = false
      try:
        discard importedGenericIndexedNestedOptionVectorCallbackApplyRuntimeValue(
          callback, noneValue)
      except ValueError as error:
        noneRuntimeRejected = "cannot infer indexed Eponym type argument" in error.msg
      var emptyRejected = false
      try:
        discard importedGenericIndexedNestedOptionVectorCallbackApply(
          callback, some(newSeq[RuntimeStructuredVariant]()))
      except ValueError as error:
        emptyRejected = "length mismatch" in error.msg
      var emptyWitnessRejected = false
      try:
        discard importedGenericIndexedEmptyOptionVectorCallbackApply(
          callback, some(newSeq[RuntimeStructuredVariant]()))
      except ValueError as error:
        emptyWitnessRejected = "empty sequence" in error.msg
      var emptyRuntimeWitnessRejected = false
      try:
        discard importedGenericIndexedEmptyOptionVectorCallbackApplyRuntimeValue(
          callback, some(newSeq[RuntimeStructuredVariant]()))
      except ValueError as error:
        emptyRuntimeWitnessRejected = "empty sequence" in error.msg
      let vectorValue = @[tree(length), tree(length)]
      let vectorCallback: proc(value: seq[RuntimeStructuredVariant]):
          seq[RuntimeStructuredVariant] {.closure.} =
        proc(value: seq[RuntimeStructuredVariant]):
            seq[RuntimeStructuredVariant] = value
      let vectorTyped = importedGenericIndexedVectorCallbackApply(
        vectorCallback, vectorValue)
      let vectorRuntime = importedGenericIndexedVectorCallbackApplyRuntimeValue(
        vectorCallback, vectorValue)
      let vectorExpectedType = callRuntimeValue(
        runtimeGlobalValue(vectorRuntime.globals, "Vec"),
        [treeType, natToValue(2, vectorRuntime.globals)])
      validateRuntimeValueType(vectorRuntime.value, vectorExpectedType,
        vectorRuntime.globals)
      let wrongVectorCallback:
          proc(value: seq[RuntimeStructuredVariant]):
            seq[RuntimeStructuredVariant] {.closure.} =
        proc(value: seq[RuntimeStructuredVariant]):
            seq[RuntimeStructuredVariant] =
          result = value
          inc result[0].arguments[0].natValue
      var vectorMismatchRejected = false
      try:
        discard importedGenericIndexedVectorCallbackApply(wrongVectorCallback,
          vectorValue)
      except ValueError:
        vectorMismatchRejected = true
      var vectorRuntimeMismatchRejected = false
      try:
        discard importedGenericIndexedVectorCallbackApplyRuntimeValue(
          wrongVectorCallback, vectorValue)
      except ValueError:
        vectorRuntimeMismatchRejected = true
      var emptyDirectVectorRejected = false
      try:
        discard importedGenericIndexedEmptyVectorCallbackApply(vectorCallback,
          newSeq[RuntimeStructuredVariant]())
      except ValueError as error:
        emptyDirectVectorRejected = "empty sequence" in error.msg
      var emptyDirectVectorRuntimeRejected = false
      try:
        discard importedGenericIndexedEmptyVectorCallbackApplyRuntimeValue(
          vectorCallback, newSeq[RuntimeStructuredVariant]())
      except ValueError as error:
        emptyDirectVectorRuntimeRejected = "empty sequence" in error.msg
      var decodedIndicesMatch = decoded.isSome and decoded.get.len == 2
      if decodedIndicesMatch:
        for item in decoded.get:
          if item.arguments[0].natValue != length:
            decodedIndicesMatch = false
      if not (typed.isSome and typed.get.len == 2 and decodedIndicesMatch and
          typedMismatchRejected and runtimeMismatchRejected and noneRejected and
          noneRuntimeRejected and emptyRejected and emptyWitnessRejected and
          emptyRuntimeWitnessRejected and vectorMismatchRejected and
          vectorRuntimeMismatchRejected and emptyDirectVectorRejected and
          emptyDirectVectorRuntimeRejected):
        echo "nested indexed Option/Vec property failed at length ", length
      typed.isSome and typed.get.len == 2 and
        decodedIndicesMatch and
        typedMismatchRejected and runtimeMismatchRejected and noneRejected and
        noneRuntimeRejected and emptyRejected and emptyWitnessRejected and
        emptyRuntimeWitnessRejected and vectorTyped.len == 2 and
        vectorMismatchRejected and vectorRuntimeMismatchRejected and
        emptyDirectVectorRejected and emptyDirectVectorRuntimeRejected,
    shrinkInt)
  if not nestedIndexedOptionCallbackCases:
    quit(1)
  let indexedListCallbackCases = forAll(
    "generic callbacks infer indexed witnesses from nonempty Lists", r, 50,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      proc tree(index: int): RuntimeStructuredVariant =
        RuntimeStructuredVariant(constructor: "sizedTree", arguments: @[
          RuntimeStructuredValue(kind: rsvNat, natValue: index),
          RuntimeStructuredValue(kind: rsvVariant,
            variantValue: RuntimeStructuredVariant(
              constructor: "treeEmpty"))])
      let value = @[tree(length), tree(length)]
      let callback: proc(value: seq[RuntimeStructuredVariant]):
          seq[RuntimeStructuredVariant] {.closure.} =
        proc(value: seq[RuntimeStructuredVariant]):
            seq[RuntimeStructuredVariant] = value
      let typed = importedGenericIndexedListCallbackApply(callback, value)
      let runtime = importedGenericIndexedListCallbackApplyRuntimeValue(
        callback, value)
      let treeType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "SizedTree"),
        [natToValue(length, runtime.globals)])
      let expectedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "List"), [treeType])
      validateRuntimeValueType(runtime.value, expectedType, runtime.globals)
      let decoded = listValueToSeq[RuntimeStructuredVariant](runtime.value,
        runtime.globals, "List",
        proc(item: Value, globals: Globals): RuntimeStructuredVariant =
          valueToRuntimeStructuredVariant(item, globals, "SizedTree",
            ["sizedTree"]))
      let wrongIndexCallback:
          proc(value: seq[RuntimeStructuredVariant]):
            seq[RuntimeStructuredVariant] {.closure.} =
        proc(value: seq[RuntimeStructuredVariant]):
            seq[RuntimeStructuredVariant] =
          result = value
          inc result[0].arguments[0].natValue
      var typedMismatchRejected = false
      try:
        discard importedGenericIndexedListCallbackApply(wrongIndexCallback,
          value)
      except ValueError:
        typedMismatchRejected = true
      var runtimeMismatchRejected = false
      try:
        discard importedGenericIndexedListCallbackApplyRuntimeValue(
          wrongIndexCallback, value)
      except ValueError:
        runtimeMismatchRejected = true
      var emptyRejected = false
      try:
        discard importedGenericIndexedListCallbackApply(callback,
          newSeq[RuntimeStructuredVariant]())
      except ValueError as error:
        emptyRejected = "empty sequence" in error.msg
      var emptyRuntimeRejected = false
      try:
        discard importedGenericIndexedListCallbackApplyRuntimeValue(callback,
          newSeq[RuntimeStructuredVariant]())
      except ValueError as error:
        emptyRuntimeRejected = "empty sequence" in error.msg
      typed.len == 2 and decoded.len == 2 and
        decoded[0].arguments[0].natValue == length and
        decoded[1].arguments[0].natValue == length and
        typedMismatchRejected and runtimeMismatchRejected and emptyRejected and
        emptyRuntimeRejected,
    shrinkInt)
  if not indexedListCallbackCases:
    quit(1)
  let indexedOptionListCallbackCases = forAll(
    "generic callbacks infer indexed witnesses from nonempty Option Lists",
    r, 50,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      proc tree(index: int): RuntimeStructuredVariant =
        RuntimeStructuredVariant(constructor: "sizedTree", arguments: @[
          RuntimeStructuredValue(kind: rsvNat, natValue: index),
          RuntimeStructuredValue(kind: rsvVariant,
            variantValue: RuntimeStructuredVariant(
              constructor: "treeEmpty"))])
      let value = some(@[tree(length), tree(length)])
      let callback:
          proc(value: Option[seq[RuntimeStructuredVariant]]):
            Option[seq[RuntimeStructuredVariant]] {.closure.} =
        proc(value: Option[seq[RuntimeStructuredVariant]]):
            Option[seq[RuntimeStructuredVariant]] = value
      let typed = importedGenericIndexedOptionListCallbackApply(callback,
        value)
      let runtime = importedGenericIndexedOptionListCallbackApplyRuntimeValue(
        callback, value)
      let treeType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "SizedTree"),
        [natToValue(length, runtime.globals)])
      let listType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "List"), [treeType])
      let expectedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Option"), [listType])
      validateRuntimeValueType(runtime.value, expectedType, runtime.globals)
      var mismatchRejected = false
      let wrongCallback:
          proc(value: Option[seq[RuntimeStructuredVariant]]):
            Option[seq[RuntimeStructuredVariant]] {.closure.} =
        proc(value: Option[seq[RuntimeStructuredVariant]]):
            Option[seq[RuntimeStructuredVariant]] =
          if value.isNone: return none[seq[RuntimeStructuredVariant]]()
          var changed = value.get
          inc changed[0].arguments[0].natValue
          some(changed)
      try:
        discard importedGenericIndexedOptionListCallbackApply(wrongCallback,
          value)
      except ValueError:
        mismatchRejected = true
      var runtimeMismatchRejected = false
      try:
        discard importedGenericIndexedOptionListCallbackApplyRuntimeValue(
          wrongCallback, value)
      except ValueError:
        runtimeMismatchRejected = true
      var noneRejected = false
      try:
        discard importedGenericIndexedOptionListCallbackApply(callback,
          none[seq[RuntimeStructuredVariant]]())
      except ValueError as error:
        noneRejected = "cannot infer indexed Eponym type argument" in error.msg
      var emptyRejected = false
      try:
        discard importedGenericIndexedOptionListCallbackApply(callback,
          some(newSeq[RuntimeStructuredVariant]()))
      except ValueError as error:
        emptyRejected = "empty sequence" in error.msg
      typed.isSome and mismatchRejected and runtimeMismatchRejected and
        noneRejected and emptyRejected,
    shrinkInt)
  if not indexedOptionListCallbackCases:
    quit(1)
  let rawAppliedGenericTypeCases = forAll(
    "raw Values for applied generic domains are type checked", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let tree = runtimeVariantToValue(RuntimeVariant(
        constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
        runtimeTreeConstructors)
      let indexed = runtimeVariantToValue(RuntimeVariant(
        constructor: "sizedTree",
        arguments: @[natToValue(length, variantGlobals), tree]),
        variantGlobals, "SizedTree", ["sizedTree"])
      let runtimeResult = genericUnmappedSizedTreeProjectionRuntimeValueRaw(
        [natToValue(length, variantGlobals), indexed], [intToValue(0)])
      let ordinaryRuntimeResult = generatedSizedTreeRawIdentityRuntimeValue(
        [natToValue(length, variantGlobals), indexed])
      var wrongOrdinaryIndexRejected = false
      try:
        let wrongIndexed = runtimeVariantToValue(RuntimeVariant(
          constructor: "sizedTree",
          arguments: @[natToValue(length + 1, variantGlobals), tree]),
          variantGlobals, "SizedTree", ["sizedTree"])
        discard generatedSizedTreeRawIdentityRuntimeValue(
          [natToValue(length, variantGlobals), wrongIndexed])
      except ValueError:
        wrongOrdinaryIndexRejected = true
      let decoded = valueToRuntimeVariant(runtimeResult.value,
        runtimeResult.globals,
        "SizedTree", ["sizedTree"])
      let ordinaryDecoded = valueToRuntimeVariant(ordinaryRuntimeResult.value,
        ordinaryRuntimeResult.globals, "SizedTree", ["sizedTree"])
      valueToNat(decoded.arguments[0], runtimeResult.globals) == length and
        decoded.arguments[1].whnfRefId == tree.whnfRefId and
        valueToNat(ordinaryDecoded.arguments[0],
          ordinaryRuntimeResult.globals) == length and
        wrongOrdinaryIndexRejected,
    shrinkInt)
  if not rawAppliedGenericTypeCases:
    quit(1)
  var appliedGenericIndexRejected = false
  try:
    let tree = runtimeVariantToValue(RuntimeVariant(
      constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
      runtimeTreeConstructors)
    let wrongIndexedTree = runtimeVariantToValue(RuntimeVariant(
      constructor: "sizedTree",
      arguments: @[natToValue(4, variantGlobals), tree]), variantGlobals,
      "SizedTree", ["sizedTree"])
    discard genericIndexedTreeProjectionRuntimeValueDynamic(3,
      valueToRuntimeStructuredVariant(wrongIndexedTree, variantGlobals,
        "SizedTree", ["sizedTree"]), 0)
  except ValueError:
    appliedGenericIndexRejected = true
  doAssert appliedGenericIndexRejected
  var rawAppliedGenericIndexRejected = false
  try:
    let tree = runtimeVariantToValue(RuntimeVariant(
      constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
      runtimeTreeConstructors)
    let wrongIndexedTree = runtimeVariantToValue(RuntimeVariant(
      constructor: "sizedTree",
      arguments: @[natToValue(4, variantGlobals), tree]), variantGlobals,
      "SizedTree", ["sizedTree"])
    discard genericUnmappedSizedTreeProjectionRuntimeValueRaw(
      [natToValue(3, variantGlobals), wrongIndexedTree], [intToValue(0)])
  except ValueError:
    rawAppliedGenericIndexRejected = true
  doAssert rawAppliedGenericIndexRejected
  var variantArityRejected = false
  try:
    discard runtimeVariantToValue(RuntimeVariant(
      constructor: "treeNode", arguments: @[intToValue(1)]),
      variantGlobals, "RuntimeTree", runtimeTreeConstructors)
  except ValueError as error:
    variantArityRejected = "expects 2 arguments" in error.msg
  doAssert variantArityRejected
  var variantFamilyRejected = false
  try:
    validateRuntimeVariantConstructors(variantGlobals, "RuntimeTree",
      ["treeEmpty", "otherTree"])
  except ValueError as error:
    variantFamilyRejected = "does not return family" in error.msg
  doAssert variantFamilyRejected

  let importedRuntimeCases = forAll(
    "raw runtimeValue access reaches imported checked definitions", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let runtime = importedIdentityRuntimeValue([intToValue(value)])
      let typedRuntime = importedIdentityRuntimeValue(value)
      importedIdentity(value) == value and
        typedRuntime.value.whnfKind == wInt and
        typedRuntime.value.whnfIntVal == value and
        runtime.value.whnfKind == wInt and runtime.value.whnfIntVal == value,
    shrinkInt)
  if not importedRuntimeCases:
    quit(1)

  let importedDependentVectorCases = forAll(
    "typed imported wrappers carry dependent Vec indices", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let values = makeIndexedRuntimeValues(length)
      let direct = importedVectorIdentity(length, values)
      let runtime = importedVectorIdentityRuntimeValue(length, values)
      let rawRuntime = importedVectorIdentityRuntimeValue(
        [natToValue(length, runtime.globals),
         runtimeIntVector(values, runtime.globals)])
      let decoded = vecValueToSeq[int](runtime.value, length, runtime.globals,
        "Vec", proc(item: Value, _: Globals): int = valueToInt(item))
      let decodedRaw = vecValueToSeq[int](rawRuntime.value, length,
        rawRuntime.globals, "Vec",
        proc(item: Value, _: Globals): int = valueToInt(item))
      direct == values and decoded == values and decodedRaw == values,
    shrinkInt)
  if not importedDependentVectorCases:
    quit(1)
  let importedGenericRawCases = forAll(
    "imported generic raw signatures validate type and value arguments", r,
    200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let globals = importedIntIdentityRuntimeValue(n).globals
      let intType = runtimeGlobalValue(globals, "Int")
      let runtime = importedGenericIdentityRuntimeValueRaw(
        [intType, intToValue(n)])
      let implicitRaw = importedImplicitGenericIdentityRuntimeValueRaw(
        [intType, intToValue(n)])
      let typed = importedGenericIdentity(n)
      let implicit = importedImplicitGenericIdentity(n)
      let typedRuntime = importedGenericIdentityRuntimeValue(n)
      let implicitRuntime = importedImplicitGenericIdentityRuntimeValue(n)
      typed == n and implicit == n and
        valueToHost[int](typedRuntime.value) == n and
        valueToHost[int](implicitRuntime.value) == n and
        valueToInt(runtime.value) == n and
        valueToInt(implicitRaw.value) == n,
    shrinkInt)
  if not importedGenericRawCases:
    quit(1)
  let importedGenericCallbackCases = forAll(
    "imported generic definitions adapt mapped Nim callbacks", r, 200,
    proc(r: var Rng): bool = r.genBool,
    proc(useRed: bool): bool =
      let value = if useRed: importedTokenRed else: importedTokenBlue
      let expected = if useRed: importedTokenBlue else: importedTokenRed
      let callback: proc(value: ImportedToken): ImportedToken {.closure.} =
        proc(value: ImportedToken): ImportedToken =
          if value == importedTokenRed: importedTokenBlue
          else: importedTokenRed
      let typed = importedGenericCallbackApply(callback, value)
      let runtime = importedGenericCallbackApplyRuntimeValue(callback, value)
      typed == expected and
        valueToHost[ImportedToken](runtime.value) == expected)
  if not importedGenericCallbackCases:
    quit(1)
  let importedGenericCodecCallbackCases = forAll(
    "imported generic callbacks use custom runtimeCodec mappings", r, 200,
    proc(r: var Rng): tuple[id, delta: int, label, suffix: string] =
      (r.genInt(-1000, 1000), r.genInt(-100, 100), "handle", "-mapped"),
    proc(input: tuple[id, delta: int, label, suffix: string]): bool =
      let value = ChannelHandle(id: input.id, label: input.label)
      let callback: proc(value: ChannelHandle): ChannelHandle {.closure.} =
        proc(value: ChannelHandle): ChannelHandle =
          ChannelHandle(id: value.id + input.delta,
            label: value.label & input.suffix)
      let expected = callback(value)
      let typed = importedGenericCallbackApply(callback, value)
      let runtime = importedGenericCallbackApplyRuntimeValue(callback, value)
      typed == expected and
        valueToHost[ChannelHandle](runtime.value) == expected)
  if not importedGenericCodecCallbackCases:
    quit(1)
  let importedGenericOptionCallbackCases = forAll(
    "imported generic callbacks recurse through Option codecs", r, 200,
    proc(r: var Rng): tuple[present: bool, value, delta: int] =
      (r.genBool(), r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[present: bool, value, delta: int]): bool =
      let value = if input.present: some(input.value) else: none(int)
      let callback: proc(value: Option[int]): Option[int] {.closure.} =
        proc(value: Option[int]): Option[int] =
          if value.isSome: some(value.get + input.delta) else: none(int)
      let expected = callback(value)
      let typed = importedGenericCallbackApply(callback, value)
      let runtime = importedGenericCallbackApplyRuntimeValue(callback, value)
      typed == expected and valueToHost[Option[int]](runtime.value) == expected)
  if not importedGenericOptionCallbackCases:
    quit(1)
  let importedGenericDependentVectorCallbackCases = forAll(
    "imported generic callbacks preserve dependent Vec indices", r, 200,
    proc(r: var Rng): tuple[length, seed, delta: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[length, seed, delta: int]): bool =
      var values: seq[ChannelHandle] = @[]
      var expected: seq[ChannelHandle] = @[]
      for i in 0 ..< input.length:
        let item = ChannelHandle(id: input.seed + i, label: "generic-vec")
        values.add(item)
        expected.add(ChannelHandle(id: item.id + input.delta,
          label: "decoded-" & $(item.id + input.delta)))
      let callback: proc(length: int, values: seq[ChannelHandle]):
          seq[ChannelHandle] {.closure.} =
        proc(length: int, values: seq[ChannelHandle]): seq[ChannelHandle] =
          var mapped: seq[ChannelHandle] = @[]
          for item in values:
            mapped.add(ChannelHandle(id: item.id + input.delta,
              label: item.label & "/mapped"))
          mapped
      let typed = importedGenericDependentVectorCallbackApply(callback,
        input.length, values)
      let runtime = importedGenericDependentVectorCallbackApplyRuntimeValue(
        callback, input.length, values)
      typed == expected and
        vecValueToSeq[ChannelHandle](runtime.value, input.length,
          runtime.globals, "Vec", decodeRuntimeHandle) == expected)
  if not importedGenericDependentVectorCallbackCases:
    quit(1)
  let importedGenericOptionContainerCallbackCases = forAll(
    "imported generic callbacks preserve Option custom codecs", r, 200,
    proc(r: var Rng): tuple[present: bool, seed, delta: int] =
      (r.genBool(), r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[present: bool, seed, delta: int]): bool =
      let value = if input.present:
        some(ChannelHandle(id: input.seed, label: "option-input"))
      else: none(ChannelHandle)
      let expected = if input.present:
        some(ChannelHandle(id: input.seed + input.delta,
          label: "decoded-" & $(input.seed + input.delta)))
      else: none(ChannelHandle)
      let callback: proc(value: Option[ChannelHandle]): Option[ChannelHandle]
          {.closure.} =
        proc(value: Option[ChannelHandle]): Option[ChannelHandle] =
          if value.isSome:
            some(ChannelHandle(id: value.get.id + input.delta,
              label: value.get.label & "/mapped"))
          else:
            none(ChannelHandle)
      let typed = importedGenericOptionCallbackApply(callback, value)
      let runtime = importedGenericOptionCallbackApplyRuntimeValue(callback,
        value)
      typed == expected and
        valueToOption[ChannelHandle](runtime.value, runtime.globals, "Option",
          decodeRuntimeHandle) == expected)
  if not importedGenericOptionContainerCallbackCases:
    quit(1)
  let importedGenericNestedOptionVectorCallbackCases = forAll(
    "imported generic callbacks compose Option and Vec codecs", r, 200,
    proc(r: var Rng): tuple[first, second, delta: int, present: bool] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000),
       r.genInt(-100, 100), r.genBool),
    proc(input: tuple[first, second, delta: int, present: bool]): bool =
      let value = if input.present:
        some(@[
          ChannelHandle(id: input.first, label: "nested-first"),
          ChannelHandle(id: input.second, label: "nested-second")])
        else: none[seq[ChannelHandle]]()
      let expected = if input.present:
        some(@[
          ChannelHandle(id: input.first + input.delta,
            label: "decoded-" & $(input.first + input.delta)),
          ChannelHandle(id: input.second + input.delta,
            label: "decoded-" & $(input.second + input.delta))])
        else: none[seq[ChannelHandle]]()
      let callback: proc(value: Option[seq[ChannelHandle]]):
          Option[seq[ChannelHandle]] {.closure.} =
        proc(value: Option[seq[ChannelHandle]]):
            Option[seq[ChannelHandle]] =
          if value.isNone: return none[seq[ChannelHandle]]()
          var updated = value.get
          for item in updated.mitems:
            inc item.id, input.delta
            item.label.add("/nested")
          some(updated)
      let typed = importedGenericNestedOptionVectorCallbackApply[
        ChannelHandle](callback, value)
      let runtime = importedGenericNestedOptionVectorCallbackApplyRuntimeValue[
        ChannelHandle](callback, value)
      let runtimeElementType = runtimeGlobalValue(runtime.globals,
        "RuntimeHandle")
      let expectedVecType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Vec"),
        [runtimeElementType, natToValue(2, runtime.globals)])
      let expectedOptionType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Option"), [expectedVecType])
      validateRuntimeValueType(runtime.value, expectedOptionType,
        runtime.globals)
      let decoded = valueToOption(runtime.value, runtime.globals, "Option",
        proc(item: Value, globals: Globals): seq[ChannelHandle] =
          vecValueToSeq[ChannelHandle](item, 2, globals, "Vec",
            decodeRuntimeHandle))
      typed == expected and decoded == expected,
    proc(input: tuple[first, second, delta: int, present: bool]):
        seq[tuple[first, second, delta: int, present: bool]] = @[])
  if not importedGenericNestedOptionVectorCallbackCases:
    quit(1)
  let importedGenericListContainerCallbackCases = forAll(
    "imported generic callbacks preserve List custom codecs", r, 200,
    proc(r: var Rng): tuple[length, seed, delta: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[length, seed, delta: int]): bool =
      var value: seq[ChannelHandle] = @[]
      var expected: seq[ChannelHandle] = @[]
      for i in 0 ..< input.length:
        value.add(ChannelHandle(id: input.seed + i, label: "list-input"))
        expected.add(ChannelHandle(id: input.seed + i + input.delta,
          label: "decoded-" & $(input.seed + i + input.delta)))
      let callback: proc(value: seq[ChannelHandle]): seq[ChannelHandle]
          {.closure.} =
        proc(value: seq[ChannelHandle]): seq[ChannelHandle] =
          var mapped: seq[ChannelHandle] = @[]
          for item in value:
            mapped.add(ChannelHandle(id: item.id + input.delta,
              label: item.label & "/mapped"))
          mapped
      let typed = importedGenericListCallbackApply(callback, value)
      let runtime = importedGenericListCallbackApplyRuntimeValue(callback,
        value)
      typed == expected and
        listValueToSeq[ChannelHandle](runtime.value, runtime.globals, "List",
          decodeRuntimeHandle) == expected)
  if not importedGenericListContainerCallbackCases:
    quit(1)
  let importedGenericSigmaCallbackCases = forAll(
    "imported generic callbacks preserve Sigma custom codecs", r, 200,
    proc(r: var Rng): tuple[left, right, delta: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[left, right, delta: int]): bool =
      let value = (ChannelHandle(id: input.left, label: "sigma-left"),
        ChannelHandle(id: input.right, label: "sigma-right"))
      let expected = (
        ChannelHandle(id: input.left + input.delta,
          label: "decoded-" & $(input.left + input.delta)),
        ChannelHandle(id: input.right + input.delta,
          label: "decoded-" & $(input.right + input.delta)))
      let callback: proc(value: tuple[left, right: ChannelHandle]):
          tuple[left, right: ChannelHandle] {.closure.} =
        proc(value: tuple[left, right: ChannelHandle]):
            tuple[left, right: ChannelHandle] =
          (ChannelHandle(id: value[0].id + input.delta,
             label: value[0].label & "/mapped"),
           ChannelHandle(id: value[1].id + input.delta,
             label: value[1].label & "/mapped"))
      let typed = importedGenericSigmaCallbackApply(callback, value)
      let runtime = importedGenericSigmaCallbackApplyRuntimeValue(callback,
        value)
      let first = decodeRuntimeHandle(runtimePairFirst(runtime.value),
        runtime.globals)
      let second = decodeRuntimeHandle(runtimePairSecond(runtime.value),
        runtime.globals)
      typed == expected and (first, second) == expected)
  if not importedGenericSigmaCallbackCases:
    quit(1)
  let importedGenericDependentPairCallbackCases = forAll(
    "imported generic callbacks preserve dependent Sigma Vec indices", r, 200,
    proc(r: var Rng): tuple[length, seed, delta: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[length, seed, delta: int]): bool =
      var values: seq[ChannelHandle] = @[]
      var expected: seq[ChannelHandle] = @[]
      for i in 0 ..< input.length:
        values.add(ChannelHandle(id: input.seed + i, label: "pair-input"))
        expected.add(ChannelHandle(id: input.seed + i + input.delta,
          label: "decoded-" & $(input.seed + i + input.delta)))
      let value = (input.length, values)
      let expectedPair = (input.length, expected)
      let callback: proc(value: tuple[length: int,
          values: seq[ChannelHandle]]): tuple[length: int,
          values: seq[ChannelHandle]] {.closure.} =
        proc(value: tuple[length: int, values: seq[ChannelHandle]]):
            tuple[length: int, values: seq[ChannelHandle]] =
          var mapped: seq[ChannelHandle] = @[]
          for item in value.values:
            mapped.add(ChannelHandle(id: item.id + input.delta,
              label: item.label & "/mapped"))
          (value.length, mapped)
      let typed = importedGenericDependentPairCallbackApply[ChannelHandle](
        callback, value)
      let runtime = importedGenericDependentPairCallbackApplyRuntimeValue[
        ChannelHandle](callback, value)
      var wrongLengthRejected = false
      try:
        discard importedGenericDependentPairCallbackApply[ChannelHandle](
          callback, (input.length + 1, values))
      except ValueError:
        wrongLengthRejected = true
      var wrongRuntimeInputRejected = false
      try:
        discard importedGenericDependentPairCallbackApplyRuntimeValue[
          ChannelHandle](callback, (input.length + 1, values))
      except ValueError:
        wrongRuntimeInputRejected = true
      let badCallback: proc(value: tuple[length: int,
          values: seq[ChannelHandle]]): tuple[length: int,
          values: seq[ChannelHandle]] {.closure.} =
        proc(value: tuple[length: int, values: seq[ChannelHandle]]):
            tuple[length: int, values: seq[ChannelHandle]] =
          (value.length + 1, value.values)
      var wrongCallbackResultRejected = false
      try:
        discard importedGenericDependentPairCallbackApply[ChannelHandle](
          badCallback, value)
      except ValueError:
        wrongCallbackResultRejected = true
      var wrongRuntimeCallbackResultRejected = false
      try:
        discard importedGenericDependentPairCallbackApplyRuntimeValue[
          ChannelHandle](badCallback, value)
      except ValueError:
        wrongRuntimeCallbackResultRejected = true
      typed == expectedPair and wrongLengthRejected and
        wrongRuntimeInputRejected and wrongCallbackResultRejected and
        wrongRuntimeCallbackResultRejected and
        valueToNat(runtimePairFirst(runtime.value), runtime.globals) ==
          input.length and
        vecValueToSeq[ChannelHandle](runtimePairSecond(runtime.value),
          input.length, runtime.globals, "Vec", decodeRuntimeHandle) ==
            expected)
  if not importedGenericDependentPairCallbackCases:
    quit(1)
  let importedGenericExplicitScalarMappingCases = forAll(
    "explicit unique scalar mappings reify generic runtime types", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let typed = importedGenericSingleton(value)
      let runtime = importedGenericSingletonRuntimeValue(value)
      typed == @[value] and
        vecValueToSeq[int](runtime.value, 1, runtime.globals, "Vec",
          decodeRuntimeScalar) == @[value])
  if not importedGenericExplicitScalarMappingCases:
    quit(1)
  let importedGenericStructuredVariantCallbackCases = forAll(
    "imported generic callbacks preserve data-variant leaf codecs", r, 200,
    proc(r: var Rng): tuple[id, delta: int] =
      (r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[id, delta: int]): bool =
      let typeArgument = RuntimeStructuredValue(kind: rsvRaw,
        rawValue: runtimeGlobalValue(importedGenericVariantGlobals,
          "RuntimeHandle"))
      let value = RuntimeStructuredVariant(constructor: "runtimeBox",
        arguments: @[typeArgument,
          runtimeStructuredOpaque(ChannelHandle(id: input.id,
            label: "variant-input"))])
      let expected = RuntimeStructuredVariant(constructor: "runtimeBox",
        arguments: @[typeArgument,
          runtimeStructuredOpaque(ChannelHandle(id: input.id + input.delta,
            label: "decoded-" & $(input.id + input.delta)))])
      let callback: proc(value: RuntimeStructuredVariant):
          RuntimeStructuredVariant {.closure.} =
        proc(value: RuntimeStructuredVariant): RuntimeStructuredVariant =
          let handle = runtimeStructuredOpaqueAs[ChannelHandle](
            value.arguments[1])
          RuntimeStructuredVariant(constructor: "runtimeBox",
            arguments: @[value.arguments[0], runtimeStructuredOpaque(
              ChannelHandle(id: handle.id + input.delta,
                label: handle.label & "/mapped"))])
      let typed = importedGenericBoxCallbackApply[ChannelHandle](callback,
        value)
      let runtime = importedGenericBoxCallbackApplyRuntimeValue[ChannelHandle](
        callback, value)
      let decoded = valueToRuntimeStructuredVariant(runtime.value,
        runtime.globals, "RuntimeBox", ["runtimeBox"],
        [runtimeStructuredCustomCodec[ChannelHandle]("RuntimeHandle",
          encodeRuntimeHandle, decodeRuntimeHandle)])
      typed.constructor == expected.constructor and
        runtimeStructuredOpaqueAs[ChannelHandle](typed.arguments[1]) ==
          runtimeStructuredOpaqueAs[ChannelHandle](expected.arguments[1]) and
        runtimeStructuredOpaqueAs[ChannelHandle](decoded.arguments[1]) ==
          runtimeStructuredOpaqueAs[ChannelHandle](expected.arguments[1]))
  if not importedGenericStructuredVariantCallbackCases:
    quit(1)
  let importedGenericArrayCallbackCases = forAll(
    "imported generic callbacks preserve fixed-array Vec codecs", r, 200,
    proc(r: var Rng): tuple[first, second, delta: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[first, second, delta: int]): bool =
      let value = [
        ChannelHandle(id: input.first, label: "array-first"),
        ChannelHandle(id: input.second, label: "array-second")]
      let expected = [
        ChannelHandle(id: input.first + input.delta,
          label: "decoded-" & $(input.first + input.delta)),
        ChannelHandle(id: input.second + input.delta,
          label: "decoded-" & $(input.second + input.delta))]
      let callback: proc(value: array[2, ChannelHandle]):
          array[2, ChannelHandle] {.closure.} =
        proc(value: array[2, ChannelHandle]): array[2, ChannelHandle] =
          [
            ChannelHandle(id: value[0].id + input.delta,
              label: value[0].label & "/mapped"),
            ChannelHandle(id: value[1].id + input.delta,
              label: value[1].label & "/mapped")]
      let typed = importedGenericArrayCallbackApply[ChannelHandle](callback,
        value)
      let runtime = importedGenericArrayCallbackApplyRuntimeValue[
        ChannelHandle](callback, value)
      typed == expected and
        vecValueToArray[2, ChannelHandle](runtime.value, 2, runtime.globals,
          "Vec", decodeRuntimeHandle) == expected)
  if not importedGenericArrayCallbackCases:
    quit(1)
  let importedImplicitNatVecCases = forAll(
    "imported implicit Nat binders have static and dynamic Nim wrappers",
    r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var expected: seq[int] = @[]
      for i in 0 ..< input.length:
        expected.add(input.seed + i)
      let typed = importedImplicitNatVecIdentityDynamic(input.length, expected)
      let runtime = importedImplicitNatVecIdentityRuntimeValueDynamic(
        input.length, expected)
      let globals = runtime.globals
      let raw = importedImplicitNatVecIdentityRuntimeValueRaw([
        natToValue(input.length, globals),
        runtimeIntVector(expected, globals)])
      let decoded = vecValueToSeq[int](runtime.value, input.length, globals,
        "Vec", proc(value: Value, globals: Globals): int = valueToInt(value))
      let rawDecoded = vecValueToSeq[int](raw.value, input.length,
        raw.globals, "Vec",
        proc(value: Value, globals: Globals): int = valueToInt(value))
      typed == expected and decoded == expected and rawDecoded == expected,
    proc(input: tuple[length, seed: int]):
        seq[tuple[length, seed: int]] =
      @[(0, input.seed), (input.length div 2, input.seed),
        (input.length, 0)])
  if not importedImplicitNatVecCases:
    quit(1)
  var importedImplicitNatVecMismatchRejected = false
  try:
    discard importedImplicitNatVecIdentityDynamic(2, @[1])
  except ValueError:
    importedImplicitNatVecMismatchRejected = true
  var importedImplicitNatVecRawMismatchRejected = false
  try:
    let globals = importedIntIdentityRuntimeValue(0).globals
    discard importedImplicitNatVecIdentityRuntimeValueRaw([
      natToValue(2, globals), runtimeIntVector(@[1], globals)])
  except ValueError:
    importedImplicitNatVecRawMismatchRejected = true
  doAssert importedImplicitNatVecMismatchRejected and
    importedImplicitNatVecRawMismatchRejected
  let importedImplicitScalarCases = forAll(
    "imported implicit Bool, Int, and mapped binders bridge to Nim",
    r, 200,
    proc(r: var Rng): tuple[flag: bool, number: int] =
      (r.genBool(), r.genInt(-1000, 1000)),
    proc(input: tuple[flag: bool, number: int]): bool =
      let globals = importedIntIdentityRuntimeValue(0).globals
      let boolStatic = importedImplicitBoolIdentity[true]()
      let boolStaticRuntime = importedImplicitBoolIdentityRuntimeValue[false]()
      let tokenStatic = importedImplicitTokenIdentity[importedTokenRed]()
      let tokenStaticRuntime =
        importedImplicitTokenIdentityRuntimeValue[importedTokenBlue]()
      let boolDynamic = importedImplicitBoolIdentityDynamic(input.flag)
      let boolRuntime = importedImplicitBoolIdentityRuntimeValueDynamic(
        input.flag)
      let boolRaw = importedImplicitBoolIdentityRuntimeValueRaw(
        [boolToValue(input.flag, globals)])
      let intDynamic = importedImplicitIntIdentityDynamic(input.number)
      let intRuntime = importedImplicitIntIdentityRuntimeValueDynamic(
        input.number)
      let intRaw = importedImplicitIntIdentityRuntimeValueRaw(
        [intToValue(input.number)])
      let token = if input.flag: importedTokenBlue else: importedTokenRed
      let tokenDynamic = importedImplicitTokenIdentityDynamic(token)
      let tokenRuntime = importedImplicitTokenIdentityRuntimeValueDynamic(token)
      let tokenRaw = importedImplicitTokenIdentityRuntimeValueRaw(
        [tokenRuntime.value])
      boolStatic and
        not valueToBool(boolStaticRuntime.value, boolStaticRuntime.globals) and
        tokenStatic == importedTokenRed and
        valueToHost[ImportedToken](tokenStaticRuntime.value) == importedTokenBlue and
        boolDynamic == input.flag and
        valueToBool(boolRuntime.value, boolRuntime.globals) == input.flag and
        valueToBool(boolRaw.value, boolRaw.globals) == input.flag and
        intDynamic == input.number and valueToInt(intRuntime.value) == input.number and
        valueToInt(intRaw.value) == input.number and
        tokenDynamic == token and
        valueToHost[ImportedToken](tokenRuntime.value) == token and
        valueToHost[ImportedToken](tokenRaw.value) == token,
    proc(input: tuple[flag: bool, number: int]):
        seq[tuple[flag: bool, number: int]] =
      @[(not input.flag, input.number), (input.flag, 0)])
  if not importedImplicitScalarCases:
    quit(1)
  let importedNullaryDefinitionCases = forAll(
    "imported nullary Eponym functions become zero-argument Nim procs", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(seed: int): bool =
      discard seed
      importedNullaryInt() == 42 and
        valueToInt(importedNullaryIntRuntimeValue().value) == 42,
    shrinkInt)
  if not importedNullaryDefinitionCases:
    quit(1)
  let importedGenericGlobals = importedIntIdentityRuntimeValue(0).globals
  var importedGenericWrongValueRejected = false
  try:
    discard importedGenericIdentityRuntimeValueRaw([
      runtimeGlobalValue(importedGenericGlobals, "Int"), natToValue(3)])
  except ValueError:
    importedGenericWrongValueRejected = true
  doAssert importedGenericWrongValueRejected
  var importedGenericWrongTypeRejected = false
  try:
    discard importedGenericIdentityRuntimeValueRaw([
      natToValue(3), intToValue(3)])
  except ValueError:
    importedGenericWrongTypeRejected = true
  doAssert importedGenericWrongTypeRejected
  let importedCallbackCases = forAll(
    "imported higher-order definitions accept checked Nim closures", r, 200,
    proc(r: var Rng): tuple[seed, value: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[seed, value: int]): bool =
      let callback = proc(value: int): int = value + input.seed
      let expected = input.value + input.seed
      let typedResult = importedCallbackApply(callback, input.value)
      let runtimeResult = importedCallbackApplyRuntimeValue(callback,
        input.value)
      typedResult == expected and valueToInt(runtimeResult.value) == expected,
    proc(input: tuple[seed, value: int]): seq[tuple[seed, value: int]] =
      @[(0, input.value), (input.seed, input.value)])
  if not importedCallbackCases:
    quit(1)
  let importedMultiCallbackCases = forAll(
    "imported definitions adapt multi-argument Nim closures", r, 200,
    proc(r: var Rng): tuple[left, right, bias: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[left, right, bias: int]): bool =
      let callback = proc(left, right: int): int =
        left * 3 + right + input.bias
      let expected = input.left * 3 + input.right + input.bias
      let typedResult = importedCallbackApply2(callback, input.left,
        input.right)
      let runtimeResult = importedCallbackApply2RuntimeValue(callback,
        input.left, input.right)
      typedResult == expected and valueToInt(runtimeResult.value) == expected,
    proc(input: tuple[left, right, bias: int]):
        seq[tuple[left, right, bias: int]] =
      @[(0, input.right, input.bias), (input.left, 0, input.bias),
        (input.left, input.right, 0)])
  if not importedMultiCallbackCases:
    quit(1)
  let importedReturnedCallbackCases = forAll(
    "imported definitions return callable Nim closures", r, 200,
    proc(r: var Rng): tuple[value, bias: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[value, bias: int]): bool =
      let callback = proc(value: int): int = value * 2 + input.bias
      let returned = importedCallbackIdentity(callback)
      let runtime = importedCallbackIdentityRuntimeValue(callback)
      returned(input.value) == input.value * 2 + input.bias and
        valueToInt(callRuntimeValue(runtime.value,
          [intToValue(input.value)])) == input.value * 2 + input.bias,
    proc(input: tuple[value, bias: int]): seq[tuple[value, bias: int]] =
      @[(0, input.bias), (input.value, 0)])
  if not importedReturnedCallbackCases:
    quit(1)
  let importedNullaryCallbackCases = forAll(
    "imported definitions bridge nullary Nim callbacks", r, 200,
    proc(r: var Rng): tuple[value, offset: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[value, offset: int]): bool =
      let expected = input.value + input.offset
      let callback: proc(): int {.closure.} =
        proc(): int = expected
      let applied = applyNullaryCallback(callback)
      let appliedRuntime = applyNullaryCallbackRuntimeValue(callback)
      let returned = nullaryCallbackIdentity(callback)
      let returnedRuntime = nullaryCallbackIdentityRuntimeValue(callback)
      applied == expected and valueToInt(appliedRuntime.value) == expected and
        returned() == expected and
        valueToInt(callRuntimeValue(returnedRuntime.value, [vUnit()])) ==
          expected,
    proc(input: tuple[value, offset: int]):
        seq[tuple[value, offset: int]] =
      @[(0, input.offset), (input.value, 0)])
  if not importedNullaryCallbackCases:
    quit(1)
  let importedDependentCallbackCases = forAll(
    "imported callbacks preserve dependent Vec result indices", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      let callback = proc(length: int): seq[int] =
        for i in 0 ..< length:
          result.add(input.seed + i)
      let expected = block:
        var values: seq[int] = @[]
        for i in 0 ..< input.length:
          values.add(input.seed + i)
        values
      let typedResult = importedDependentCallbackApply(callback, input.length)
      let runtimeResult = importedDependentCallbackApplyRuntimeValue(callback,
        input.length)
      let globals = runtimeResult.globals
      let vecType = callRuntimeValue(eval(globals["Vec"].tm, @[]),
        [runtimeGlobalValue(globals, "Int"),
         natToValue(input.length, globals)])
      validateRuntimeRawValue(runtimeResult.value, vecType, globals, [])
      typedResult == expected,
    proc(input: tuple[length, seed: int]):
        seq[tuple[length, seed: int]] =
      @[(0, input.seed), (input.length div 2, input.seed),
        (input.length, 0)])
  if not importedDependentCallbackCases:
    quit(1)
  var importedDependentCallbackWrongLengthRejected = false
  try:
    discard importedDependentCallbackApply(
      proc(length: int): seq[int] = @[1], 2)
  except ValueError:
    importedDependentCallbackWrongLengthRejected = true
  doAssert importedDependentCallbackWrongLengthRejected
  let importedDependentPairCases = forAll(
    "trusted imported wrappers bridge dependent Sigma values", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var values: seq[int] = @[]
      for i in 0 ..< input.length:
        values.add(input.seed + i)
      let argument = (input.length, values)
      let typedResult = importedDependentPairIdentity(argument)
      let runtimeResult = importedDependentPairIdentityRuntimeValue(argument)
      let first = valueToNat(runtimePairFirst(runtimeResult.value),
        runtimeResult.globals)
      let second = vecValueToSeq[int](
        runtimePairSecond(runtimeResult.value), input.length,
        runtimeResult.globals, "Vec",
        proc(value: Value, globals: Globals): int = valueToInt(value))
      first == input.length and typedResult == argument and second == values,
    proc(input: tuple[length, seed: int]):
        seq[tuple[length, seed: int]] =
      @[(0, input.seed), (input.length div 2, input.seed),
        (input.length, 0)])
  if not importedDependentPairCases:
    quit(1)
  var importedDependentPairWrongLengthRejected = false
  try:
    discard importedDependentPairIdentity((2, @[1]))
  except ValueError:
    importedDependentPairWrongLengthRejected = true
  doAssert importedDependentPairWrongLengthRejected
  var importedVectorMismatchRejected = false
  try:
    discard importedVectorIdentity(3, @[1, 2])
  except ValueError as error:
    importedVectorMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert importedVectorMismatchRejected
  let importedVectorGlobals = importedVectorIdentityRuntimeValue(3,
    @[1, 2, 3]).globals
  var importedRawVectorMismatchRejected = false
  try:
    discard importedVectorIdentityRuntimeValue(
      [natToValue(3, importedVectorGlobals),
       runtimeIntVector(@[1, 2], importedVectorGlobals)])
  except ValueError:
    importedRawVectorMismatchRejected = true
  doAssert importedRawVectorMismatchRejected

  let tokenValue = makeRuntimeTokenRuntimeValue().value
  let unmappedGenericCases = forAll(
    "dynamic wrappers accept unmapped indexed Values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(ignored: int): bool =
      let tokenProjection = genericRuntimeTokenProjectionRuntimeValueDynamic(
        tokenValue, ignored)
      let rawProjection = genericRuntimeTokenProjectionRuntimeValueRaw(
        [tokenValue], [intToValue(ignored)])
      tokenProjection.value.whnfKind == tokenValue.whnfKind and
        tokenProjection.value.whnfRefId == tokenValue.whnfRefId and
        rawProjection.value.whnfKind == tokenValue.whnfKind and
        rawProjection.value.whnfRefId == tokenValue.whnfRefId,
    shrinkInt)
  if not unmappedGenericCases:
    quit(1)
  var unmappedGenericTypeRejected = false
  try:
    discard genericRuntimeTokenProjectionRuntimeValueDynamic(
      intToValue(42), 0)
  except ValueError as error:
    unmappedGenericTypeRejected = "mismatch" in error.msg
  doAssert unmappedGenericTypeRejected
  var rawUnmappedGenericTypeRejected = false
  try:
    discard genericRuntimeTokenProjectionRuntimeValueRaw(
      [intToValue(42)], [intToValue(0)])
  except ValueError as error:
    rawUnmappedGenericTypeRejected = "mismatch" in error.msg
  doAssert rawUnmappedGenericTypeRejected

  let genericFunctionValue = generatedRuntimeIncrementValueRuntimeValue()
  let genericFunctionType = runtimeArrowType(
    runtimeGlobalValue(genericFunctionValue.globals, "Int"),
    runtimeGlobalValue(genericFunctionValue.globals, "Int"))
  let hostGenericFunctionValue = setRuntimeHostFunctionType(
    vHostFunc(proc(value: Value): Value =
      intToValue(valueToInt(value) + 1)), genericFunctionType,
    genericFunctionValue.globals)
  validateRuntimeValueType(genericFunctionValue.value, genericFunctionType,
    genericFunctionValue.globals)
  let genericFunctionBinderCases = forAll(
    "dynamic generic binders validate checked and host function values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(input: int): bool =
      let checked = generatedApplyGenericFunctionDynamic(
        genericFunctionValue.value, input)
      let runtime = generatedApplyGenericFunctionRuntimeValueDynamic(
        genericFunctionValue.value, input)
      let hostChecked = generatedApplyGenericFunctionDynamic(
        hostGenericFunctionValue, input)
      let hostRuntime = generatedApplyGenericFunctionRuntimeValueDynamic(
        hostGenericFunctionValue, input)
      let nimcallResult = generatedApplyGenericFunctionDynamic(
        hostStepNim, input)
      let nimcallRuntime = generatedApplyGenericFunctionRuntimeValueDynamic(
        hostStepNim, input)
      checked == input + 1 and valueToInt(runtime.value) == input + 1 and
        hostChecked == input + 1 and valueToInt(hostRuntime.value) == input + 1 and
        nimcallResult == input + 7 and
        valueToInt(nimcallRuntime.value) == input + 7,
    shrinkInt)
  if not genericFunctionBinderCases:
    quit(1)
  var genericFunctionTypeRejected = false
  try:
    discard generatedApplyGenericFunctionRuntimeValueDynamic(
      intToValue(42), 0)
  except ValueError:
    genericFunctionTypeRejected = true
  doAssert genericFunctionTypeRejected
  var hostFunctionTypeRejected = false
  try:
    discard generatedApplyGenericFunctionDynamic(intToValue(42), 0)
  except ValueError:
    hostFunctionTypeRejected = true
  doAssert hostFunctionTypeRejected

  let dependentTypeGlobals = generatedDependentTypeAnchorRuntimeValue().globals
  let natTypeForCallback = runtimeGlobalValue(dependentTypeGlobals, "Nat")
  let intTypeForCallback = runtimeGlobalValue(dependentTypeGlobals, "Int")
  let expectedDependentCallbackType = runtimeDependentArrowType(
    natTypeForCallback, dependentTypeGlobals,
    proc(length: Value): Value =
      callRuntimeValue(eval(dependentTypeGlobals["Vec"].tm, @[]),
        [intTypeForCallback, length]))
  let dependentHostCallback = setRuntimeHostFunctionType(
    vHostFunc(proc(length: Value): Value =
      runtimeIntVector(makeIndexedRuntimeValues(valueToNat(
        length, dependentTypeGlobals)), dependentTypeGlobals)),
    expectedDependentCallbackType, dependentTypeGlobals)
  let genericDependentFunctionCases = forAll(
    "dynamic generic binders accept Nim callbacks with dependent Pi types", r, 200,
    proc(r: var Rng): int = r.genInt(0, 16),
    proc(length: int): bool =
      let expected = makeIndexedRuntimeValues(length)
      let nimCallback: proc(length: int): seq[int] {.closure.} =
        proc(length: int): seq[int] = makeIndexedRuntimeValues(length)
      let checked = generatedApplyDependentVectorFunctionDynamic(
        nimCallback, length)
      let runtime = generatedApplyDependentVectorFunctionRuntimeValueDynamic(
        nimCallback, length)
      let rawRuntime = generatedApplyDependentVectorFunctionRuntimeValueRaw(
        [dependentHostCallback], [natToValue(length, dependentTypeGlobals)])
      checked == expected and vecValueToSeq[int](runtime.value, length,
        runtime.globals, "Vec",
        proc(value: Value, globals: Globals): int = valueToInt(value)) ==
          expected and vecValueToSeq[int](rawRuntime.value, length,
        rawRuntime.globals, "Vec",
        proc(value: Value, globals: Globals): int = valueToInt(value)) ==
          expected,
    shrinkInt)
  if not genericDependentFunctionCases:
    quit(1)
  let genericComputedVectorCallbackCases = forAll(
    "dynamic callbacks reify add in dependent Vec indices", r, 200,
    proc(r: var Rng): int = r.genInt(0, 16),
    proc(length: int): bool =
      var expected: seq[int] = @[]
      for i in 0 .. length: expected.add(i - length)
      let callback: proc(length: int): seq[int] {.closure.} =
        proc(length: int): seq[int] =
          var values: seq[int] = @[]
          for i in 0 .. length: values.add(i - length)
          values
      let checked = generatedApplyComputedVectorFunctionDynamic(callback,
        length)
      let runtime = generatedApplyComputedVectorFunctionRuntimeValueDynamic(
        callback, length)
      let wrongLength: proc(length: int): seq[int] {.closure.} =
        proc(length: int): seq[int] = newSeq[int](length)
      var wrongLengthRejected = false
      try:
        discard generatedApplyComputedVectorFunctionDynamic(wrongLength,
          length)
      except ValueError:
        wrongLengthRejected = true
      var wrongRuntimeLengthRejected = false
      try:
        discard generatedApplyComputedVectorFunctionRuntimeValueDynamic(
          wrongLength, length)
      except ValueError:
        wrongRuntimeLengthRejected = true
      checked == expected and
        vecValueToSeq[int](runtime.value, length + 1, runtime.globals, "Vec",
          proc(value: Value, globals: Globals): int = valueToInt(value)) ==
          expected and wrongLengthRejected and wrongRuntimeLengthRejected,
    shrinkInt)
  if not genericComputedVectorCallbackCases:
    quit(1)
  let genericTwoIndexVectorCallbackCases = forAll(
    "dependent callbacks use all binders in computed Vec indices", r, 200,
    proc(r: var Rng): tuple[left, right: int] =
      (r.genInt(0, 8), r.genInt(0, 8)),
    proc(input: tuple[left, right: int]): bool =
      let expectedLength = input.left + input.right
      var expected: seq[int] = @[]
      for i in 0 ..< expectedLength: expected.add(i - input.left)
      let callback: proc(left, right: int): seq[int] {.closure.} =
        proc(left, right: int): seq[int] =
          var values: seq[int] = @[]
          for i in 0 ..< (left + right): values.add(i - left)
          values
      let checked = generatedApplyTwoIndexVectorFunctionDynamic(callback,
        input.left, input.right)
      let runtime = generatedApplyTwoIndexVectorFunctionRuntimeValueDynamic(
        callback, input.left, input.right)
      let wrongLength: proc(left, right: int): seq[int] {.closure.} =
        proc(left, right: int): seq[int] = newSeq[int](left + right + 1)
      var checkedRejected = false
      try:
        discard generatedApplyTwoIndexVectorFunctionDynamic(wrongLength,
          input.left, input.right)
      except ValueError:
        checkedRejected = true
      var runtimeRejected = false
      try:
        discard generatedApplyTwoIndexVectorFunctionRuntimeValueDynamic(
          wrongLength, input.left, input.right)
      except ValueError:
        runtimeRejected = true
      checked == expected and
        vecValueToSeq[int](runtime.value, expectedLength, runtime.globals,
          "Vec", proc(value: Value, globals: Globals): int = valueToInt(value)) ==
          expected and checkedRejected and runtimeRejected)
  if not genericTwoIndexVectorCallbackCases:
    quit(1)
  let wrongDependentCallbackType = runtimeDependentArrowType(
    natTypeForCallback, dependentTypeGlobals,
    proc(length: Value): Value =
      callRuntimeValue(eval(dependentTypeGlobals["Vec"].tm, @[]),
        [natTypeForCallback, length]))
  let wrongDependentHostCallback = setRuntimeHostFunctionType(
    vHostFunc(proc(length: Value): Value =
      runtimeIntVector(makeIndexedRuntimeValues(valueToNat(
        length, dependentTypeGlobals)), dependentTypeGlobals)),
    wrongDependentCallbackType, dependentTypeGlobals)
  var dependentCallbackTypeRejected = false
  try:
    discard generatedApplyDependentVectorFunctionDynamic(
      wrongDependentHostCallback, 0)
  except ValueError:
    dependentCallbackTypeRejected = true
  doAssert dependentCallbackTypeRejected
  let genericBinaryCallbackCases = forAll(
    "dynamic generic binders bridge multi-argument Nim callbacks", r, 200,
    proc(r: var Rng): tuple[left, right, bias: int] =
      (r.genInt(-500, 500), r.genInt(-500, 500), r.genInt(-100, 100)),
    proc(input: tuple[left, right, bias: int]): bool =
      let callback: proc(left, right: int): int {.closure.} =
        proc(left, right: int): int = left + right + input.bias
      let expected = input.left + input.right + input.bias
      generatedApplyGenericBinaryFunctionDynamic(callback, input.left,
        input.right) == expected and
        valueToInt(generatedApplyGenericBinaryFunctionRuntimeValueDynamic(
          callback, input.left, input.right).value) == expected,
    proc(input: tuple[left, right, bias: int]):
        seq[tuple[left, right, bias: int]] =
      @[(input.left div 2, input.right, input.bias),
        (input.left, input.right div 2, input.bias),
        (input.left, input.right, 0)])
  if not genericBinaryCallbackCases:
    quit(1)

  let rawGenericNatCases = forAll(
    "raw runtimeValue accepts Eponym generic arguments as Values", r, 200,
    proc(r: var Rng): int = r.genInt(0, 1000),
    proc(index: int): bool = rawGenericNatAt(index),
    shrinkInt)
  if not rawGenericNatCases:
    quit(1)

  let rawCallbackCases = forAll(
    "raw Value callbacks bridge unmapped higher-order types", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let globals = generatedRawTokenCallbackEchoRuntimeValue(
        rawRuntimeIdentity).globals
      let token = eval(globals["runtimeTokenRed"].tm, @[])
      let callback: RawRuntimeCallback =
        generatedRawTokenCallbackEcho(rawRuntimeIdentity)
      let wrapperResult = callback(token).whnfKind == token.whnfKind and
        callback(token).whnfRefId == token.whnfRefId
      let runtime = generatedRawTokenCallbackEchoRuntimeValue(
        rawRuntimeIdentity)
      let runtimeCallback = callRuntimeValue(runtime.value, [token])
      let runtimeResult = runtimeCallback.whnfKind == token.whnfKind and
        runtimeCallback.whnfRefId == token.whnfRefId
      wrapperResult and runtimeResult,
    shrinkInt)
  if not rawCallbackCases:
    quit(1)

  let rawCallbackRuntime = generatedRawTokenCallbackEchoRuntimeValue(
    rawRuntimeIdentity)
  let rawCallbackToken = eval(rawCallbackRuntime.globals["runtimeTokenRed"].tm,
    @[])
  var rawCallbackArgumentRejected = false
  try:
    discard generatedRawTokenCallbackEcho(rawRuntimeIdentity)(intToValue(42))
  except ValueError as error:
    rawCallbackArgumentRejected = true
    doAssert "runtime" in error.msg
  doAssert rawCallbackArgumentRejected, "wrong callback argument was accepted"
  var rawCallbackResultRejected = false
  try:
    discard generatedRawTokenCallbackEcho(rawRuntimeWrongToken)(rawCallbackToken)
  except ValueError as error:
    rawCallbackResultRejected = true
    doAssert "runtime" in error.msg
  doAssert rawCallbackResultRejected, "wrong callback result was accepted"
  var rawRuntimeCallbackResultRejected = false
  try:
    let badRuntime = generatedRawTokenCallbackEchoRuntimeValue(
      rawRuntimeWrongToken)
    discard callRuntimeValue(badRuntime.value, [rawCallbackToken])
  except ValueError as error:
    rawRuntimeCallbackResultRejected = true
    doAssert "runtime" in error.msg
  doAssert rawRuntimeCallbackResultRejected,
    "wrong raw RuntimeValue callback result was accepted"

  let rawIndexedCallbackCases = forAll(
    "raw callback checks dependent Vec arguments and indices", r, 200,
    proc(r: var Rng): tuple[length: int, values: seq[int]] =
      let length = r.genInt(0, 12)
      var values: seq[int] = @[]
      for _ in 0 ..< length: values.add(r.genInt(-1000, 1000))
      (length, values),
    proc(input: tuple[length: int, values: seq[int]]): bool =
      let runtime = generatedRawIndexedCallbackEchoRuntimeValue(
        rawRuntimeReturnLength)
      let vector = runtimeIntVector(input.values, runtime.globals)
      let callback: RawIndexedRuntimeCallback =
        generatedRawIndexedCallbackEcho(rawRuntimeReturnLength)
      let direct = callback(natToValue(input.length, runtime.globals), vector)
      let reified = callRuntimeValue(runtime.value,
        [natToValue(input.length, runtime.globals), vector])
      valueToNat(direct, runtime.globals) == input.length and
        valueToNat(reified, runtime.globals) == input.length,
    proc(input: tuple[length: int, values: seq[int]]):
        seq[tuple[length: int, values: seq[int]]] = @[])
  if not rawIndexedCallbackCases:
    quit(1)
  let rawIndexedGlobals = generatedRawIndexedCallbackEchoRuntimeValue(
    rawRuntimeReturnLength).globals
  var rawIndexedCallbackRejected = false
  try:
    let callback: RawIndexedRuntimeCallback =
      generatedRawIndexedCallbackEcho(rawRuntimeReturnLength)
    discard callback(natToValue(2, rawIndexedGlobals),
      runtimeIntVector(@[1], rawIndexedGlobals))
  except ValueError:
    rawIndexedCallbackRejected = true
  doAssert rawIndexedCallbackRejected,
    "raw callback accepted a Vec with the wrong dependent length"

  var importedArityRejected = false
  try:
    discard importedIdentityRuntimeValue([])
  except ValueError as error:
    importedArityRejected =
      "runtimeValue argument count mismatch for importedIdentity" in error.msg
  doAssert importedArityRejected

  let importedPostulateCases = forAll(
    "imported checked definitions dispatch bound host postulates", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let runtime = importedApplyRuntimeValue([intToValue(value)])
      let typedRuntime = importedApplyRuntimeValue(value)
      importedApply(value) == value + 7 and
        namedImportedApply(value = value) == value + 7 and
        typedRuntime.value.whnfKind == wInt and
        typedRuntime.value.whnfIntVal == value + 7 and
        runtime.value.whnfKind == wInt and runtime.value.whnfIntVal == value + 7,
    shrinkInt)
  if not importedPostulateCases:
    quit(1)

  let intRoundTrips = forAll("runtime Int Values through checked definitions",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let value = callValueFuncDir(baseDir, program, "double",
        @[intToValue(n)])
      valueToInt(value) == n * 2,
    shrinkInt)

  let natRoundTrips = forAll("runtime Nat Values through checked definitions",
    r, 200,
    proc(r: var Rng): int = r.genInt(0, 1000),
    proc(n: int): bool =
      let value = callValueFuncDir(baseDir, program, "idNat",
        @[natToValue(n)])
      valueToNat(value) == n,
    shrinkInt)

  # Keep the original generated-wrapper helper working through the shared
  # Value-based evaluator path.
  let compat = callIntFuncDir(baseDir, program, "double", @[21]) == 42
  let generatedBindingWorks = generatedCheckedRole(35) == 42
  let generatedTypedWrappersWork = generatedAdd(20, 22) == 42 and
    generatedAdd(left = 20, right = 22) == 42 and
    generatedDefault() == 42 and generatedDefault(7) == 7 and
    generatedDefault(value = 7) == 7 and
    generatedNestedDefault() == 42 and
    generatedNatId(17) == 17 and generatedArithmetic(5, 7, 3) == -27 and
    generatedSigmaId((17, -9)) == (17, -9) and
    generatedOpaqueSigmaId((17, ChannelHandle(id: 1))) ==
      (17, ChannelHandle(id: 1))
  let namedArgumentCalls = forAll(
    "named arguments preserve checked callable parameter order", r, 200,
    proc(r: var Rng): tuple[left, right: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[left, right: int]): bool =
      generatedNamedAdd(input.left, input.right) == input.left + input.right and
      generatedNamedCallback(hostAddTwoNim, input.left, input.right) ==
        input.left + input.right,
    proc(input: tuple[left, right: int]):
        seq[tuple[left, right: int]] = @[])
  if not namedArgumentCalls:
    quit(1)
  let namedDefaultCalls = forAll(
    "checked calls fill omitted Nim defaults before named arguments", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(adjustment: int): bool =
      generatedNamedDefaultGap(adjustment) == 42 + adjustment,
    shrinkInt)
  if not namedDefaultCalls:
    quit(1)
  let generatedRecordRoundTrips = forAll(
    "structural record codec preserves primitive and opaque fields", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let input = RuntimePoint(x: abs(n mod 1000),
        channel: ChannelHandle(id: n, label: "point-" & $n))
      let runtime = generatedPointIdRuntimeValue(input)
      let rawRuntime = generatedPointIdRuntimeValue([runtime.value])
      var wrongOpaqueBoxRejected = false
      try:
        let malformed = pairValue(natToValue(input.x, runtime.globals),
          pairValue(toHostValue("wrong host type"), unitValue()))
        discard generatedPointIdRuntimeValue([malformed])
      except ValueError:
        wrongOpaqueBoxRejected = true
      generatedPointId(input) == input and
        rawRuntime.value.whnfKind == wPair and wrongOpaqueBoxRejected,
    shrinkInt)
  if not generatedRecordRoundTrips:
    quit(1)
  let generatedPairBindingCases = forAll(
    "typed host adapters can return non-dependent Sigma values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let nat = abs(id)
      let input = ChannelHandle(id: nat, label: "split-" & $nat)
      let pairResult = generatedSplitChannel(input)
      pairResult[0] == nat and pairResult[1] ==
        ChannelHandle(id: nat + 1, label: "split-" & $nat & "/split"),
    shrinkInt)
  if not generatedPairBindingCases:
    quit(1)
  let generatedBinaryPairBindingCases = forAll(
    "two-argument typed adapters return non-dependent Sigma values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let left = abs(n mod 1000)
      let right = abs((n div 3) mod 1000)
      let channel = ChannelHandle(id: left, label: "binary-" & $right)
      let pairResult = generatedSplitChannelWithNat(right, channel)
      pairResult[0] == right + left and pairResult[1] ==
        ChannelHandle(id: left + 1, label: "binary-" & $right & "/split-nat"),
    shrinkInt)
  if not generatedBinaryPairBindingCases:
    quit(1)
  let generatedTernaryPairBindingCases = forAll(
    "three-argument typed adapters return non-dependent Sigma values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let first = abs(n mod 1000)
      let second = abs((n div 5) mod 1000)
      let channel = ChannelHandle(id: first, label: "ternary-" & $second)
      let pairResult = generatedSplitChannelWithTwoNats(first, second, channel)
      pairResult[0] == first + second + first and pairResult[1] ==
        ChannelHandle(id: first + 1,
          label: "ternary-" & $second & "/split-two"),
    shrinkInt)
  if not generatedTernaryPairBindingCases:
    quit(1)
  let generatedTrustedDependentPairCases = forAll(
    "explicit trusted codecs carry a dependent Sigma field", r, 200,
    proc(r: var Rng): int = r.genInt(0, 1000),
    proc(index: int): bool =
      generatedIndexedChannelIndex(IndexedChannelHandle(index: index,
        label: "index-" & $index)) == index,
    shrinkInt)
  let generatedTrustedDependentPairAdapterCases = forAll(
    "trusted host pair adapters preserve dependent Vec indices", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(seed: int): bool =
      let pairResult = generatedMakeIndexedVector(seed)
      pairResult[0] == abs(seed mod 20) and
        pairResult[1].len == pairResult[0] and
        pairResult[1] == hostMakeIndexedVector(seed).values,
    shrinkInt)
  let generatedOuterDependentVectorCases = forAll(
    "function arguments and host pair results share an outer Nat index", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(index: int): bool =
      var values: seq[int] = @[]
      for i in 0 ..< index: values.add(i - index)
      let wrapperRoundTrip =
        generatedVectorArgIdentity(index, values) == values
      let runtime = generatedVectorArgIdentityRuntimeValue(index, values)
      let runtimeRoundTrip = vecValueToSeq[int](runtime.value, index,
        runtime.globals, "Vec",
        proc(value: Value, globals: Globals): int = valueToInt(value)) == values
      let rawVector = runtimeIntVector(values, runtime.globals)
      let rawRuntime = generatedVectorArgIdentityRuntimeValue(
        [natToValue(index, runtime.globals), rawVector])
      let rawRoundTrip = vecValueToSeq[int](rawRuntime.value, index,
        rawRuntime.globals, "Vec",
        proc(value: Value, globals: Globals): int = valueToInt(value)) == values
      let pairResult = generatedVectorForIndex(index, -index)
      let pairRoundTrip = pairResult[0] == -index and
        pairResult[1].len == index
      let importedPairResult = generatedImportedVectorForIndex(index, -index)
      let importedPairRoundTrip = importedPairResult[0] == -index and
        importedPairResult[1].len == index
      var inputMismatchRejected = false
      try:
        discard generatedVectorArgIdentity(index, values & @[index])
      except ValueError:
        inputMismatchRejected = true
      var rawInputMismatchRejected = false
      try:
        let malformed = runtimeIntVector(values & @[index], runtime.globals)
        discard generatedVectorArgIdentityRuntimeValue(
          [natToValue(index, runtime.globals), malformed])
      except ValueError:
        rawInputMismatchRejected = true
      var typedRuntimeInputMismatchRejected = false
      try:
        discard generatedVectorArgIdentityRuntimeValue(index,
          values & @[index])
      except ValueError:
        typedRuntimeInputMismatchRejected = true
      var adapterMismatchRejected = false
      try:
        discard generatedVectorForIndex(index, low(int))
      except ValueError:
        adapterMismatchRejected = true
      var importedAdapterMismatchRejected = false
      try:
        discard generatedImportedVectorForIndex(index, low(int))
      except ValueError:
        importedAdapterMismatchRejected = true
      wrapperRoundTrip and runtimeRoundTrip and rawRoundTrip and pairRoundTrip and
        importedPairRoundTrip and inputMismatchRejected and
        rawInputMismatchRejected and typedRuntimeInputMismatchRejected and
        adapterMismatchRejected and
        importedAdapterMismatchRejected,
    shrinkInt)
  var dependentPairAdapterMismatchRejected = false
  try:
    discard generatedMakeIndexedVector(low(int))
  except ValueError:
    dependentPairAdapterMismatchRejected = true
  if not generatedTrustedDependentPairCases:
    quit(1)
  let generatedTrustedDependentResultCases = forAll(
    "explicit trusted wrapper codecs carry a dependent Sigma result", r, 200,
    proc(r: var Rng): int = r.genInt(0, 1000),
    proc(index: int): bool =
      let pairOutput = generatedSplitIndexedChannel(IndexedChannelHandle(
        index: index, label: "wrapper-" & $index))
      pairOutput[0] == index and pairOutput[1] == IndexedChannelHandle(
        index: index, label: "wrapper-" & $index & "/indexed"),
    shrinkInt)
  let generatedDependentPairVecCases = forAll(
    "trusted dependent Sigma checks its Vec length", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(n: int): bool =
      let length = n mod 20
      var values: seq[int] = @[]
      for i in 0 ..< length: values.add(i + n)
      let input = (length, n, values)
      let roundTrips = generatedDependentPairVecIdentity(input) == input
      let runtime = generatedDependentPairVecIdentityRuntimeValue(input)
      let rawRuntime = generatedDependentPairVecIdentityRuntimeValue(
        [runtime.value])
      let badValues = if values.len == 0: @[n] else: values[0 ..< values.len - 1]
      var mismatchRejected = false
      try:
        discard generatedDependentPairVecIdentity((length, n, badValues))
      except ValueError:
        mismatchRejected = true
      var rawMismatchRejected = false
      try:
        let malformed = pairValue(natToValue(length, runtime.globals),
          pairValue(intToValue(n), runtimeIntVector(badValues,
            runtime.globals)))
        discard generatedDependentPairVecIdentityRuntimeValue([malformed])
      except ValueError:
        rawMismatchRejected = true
      roundTrips and runtime.value.whnfKind == wPair and
        rawRuntime.value.whnfKind == wPair and mismatchRejected and
        rawMismatchRejected,
    shrinkInt)
  let generatedDependentPairEnvelopeCases = forAll(
    "dependent record and Sigma indices compose through Vec codecs", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(n: int): bool =
      let base = n mod 10
      let count = (n div 3) mod 10
      var values: seq[int] = @[]
      for i in 0 ..< base + count: values.add(i + n)
      let input = RuntimeDependentPairEnvelope(base: base,
        payload: (count, values))
      let roundTrips = generatedDependentPairEnvelopeIdentity(input) == input
      var mismatchRejected = false
      try:
        var bad = input
        bad.payload.values.add(n)
        discard generatedDependentPairEnvelopeIdentity(bad)
      except ValueError:
        mismatchRejected = true
      roundTrips and mismatchRejected,
    shrinkInt)
  let generatedShadowedDependentPairVecCases = forAll(
    "nested Sigma index shadowing uses the nearest binder", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(n: int): bool =
      let outerLength = n mod 20
      let innerLength = (n div 3) mod 20
      var values: seq[int] = @[]
      for i in 0 ..< innerLength: values.add(i + n)
      let input = (outerLength, innerLength, values)
      let roundTrips = generatedShadowedDependentPairVecIdentity(input) == input
      var mismatchRejected = false
      try:
        discard generatedShadowedDependentPairVecIdentity(
          (outerLength, innerLength, values & @[n]))
      except ValueError:
        mismatchRejected = true
      roundTrips and mismatchRejected,
    shrinkInt)
  if not generatedTrustedDependentResultCases:
    quit(1)
  let fourFieldSigmaCases = forAll(
    "nested Sigma values map to flat four-field Nim tuples", r, 200,
    proc(r: var Rng): tuple[a, b, c: int, flag: bool] =
      (r.genInt(-1000, 1000), r.genInt(0, 100), r.genInt(-1000, 1000),
       r.genBool()),
    proc(input: tuple[a, b, c: int, flag: bool]): bool =
      let runtime = generatedFourFieldSigmaIdentityRuntimeValue(input)
      let rawRuntime = generatedFourFieldSigmaIdentityRuntimeValue(
        [runtime.value])
      generatedFourFieldSigmaIdentity(input) == input and
        generatedFourFieldSigmaIdentityRuntimeValue(input).value.whnfKind ==
          wPair and rawRuntime.value.whnfKind == wPair and
        generatedMakeFourSigma(abs(input.a)) ==
          hostMakeFourSigma(abs(input.a)) and
        (block:
          let seed = abs(input.a)
          let pair = generatedMakeFourSigmaRuntimeValue(seed)
          let tail1 = runtimePairSecond(pair.value)
          let tail2 = runtimePairSecond(tail1)
          let tail3 = runtimePairSecond(tail2)
          valueToInt(runtimePairFirst(pair.value)) == seed and
          valueToNat(runtimePairFirst(tail1), pair.globals) == seed mod 101 and
          valueToInt(runtimePairFirst(tail2)) == -seed and
          valueToBool(tail3, pair.globals) == ((seed mod 2) == 0)),
    proc(input: tuple[a, b, c: int, flag: bool]):
        seq[tuple[a, b, c: int, flag: bool]] =
      @[(0, input.b, input.c, input.flag),
        (input.a, input.b, 0, input.flag),
        (input.a, input.b, input.c, not input.flag)])
  if not fourFieldSigmaCases:
    quit(1)
  let generatedPairWithExternalIndexCases = forAll(
    "non-dependent Sigma tails may use earlier Pi indices", r, 200,
    proc(r: var Rng): int = r.genInt(0, 1000),
    proc(index: int): bool =
      let channel = IndexedChannelHandle(index: index,
        label: "outer-" & $index)
      let pairResult = generatedRepeatIndexedChannel(index, channel)
      pairResult[0] == channel and pairResult[1] ==
        IndexedChannelHandle(index: index, label: channel.label & "/copy"),
    shrinkInt)
  if not generatedPairWithExternalIndexCases:
    quit(1)
  let generatedNestedRecordRoundTrips = forAll(
    "nested structural record codecs preserve recursive fields", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let input = RuntimeEnvelope(
        point: RuntimePoint(x: abs(n mod 1000),
          channel: ChannelHandle(id: n, label: "nested-" & $n)),
        note: "message-" & $n)
      generatedEnvelopeId(input) == input,
    shrinkInt)
  if not generatedNestedRecordRoundTrips:
    quit(1)
  let generatedPureConditionalsWork = generatedChooseTrue() == 19 and
    generatedChooseFalse() == 17
  let generatedOpaqueWrapperWorks = generatedRouteRole(
    ChannelHandle(id: 17, label: "socket"), "generated").label ==
      "socket:generated"
  let futureInput = newFuture[int]("futureArgument")
  let generatedFutureInputPassesThrough =
    generatedFutureInput(futureInput) == futureInput
  let arithmeticCases = forAll("Nim-shaped checked Int arithmetic", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let right = n div 2
      let scale = (n mod 9) + 1
      generatedArithmetic(n, right, scale) == (n - right - right) * scale,
    shrinkInt)
  let boolXorCases = forAll(
    "Nim-shaped checked Bool xor evaluates both values correctly", r, 200,
    proc(r: var Rng): tuple[left, right: bool] = (r.genBool(), r.genBool()),
    proc(input: tuple[left, right: bool]): bool =
      generatedBoolXor(input.left, input.right) == (input.left xor input.right),
    proc(input: tuple[left, right: bool]): seq[tuple[left, right: bool]] =
      @[(false, input.right), (input.left, false)])
  doAssert generatedIntOne() == 1
  doAssert generatedBoolXorWithNimCalls() == (true xor false)
  let sigmaRoundTrips = forAll(
    "structural Sigma codec round-trips Nat/Int tuple values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let input = (abs(n mod 1000), n)
      generatedSigmaId(input) == input,
    shrinkInt)
  if not sigmaRoundTrips:
    quit(1)
  let opaqueSigmaCases = forAll(
    "structural Sigma codec preserves mapped opaque fields", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let input = (abs(n mod 1000), ChannelHandle(id: n, label: $n))
      generatedOpaqueSigmaId(input) == input,
    shrinkInt)
  if not opaqueSigmaCases:
    quit(1)
  if not arithmeticCases:
    quit(1)
  if not boolXorCases:
    quit(1)
  let generatedUnaryOpaqueWorks = generatedRotateRole(
    ChannelHandle(id: 18, label: "single")).id == 19
  let generatedUnaryOpaqueCases = forAll(
    "generated unary opaque wrappers preserve typed values",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let value = generatedRotateRole(ChannelHandle(id: id, label: "unit"))
      value.id == id + 1 and value.label == "unit*",
    shrinkInt)
  let generatedOpaqueWrapperCases = forAll(
    "generated opaque wrappers preserve typed values",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let value = generatedRouteRole(ChannelHandle(id: id, label: "channel"),
                                     $id)
      value.id == id and value.label == "channel:" & $id,
    shrinkInt)
  var hostExceptionPropagated = false
  try:
    discard generatedFailureRole(1)
  except IOError as e:
    hostExceptionPropagated = e.msg == "host adapter failed"

  var rejectedNegativeNat = false
  try:
    discard natToValue(-1)
  except ValueError:
    rejectedNegativeNat = true
  if not (intRoundTrips and natRoundTrips and compat and generatedBindingWorks and
      generatedTypedWrappersWork and generatedOpaqueWrapperWorks and
      generatedRecordRoundTrips and
      generatedPairBindingCases and
      generatedBinaryPairBindingCases and
      generatedTernaryPairBindingCases and
      generatedTrustedDependentPairCases and
      generatedTrustedDependentPairAdapterCases and
      generatedOuterDependentVectorCases and
      dependentPairAdapterMismatchRejected and
      generatedDependentPairVecCases and
      generatedDependentPairEnvelopeCases and
      generatedShadowedDependentPairVecCases and
      generatedPairWithExternalIndexCases and
      generatedNestedRecordRoundTrips and
      generatedFutureInputPassesThrough and
      generatedPureConditionalsWork and
      generatedUnaryOpaqueWorks and generatedUnaryOpaqueCases and
      generatedOpaqueWrapperCases and
      rejectedNegativeNat and hostExceptionPropagated):
    quit(1)

  # The runtime-binding work needs the exact global identities assigned by
  # the checker. Confirm a definition body refers to the same postulate
  # reference exposed in the returned state.
  const identityProgram = """
import "tests/fixtures/runtime_host_step.ep"
postulate Message : Type 0
postulate routeChannel : Channel -> Message -> Channel
proc throughHelper : Int -> Int = lam (n : Int). importedHelper n
proc opaqueRole : Channel -> Channel =
  lam (channel : Channel). importedChannelStep channel
proc routeRole : Channel -> Message -> Channel =
  lam (channel : Channel). lam (message : Message).
    routeChannel channel message
postulate RequestId : Type 0
postulate Phase : Type 0
postulate PendingResult : Type 0
postulate Callback : Type 0
postulate Sample : Type 0
postulate routeChannelWithId : Channel -> Message -> RequestId -> Channel
proc routeWithIdRole : Channel -> Message -> RequestId -> Channel =
  lam (channel : Channel). lam (message : Message). lam (requestId : RequestId).
    routeChannelWithId channel message requestId
postulate routeChannelWithPhase : Channel -> Message -> RequestId -> Phase -> Channel
proc routeWithPhaseRole : Channel -> Message -> RequestId -> Phase -> Channel =
  lam (channel : Channel). lam (message : Message). lam (requestId : RequestId).
    lam (phase : Phase). routeChannelWithPhase channel message requestId phase
postulate startFuture : Channel -> PendingResult
proc futureRole : Channel -> PendingResult =
  lam (channel : Channel). startFuture channel
postulate invokeCallback : Callback -> Sample -> Sample
proc callbackRole : Callback -> Sample -> Sample =
  lam (callback : Callback). lam (value : Sample).
    invokeCallback callback value
"""
  let checked = elabCheckDirState(identityProgram, baseDir)
  let postulateId = checked.globals["hostStep"].tm.refId
  let cachedGlobals = getGlobalsDir(baseDir, identityProgram)
  if cachedGlobals["hostStep"].tm.refId != postulateId:
    quit(1)
  var runtimeBindings = initRuntimeBindings()
  runtimeBindings.bindHostIntUnary(cachedGlobals, "hostStep", hostStepNim)
  let hostResult = callValueFuncDir(baseDir, identityProgram,
    "throughHelper", @[intToValue(35)], runtimeBindings)
  if valueToInt(hostResult) != 42:
    quit(1)

  var missingHostBindingDiagnosed = false
  try:
    discard callValueFuncDir(baseDir, identityProgram, "throughHelper",
      @[intToValue(35)])
  except ValueError as e:
    missingHostBindingDiagnosed = "unbound runtime postulate 'hostStep'" in e.msg
  if not missingHostBindingDiagnosed:
    quit(1)

  let hostDispatch = forAll("checked definitions dispatch to typed Nim postulates",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      var bindings = initRuntimeBindings()
      bindings.bindHostIntUnary(cachedGlobals, "hostStep", hostStepNim)
      let value = callValueFuncDir(baseDir, identityProgram, "throughHelper",
        @[intToValue(n)], bindings)
      valueToInt(value) == hostStepNim(n),
    shrinkInt)
  if not hostDispatch:
    quit(1)

  let boolCodecCases = forAll("generated Bool wrappers preserve constructors",
    r, 200,
    proc(r: var Rng): bool = r.genBool(),
    proc(value: bool): bool = generatedBoolNot(value) == not value)
  if not boolCodecCases:
    quit(1)
  let clauseNatWrapperCases = forAll(
    "clause definitions get typed Nat wrappers from checked signatures", r,
    200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(value: int): bool =
      generatedClauseNatIdentity(value) == value,
    shrinkInt)
  if not clauseNatWrapperCases:
    quit(1)

  let genericIdentityCases = forAll(
    "polymorphic identity wrappers preserve arbitrary host values",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool = generatedGenericIdentity(value) == value and
      valueToHost[int](generatedGenericIdentityRuntimeValue(value).value) == value,
    shrinkInt)
  if not genericIdentityCases:
    quit(1)

  let genericOpaqueIdentityCases = forAll(
    "polymorphic identity wrappers round-trip boxed user objects",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let input = ChannelHandle(id: id, label: "generic/" & $id)
      let generated = generatedGenericIdentity(input)
      let runtime = generatedGenericIdentityRuntimeValue(input)
      let decoded = valueToHost[ChannelHandle](runtime.value)
      generated.id == input.id and generated.label == input.label and
        decoded.id == input.id and decoded.label == input.label,
    shrinkInt)
  if not genericOpaqueIdentityCases:
    quit(1)

  let genericNatIndexCases = forAll(
    "generic Nat indices cross typed wrappers", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let input = IndexedChannelHandle(index: id, label: "generic-index/" & $id)
      let typed = generatedGenericIndexedChannelIdentity[17](input)
      let typedRuntime = generatedGenericIndexedChannelIdentityRuntimeValue[17](
        input)
      let rawRuntime = generatedGenericIndexedChannelIdentityRuntimeValue[17](
        [toHostValue(input)])
      typed == input and
        valueToHost[IndexedChannelHandle](typedRuntime.value) == input and
        valueToHost[IndexedChannelHandle](rawRuntime.value) == input,
    shrinkInt)
  if not genericNatIndexCases:
    quit(1)

  let genericNatBodyCases = forAll(
    "Nat generic values are available in checked runtime bodies", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let typedRuntime = generatedGenericNatValueRuntimeValue[17](value)
      let rawRuntime = generatedGenericNatValueRuntimeValue[17]([intToValue(value)])
      generatedGenericNatValue[17](value) == 17 and
        valueToNat(typedRuntime.value, typedRuntime.globals) == 17 and
        valueToNat(rawRuntime.value, rawRuntime.globals) == 17,
    shrinkInt)
  if not genericNatBodyCases:
    quit(1)

  let vectorCodecCases = forAll(
    "length-indexed Vec values cross as checked Nim sequences", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(seed: int): bool =
      let values = @[seed, seed + 1, seed + 2, seed + 3]
      let handles = @[
        ChannelHandle(id: seed, label: "vec/" & $seed),
        ChannelHandle(id: seed + 1, label: "vec/" & $(seed + 1)),
        ChannelHandle(id: seed + 2, label: "vec/" & $(seed + 2)),
        ChannelHandle(id: seed + 3, label: "vec/" & $(seed + 3))]
      generatedVectorIdentity[int, 4](values) == values and
        generatedVectorIdentity[ChannelHandle, 4](handles) == handles,
    shrinkInt)
  if not vectorCodecCases:
    quit(1)
  let vectorArrayCases = forAll(
    "length-indexed Vec values bridge to fixed Nim arrays", r, 200,
    proc(r: var Rng): TestIntArray =
      for i in low(result) .. high(result):
        result[i] = r.genInt(-1000, 1000),
    proc(input: TestIntArray): bool =
      let checked = generatedArrayVecIdentity(input)
      let runtime = generatedArrayVecIdentityRuntimeValue(input)
      let decoded = vecValueToArray[3, int](runtime.value, 3, runtime.globals,
        "Vec", proc(value: Value, globals: Globals): int = valueToInt(value))
      checked == input and decoded == input,
    proc(input: TestIntArray): seq[TestIntArray] =
      var smaller = input
      for i in low(smaller) .. high(smaller): smaller[i] = 0
      @[smaller])
  if not vectorArrayCases:
    quit(1)
  let nestedVectorArrayCases = forAll(
    "nested length-indexed vectors bridge to nested Nim arrays", r, 200,
    proc(r: var Rng): TestIntMatrixArray =
      for row in low(result) .. high(result):
        for column in low(result[row]) .. high(result[row]):
          result[row][column] = r.genInt(-1000, 1000),
    proc(input: TestIntMatrixArray): bool =
      let checked = generatedArrayMatrixIdentity(input)
      let runtime = generatedArrayMatrixIdentityRuntimeValue(input)
      let decoded = vecValueToArray[3, array[2, int]](runtime.value, 3,
        runtime.globals, "Vec", proc(row: Value, globals: Globals):
        array[2, int] = vecValueToArray[2, int](row, 2, globals, "Vec",
          proc(item: Value, _: Globals): int = valueToInt(item)))
      checked == input and decoded == input,
    proc(input: TestIntMatrixArray): seq[TestIntMatrixArray] =
      var smaller = input
      for row in low(smaller) .. high(smaller):
        for column in low(smaller[row]) .. high(smaller[row]):
          smaller[row][column] = 0
      @[smaller])
  if not nestedVectorArrayCases:
    quit(1)
  let mappedGenericTypeCases = forAll(
    "mapped Nim generic types are available in checked bodies", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(seed: int): bool =
      let input = ChannelHandle(id: seed, label: "generic/" & $seed)
      let checked = generatedTypeAwareSingleton(input)
      let runtime = generatedTypeAwareSingletonRuntimeValue(input)
      let decoded = vecValueToSeq[ChannelHandle](runtime.value, 1,
        runtime.globals, "Vec", proc(value: Value, _: Globals): ChannelHandle =
          valueToHost[ChannelHandle](value))
      checked == @[input] and decoded == @[input],
    shrinkInt)
  if not mappedGenericTypeCases:
    quit(1)
  let mappedGenericCodecCases = forAll(
    "custom runtimeCodec mappings apply to generic checked bodies", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(seed: int): bool =
      let input = ChannelHandle(id: seed, label: "codec-generic/" & $seed)
      let expected = @[ChannelHandle(id: seed, label: "decoded-" & $seed)]
      let checked = generatedCodecTypeAwareSingleton(input)
      let runtime = generatedCodecTypeAwareSingletonRuntimeValue(input)
      let representedElementType = runtimeGlobalValue(runtime.globals,
        "RuntimeHandle")
      let expectedVectorType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Vec"),
        [representedElementType, natToValue(1, runtime.globals)])
      validateRuntimeValueType(runtime.value, expectedVectorType,
        runtime.globals)
      let decoded = vecValueToSeq[ChannelHandle](runtime.value, 1,
        runtime.globals, "Vec", decodeRuntimeHandle)
      checked == expected and decoded == expected,
    shrinkInt)
  if not mappedGenericCodecCases:
    quit(1)
  let vectorArrayOpaqueCases = forAll(
    "fixed Nim arrays preserve explicitly mapped opaque elements", r, 200,
    proc(r: var Rng): TestChannelArray =
      for i in low(result) .. high(result):
        let id = r.genInt(-1000, 1000)
        result[i] = ChannelHandle(id: id, label: "array-channel-" & $id),
    proc(input: TestChannelArray): bool =
      let checked = generatedChannelArrayIdentity(input)
      let runtime = generatedChannelArrayIdentityRuntimeValue(input)
      let decoded = vecValueToArray[3, ChannelHandle](runtime.value, 3,
        runtime.globals, "Vec", proc(value: Value, globals: Globals):
        ChannelHandle = valueToHost[ChannelHandle](value))
      checked == input and decoded == input,
    proc(input: TestChannelArray): seq[TestChannelArray] =
      var smaller = input
      for i in low(smaller) .. high(smaller):
        smaller[i] = ChannelHandle(id: 0, label: "array-channel-0")
      @[smaller])
  if not vectorArrayOpaqueCases:
    quit(1)
  let vectorArrayCallbackCases = forAll(
    "fixed Nim arrays cross checked closure arguments and results", r, 200,
    proc(r: var Rng): TestIntArray =
      for i in low(result) .. high(result):
        result[i] = r.genInt(-1000, 1000),
    proc(input: TestIntArray): bool =
      let callback = proc(values: TestIntArray): TestIntArray {.closure.} =
        for i in low(result) .. high(result): result[i] = values[high(values) - i]
      var expected: TestIntArray
      for i in low(expected) .. high(expected):
        expected[i] = input[high(input) - i]
      generatedArrayVecCallback(callback, input) == expected,
    proc(input: TestIntArray): seq[TestIntArray] =
      var smaller = input
      for i in low(smaller) .. high(smaller): smaller[i] = 0
      @[smaller])
  if not vectorArrayCallbackCases:
    quit(1)
  let dependentCallbackCases = forAll(
    "callback result codecs receive their dependent Nat argument", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let expected = makeIndexedRuntimeValues(length)
      let typed = generatedApplyIndexedCallback(makeIndexedRuntimeValues,
        length)
      let runtime = generatedApplyIndexedCallbackRuntimeValue(
        makeIndexedRuntimeValues, length)
      typed == expected and vecValueToSeq[int](runtime.value, length,
        runtime.globals, "Vec", proc(item: Value, _: Globals): int =
          valueToInt(item)) == expected,
    shrinkInt)
  if not dependentCallbackCases:
    quit(1)
  let trailingDependentCallbackCases = forAll(
    "callback result-only trailing indices infer through aliases", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let seed = length * 3 - 50
      let callback = proc(seedArg, callbackLength: int): seq[int] {.closure.} =
        for i in 0 ..< callbackLength: result.add(seedArg + i)
      var expected: seq[int] = @[]
      for i in 0 ..< length: expected.add(seed + i)
      generatedApplyTrailingIndexedCallback(callback, seed, length) == expected,
    shrinkInt)
  if not trailingDependentCallbackCases:
    quit(1)
  var dependentCallbackMismatchRejected = false
  try:
    discard generatedApplyIndexedCallback(makeWrongIndexedRuntimeValues, 3)
  except ValueError as error:
    dependentCallbackMismatchRejected = "runtime Vec length mismatch" in error.msg
  doAssert dependentCallbackMismatchRejected
  let dependentCallbackArgumentCases = forAll(
    "callback arguments carry earlier indices into dependent codecs", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let values = makeIndexedRuntimeValues(length)
      let applied = generatedApplyDependentVectorCallback(
        checkDependentVectorCallback, length, values)
      let runtimeApplied = generatedApplyDependentVectorCallbackRuntimeValue(
        checkDependentVectorCallback, length, values)
      let returned = generatedDependentVectorCallback()
      let returnedValue = returned(length, values)
      let runtimeReturned = generatedDependentVectorCallbackRuntimeValue()
      let runtimeReturnedValue = valueToNat(callRuntimeValue(
        runtimeReturned.value, [natToValue(length, runtimeReturned.globals),
          seqToVecValue[int](values, length, runtimeReturned.globals, "Vec",
            proc(item: int, _: Globals): Value = intToValue(item))]),
        runtimeReturned.globals)
      applied == length and valueToNat(runtimeApplied.value,
        runtimeApplied.globals) == length and
        returnedValue == length and runtimeReturnedValue == length,
    shrinkInt)
  if not dependentCallbackArgumentCases:
    quit(1)
  var dependentCallbackArgumentMismatchRejected = false
  try:
    discard generatedApplyDependentVectorCallback(checkDependentVectorCallback,
      3, @[1, 2])
  except ValueError as error:
    dependentCallbackArgumentMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert dependentCallbackArgumentMismatchRejected
  let boundCheckedCallbackCases = forAll(
    "typed postulates invoke checked Eponym callback parameters", r, 200,
    proc(r: var Rng): tuple[input, offset: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[input, offset: int]): bool =
      let callback: NimIntCallback = proc(value: int): int =
        value + input.offset
      let expected = input.input + input.offset
      let typed = generatedApplyCheckedIntCallback(callback, input.input)
      let runtime = generatedApplyCheckedIntCallbackRuntimeValue(
        callback, input.input)
      typed == expected and valueToInt(runtime.value) == expected)
  if not boundCheckedCallbackCases:
    quit(1)
  let futureCallbackCases = forAll(
    "typed callback adapters pass Future results through opaquely", r, 200,
    proc(r: var Rng): tuple[channelId, offset: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[channelId, offset: int]): bool =
      let channel = ChannelHandle(id: input.channelId, label: "future-callback")
      let future = newFuture[int]("futureCallbackProperty")
      future.complete(input.channelId + input.offset)
      let callback: proc(channel: ChannelHandle): Future[int] {.closure.} =
        proc(channel: ChannelHandle): Future[int] = future
      let generated = generatedInvokeFutureCallback(callback, channel)
      let runtime = generatedInvokeFutureCallbackRuntimeValue(callback, channel)
      generated == future and generated.read == input.channelId + input.offset and
        valueToHost[Future[int]](runtime.value) == future)
  if not futureCallbackCases:
    quit(1)
  let genericFutureCallbackCases = forAll(
    "generic Nim callbacks preserve opaque Future results", r, 200,
    proc(r: var Rng): tuple[channelId, resultValue: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[channelId, resultValue: int]): bool =
      let channel = ChannelHandle(id: input.channelId, label: "generic-future")
      let future = newFuture[int]("genericFutureCallbackProperty")
      future.complete(input.resultValue)
      let callback: proc(channel: ChannelHandle): Future[int] {.closure.} =
        proc(channel: ChannelHandle): Future[int] = future
      let generated = generatedApplyGenericFutureCallbackDynamic(callback,
        channel)
      let runtime = generatedApplyGenericFutureCallbackRuntimeValueDynamic(
        callback, channel)
      let resultType = runtimeGlobalValue(runtime.globals, "PendingResult")
      generated == future and generated.read == input.resultValue and
        valueToHostAtRuntimeType[Future[int]](runtime.value, resultType,
          runtime.globals) == future)
  if not genericFutureCallbackCases:
    quit(1)
  let asyncGenericCallbackCases = forAll(
    "async Nim callbacks cross typed postulates and dynamic generic binders",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(channelId: int): bool =
      let channel = ChannelHandle(id: channelId, label: "async-generic")
      let generated = generatedApplyGenericFutureCallbackDynamic(
        hostAsyncChannelResult, channel)
      let runtime = generatedApplyGenericFutureCallbackRuntimeValueDynamic(
        hostAsyncChannelResult, channel)
      let resultType = runtimeGlobalValue(runtime.globals, "PendingResult")
      let runtimeFuture = valueToHostAtRuntimeType[Future[int]](runtime.value,
        resultType, runtime.globals)
      let postulateResult = generatedInvokeFutureCallback(hostAsyncChannelResult,
        channel)
      let postulateRuntime = generatedInvokeFutureCallbackRuntimeValue(
        hostAsyncChannelResult, channel)
      let postulateType = runtimeGlobalValue(postulateRuntime.globals,
        "PendingResult")
      let postulateRuntimeFuture = valueToHostAtRuntimeType[Future[int]](
        postulateRuntime.value, postulateType, postulateRuntime.globals)
      waitFor(generated) == channelId and waitFor(runtimeFuture) == channelId and
        waitFor(postulateResult) == channelId and
        waitFor(postulateRuntimeFuture) == channelId)
  if not asyncGenericCallbackCases:
    quit(1)
  let voidCallbackCases = forAll(
    "typed callback adapters support Nim void callbacks", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      var seen: seq[int] = @[]
      let callback: proc(value: int) {.closure.} =
        proc(value: int) = seen.add(value)
      generatedInvokeVoidCallback(callback, value)
      let runtime = generatedInvokeVoidCallbackRuntimeValue(callback, value + 1)
      validateRuntimeUnitValue(runtime.value)
      seen == @[value, value + 1],
    shrinkInt)
  if not voidCallbackCases:
    quit(1)
  let nullaryCallbackCases = forAll(
    "typed callback adapters support nullary Nim callbacks", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let callback: proc(): int {.closure.} = proc(): int = value
      let generated = generatedInvokeNullaryCallback(callback)
      let runtime = generatedInvokeNullaryCallbackRuntimeValue(callback)
      let returned = generatedReturnNullaryInt()
      let returnedRuntime = generatedReturnNullaryIntRuntimeValue()
      let rawCallback: proc(): Value {.closure.} = proc(): Value =
        intToValue(value)
      let rawGenerated = generatedInvokeRawNullaryCallback(rawCallback)
      let rawRuntime = generatedInvokeRawNullaryCallbackRuntimeValue(rawCallback)
      generated == value and valueToInt(runtime.value) == value and
        returned() == 17 and
        valueToInt(callRuntimeValue(returnedRuntime.value,
          @[vUnit()])) == 17 and rawGenerated == value and
        valueToInt(rawRuntime.value) == value,
    shrinkInt)
  if not nullaryCallbackCases:
    quit(1)
  let importedBoundCallbackCases = forAll(
    "imported postulates invoke checked Nim callbacks", r, 200,
    proc(r: var Rng): tuple[input, offset: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[input, offset: int]): bool =
      let callback: NimIntCallback = proc(value: int): int =
        value + input.offset
      let expected = input.input + input.offset
      let typed = importedApplyCheckedIntCallback(callback, input.input)
      let runtime = importedApplyCheckedIntCallbackRuntimeValue(
        callback, input.input)
      typed == expected and valueToInt(runtime.value) == expected)
  if not importedBoundCallbackCases:
    quit(1)
  let boundDependentCallbackCases = forAll(
    "typed postulates preserve outer indices through callback codecs", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      let callback: proc(index: int): seq[int] {.closure.} =
        proc(index: int): seq[int] =
          for i in 0 ..< input.length: result.add(input.seed + index + i)
      let expected = block:
        var values: seq[int] = @[]
        for i in 0 ..< input.length:
          values.add(input.seed + input.length + i)
        values
      let typed = generatedApplyIndexedVectorCallback(input.length, callback)
      let runtime = generatedApplyIndexedVectorCallbackRuntimeValue(
        input.length, callback)
      typed == expected and
        vecValueToSeq[int](runtime.value, input.length, runtime.globals,
          "Vec", proc(value: Value, _: Globals): int = valueToInt(value)) ==
          expected)
  if not boundDependentCallbackCases:
    quit(1)
  var boundDependentCallbackMismatchRejected = false
  try:
    discard generatedApplyIndexedVectorCallback(3,
      proc(index: int): seq[int] = @[index, index + 1, index + 2, index + 3])
  except ValueError as error:
    boundDependentCallbackMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert boundDependentCallbackMismatchRejected

  let dynamicGenericVectorCases = forAll(
    "dynamic Nat generics index dependent Vec wrappers", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(index: int): bool =
      var values: seq[int] = @[]
      for i in 0 .. index: values.add(i - index)
      generatedVectorSucIndexDynamic(index, values) == index,
    shrinkInt)
  if not dynamicGenericVectorCases:
    quit(1)
  var dynamicGenericMismatchRejected = false
  try:
    discard generatedVectorSucIndexDynamic(3, @[1, 2])
  except ValueError as error:
    dynamicGenericMismatchRejected = "runtime Vec length mismatch" in error.msg
  doAssert dynamicGenericMismatchRejected
  doAssert generatedVectorIdentity[int, 0](@[]) == @[]
  doAssert generatedVectorSucIndex[3](@[1, 2, 3, 4]) == 3
  doAssert generatedVectorAddIndex[2, 3](@[1, 2, 3, 4, 5]) == 0
  var wrongVectorLengthRejected = false
  try:
    discard generatedVectorIdentity[int, 4](@[1, 2, 3])
  except ValueError as error:
    wrongVectorLengthRejected = "runtime Vec length mismatch" in error.msg
  doAssert wrongVectorLengthRejected

  let listCodecCases = forAll(
    "length-independent List values cross as checked Nim sequences", r, 200,
    proc(r: var Rng): tuple[length: int, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length: int, seed: int]): bool =
      var values = newSeq[int](input.length)
      var handles = newSeq[ChannelHandle](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
        handles[i] = ChannelHandle(id: input.seed + i,
          label: "list/" & $(input.seed + i))
      let intRuntime = generatedIntListIdentityRuntimeValue(values)
      let rawIntRuntime = generatedIntListIdentityRuntimeValue([intRuntime.value])
      let runtime = generatedListIdentityRuntimeValue[int](values)
      let rawRuntime = generatedListIdentityRuntimeValue[int]([runtime.value])
      let opaqueRuntime = generatedListIdentityRuntimeValue[ChannelHandle](handles)
      generatedIntListIdentity(values) == values and
      generatedListIdentity[int](values) == values and
        generatedListIdentity[ChannelHandle](handles) == handles and
        decodeRuntimeIntList(intRuntime.value, intRuntime.globals) == values and
        decodeRuntimeIntList(rawIntRuntime.value, rawIntRuntime.globals) == values and
        decodeRuntimeHostList[int](runtime.value, runtime.globals) == values and
        decodeRuntimeHostList[int](rawRuntime.value, rawRuntime.globals) == values and
        decodeRuntimeChannelList(opaqueRuntime.value,
          opaqueRuntime.globals) == handles)
  if not listCodecCases:
    quit(1)
  doAssert generatedListIdentity[int](@[]) == @[]

  let optionCodecCases = forAll(
    "Option values cross as checked none/some constructors", r, 200,
    proc(r: var Rng): tuple[present: bool, seed: int] =
      (r.genBool(), r.genInt(-1000, 1000)),
    proc(input: tuple[present: bool, seed: int]): bool =
      let value = if input.present: some(input.seed) else: none(int)
      let runtime = generatedOptionIdentityRuntimeValue[int](value)
      let rawRuntime = generatedOptionIdentityRuntimeValue[int]([runtime.value])
      let decoded = valueToOption[int](runtime.value, runtime.globals, "Option",
        proc(item: Value, _: Globals): int = valueToHost[int](item))
      let rawDecoded = valueToOption[int](rawRuntime.value, rawRuntime.globals,
        "Option", proc(item: Value, _: Globals): int = valueToHost[int](item))
      let primitiveRuntime = generatedPrimitiveOptionIdentityRuntimeValue(value)
      let primitiveDecoded = valueToOption[int](primitiveRuntime.value,
        primitiveRuntime.globals, "Option",
        proc(item: Value, _: Globals): int = valueToInt(item))
      let opaque = some(ChannelHandle(id: input.seed,
        label: "option/" & $input.seed))
      let nested = some(value)
      generatedOptionIdentity[int](value) == value and
        generatedOptionIdentity[ChannelHandle](opaque) == opaque and
        generatedPrimitiveOptionIdentity(value) == value and
        generatedNestedOptionIdentity(nested) == nested and
        decoded == value and rawDecoded == value and primitiveDecoded == value,
    )
  if not optionCodecCases:
    quit(1)
  let customCodecPostulateCases = forAll(
    "custom runtimeCodec values cross bound typed postulates", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let input = ChannelHandle(id: id, label: "adapter-input")
      let expected = ChannelHandle(id: id + 1,
        label: "decoded-" & $(id + 1))
      let typed = generatedRuntimeHandleAdapter(input)
      let runtime = generatedRuntimeHandleAdapterRuntimeValue(input)
      let raw = generatedRuntimeHandleAdapterRuntimeValue([
        encodeRuntimeHandle(input, runtime.globals)])
      typed == expected and
        decodeRuntimeHandle(runtime.value, runtime.globals) == expected and
        decodeRuntimeHandle(raw.value, raw.globals) == expected,
    shrinkInt)
  if not customCodecPostulateCases:
    quit(1)
  let customCodecOptionPostulateCases = forAll(
    "typed postulates accept applied structural codec types", r, 200,
    proc(r: var Rng): tuple[present: bool, id: int] =
      (r.genBool(), r.genInt(-1000, 1000)),
    proc(input: tuple[present: bool, id: int]): bool =
      let host = if input.present:
        some(ChannelHandle(id: input.id, label: "host-option"))
      else:
        none(ChannelHandle)
      let expected = if input.present:
        some(ChannelHandle(id: input.id, label: "decoded-" & $input.id))
      else:
        none(ChannelHandle)
      let typed = generatedRuntimeHandleOptionAdapter(host)
      let runtime = generatedRuntimeHandleOptionAdapterRuntimeValue(host)
      let raw = generatedRuntimeHandleOptionAdapterRuntimeValue([
        optionToValue(host, runtime.globals, "Option", encodeRuntimeHandle)])
      typed == expected and
        valueToOption[ChannelHandle](runtime.value, runtime.globals, "Option",
          decodeRuntimeHandle) == expected and
        valueToOption[ChannelHandle](raw.value, raw.globals, "Option",
          decodeRuntimeHandle) == expected)
  if not customCodecOptionPostulateCases:
    quit(1)
  let importedAppliedPostulateCases = forAll(
    "imported typed postulates preserve applied codec signatures", r, 200,
    proc(r: var Rng): tuple[present: bool, value: int] =
      (r.genBool(), r.genInt(-1000, 1000)),
    proc(input: tuple[present: bool, value: int]): bool =
      let host = if input.present: some(input.value) else: none(int)
      let typed = importedOptionIdentity(host)
      let runtime = importedOptionIdentityRuntimeValue(host)
      let raw = importedOptionIdentityRuntimeValue([
        optionToValue(host, runtime.globals, "Option",
          proc(value: int, globals: Globals): Value = intToValue(value))])
      typed == host and
        valueToOption[int](runtime.value, runtime.globals, "Option",
          proc(value: Value, globals: Globals): int = valueToInt(value)) == host and
        valueToOption[int](raw.value, raw.globals, "Option",
          proc(value: Value, globals: Globals): int = valueToInt(value)) == host)
  if not importedAppliedPostulateCases:
    quit(1)
  let dependentPostulateCodecCases = forAll(
    "typed postulates carry earlier Nat indices into structural codecs", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var values: seq[int] = @[]
      for i in 0 ..< input.length: values.add(input.seed + i)
      let typed = generatedIndexedIntVectorIdentity(input.length, values)
      let runtime = generatedIndexedIntVectorIdentityRuntimeValue(
        input.length, values)
      let vector = seqToVecValue(values, input.length, runtime.globals, "Vec",
        proc(value: int, globals: Globals): Value = intToValue(value))
      let raw = generatedIndexedIntVectorIdentityRuntimeValue([
        natToValue(input.length, runtime.globals), vector])
      typed == values and
        vecValueToSeq[int](runtime.value, input.length, runtime.globals, "Vec",
          proc(value: Value, globals: Globals): int = valueToInt(value)) == values and
        vecValueToSeq[int](raw.value, input.length, raw.globals, "Vec",
          proc(value: Value, globals: Globals): int = valueToInt(value)) == values)
  if not dependentPostulateCodecCases:
    quit(1)
  let dependentOpaquePostulateCodecCases = forAll(
    "dependent postulate codecs preserve opaque Vec element mappings", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var values: seq[ChannelHandle] = @[]
      var expected: seq[ChannelHandle] = @[]
      for i in 0 ..< input.length:
        values.add(ChannelHandle(id: input.seed + i, label: "input/" & $i))
        expected.add(ChannelHandle(id: input.seed + i + 1,
          label: "decoded-" & $(input.seed + i + 1)))
      let typed = generatedIndexedRuntimeHandleVectorAdapter(
        input.length, values)
      let runtime = generatedIndexedRuntimeHandleVectorAdapterRuntimeValue(
        input.length, values)
      let rawVector = seqToVecValue(values, input.length, runtime.globals,
        "Vec", encodeRuntimeHandle)
      let raw = generatedIndexedRuntimeHandleVectorAdapterRuntimeValue([
        natToValue(input.length, runtime.globals), rawVector])
      var wrongTypedRejected = false
      var wrongRuntimeRejected = false
      var wrongRawRejected = false
      try:
        discard generatedIndexedRuntimeHandleVectorAdapter(input.length,
          values & @[ChannelHandle(id: input.seed, label: "extra")])
      except ValueError:
        wrongTypedRejected = true
      try:
        discard generatedIndexedRuntimeHandleVectorAdapterRuntimeValue(
          input.length, values & @[ChannelHandle(id: input.seed, label: "extra")])
      except ValueError:
        wrongRuntimeRejected = true
      let wrongValues = values & @[
        ChannelHandle(id: input.seed, label: "extra")]
      let wrongRawVector = seqToVecValue(wrongValues, wrongValues.len,
        runtime.globals, "Vec", encodeRuntimeHandle)
      try:
        discard generatedIndexedRuntimeHandleVectorAdapterRuntimeValue([
          natToValue(input.length, runtime.globals), wrongRawVector])
      except ValueError:
        wrongRawRejected = true
      typed == expected and wrongTypedRejected and wrongRuntimeRejected and
        wrongRawRejected and
        vecValueToSeq[ChannelHandle](runtime.value, input.length,
          runtime.globals, "Vec", decodeRuntimeHandle) == expected and
        vecValueToSeq[ChannelHandle](raw.value, input.length,
          raw.globals, "Vec", decodeRuntimeHandle) == expected)
  if not dependentOpaquePostulateCodecCases:
    quit(1)
  let customCodecOptionCases = forAll(
    "runtimeOption recursively applies a custom runtimeCodec", r, 200,
    proc(r: var Rng): tuple[present: bool, id: int] =
      (r.genBool(), r.genInt(-1000, 1000)),
    proc(input: tuple[present: bool, id: int]): bool =
      let payload = ChannelHandle(id: input.id, label: "option/" & $input.id)
      let host = if input.present: some(payload) else: none(ChannelHandle)
      let expected = if input.present:
        some(ChannelHandle(id: input.id, label: "decoded-" & $input.id))
      else:
        none(ChannelHandle)
      let wrapperResult = generatedRuntimeHandleOptionIdentity(host)
      let runtime = generatedRuntimeHandleOptionIdentityRuntimeValue(host)
      let rawRuntime = generatedRuntimeHandleOptionIdentityRuntimeValue(
        [runtime.value])
      let decoded = valueToOption[ChannelHandle](runtime.value,
        runtime.globals, "Option", decodeRuntimeHandle)
      let rawDecoded = valueToOption[ChannelHandle](rawRuntime.value,
        rawRuntime.globals, "Option", decodeRuntimeHandle)
      wrapperResult == expected and decoded == expected and
        rawDecoded == expected)
  if not customCodecOptionCases:
    quit(1)
  let customCodecVectorCases = forAll(
    "runtimeVector recursively applies a custom runtimeCodec", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var host: seq[ChannelHandle] = @[]
      for i in 0 ..< input.length:
        host.add(ChannelHandle(id: input.seed + i, label: $i))
      let expected = decodedRuntimeHandles(host)
      let wrapper = generatedRuntimeHandleVectorIdentity(input.length, host)
      let runtime = generatedRuntimeHandleVectorIdentityRuntimeValue(
        input.length, host)
      let decoded = vecValueToSeq[ChannelHandle](runtime.value, input.length,
        runtime.globals, "Vec", decodeRuntimeHandle)
      let rawVector = seqToVecValue(host, input.length, runtime.globals, "Vec",
        encodeRuntimeHandle)
      let rawRuntime = generatedRuntimeHandleVectorIdentityRuntimeValue(
        [natToValue(input.length, runtime.globals), rawVector])
      let rawDecoded = vecValueToSeq[ChannelHandle](rawRuntime.value,
        input.length, rawRuntime.globals, "Vec", decodeRuntimeHandle)
      wrapper == expected and decoded == expected and rawDecoded == expected)
  if not customCodecVectorCases:
    quit(1)
  let customCodecListCases = forAll(
    "runtimeList recursively applies a custom runtimeCodec", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var host: seq[ChannelHandle] = @[]
      for i in 0 ..< input.length:
        host.add(ChannelHandle(id: input.seed + i, label: $i))
      let expected = decodedRuntimeHandles(host)
      let wrapper = generatedRuntimeHandleListIdentity(host)
      let runtime = generatedRuntimeHandleListIdentityRuntimeValue(host)
      let decoded = listValueToSeq[ChannelHandle](runtime.value,
        runtime.globals, "List", decodeRuntimeHandle)
      let rawList = seqToListValue(host, runtime.globals, "List",
        encodeRuntimeHandle)
      let rawRuntime = generatedRuntimeHandleListIdentityRuntimeValue([rawList])
      let rawDecoded = listValueToSeq[ChannelHandle](rawRuntime.value,
        rawRuntime.globals, "List", decodeRuntimeHandle)
      wrapper == expected and decoded == expected and rawDecoded == expected)
  if not customCodecListCases:
    quit(1)
  let optionGlobals = generatedPrimitiveOptionIdentityRuntimeValue(
    none(int)).globals
  var malformedOptionRejected = false
  try:
    discard valueToOption[int](intToValue(7), optionGlobals, "Option",
      proc(item: Value, _: Globals): int = valueToInt(item))
  except ValueError:
    malformedOptionRejected = true
  doAssert malformedOptionRejected

  let customCodecCases = forAll(
    "explicit Nim codecs bridge payload-bearing Eponym data", r, 200,
    proc(r: var Rng): seq[int] =
      result = newSeq[int](r.genInt(0, 8))
      for i in 0 ..< result.len:
        result[i] = r.genInt(-1000, 1000)
    ,
    proc(values: seq[int]): bool =
      let runtime = generatedTreeIdentityRuntimeValue(values)
      let rawRuntime = generatedTreeIdentityRuntimeValue([runtime.value])
      let rawTree = encodeRuntimeTree(values, runtime.globals)
      let rawTreeRuntime = generatedTreeIdentityRuntimeValue([rawTree])
      var malformedTreeRejected = false
      try:
        let malformedTree = callRuntimeValue(
          eval(runtime.globals["treeNode"].tm, @[]),
          [intToValue(1), intToValue(2)])
        discard generatedTreeIdentityRuntimeValue([malformedTree])
      except ValueError:
        malformedTreeRejected = true
      let typedRoundTrip = generatedTreeIdentity(values) == values
      let codecRoundTrip = decodeRuntimeTree(runtime.value,
        runtime.globals) == values
      let rawRoundTrip = decodeRuntimeTree(rawRuntime.value,
        rawRuntime.globals) == values
      let recursiveRawRoundTrip = decodeRuntimeTree(rawTreeRuntime.value,
        rawTreeRuntime.globals) == values
      typedRoundTrip and
        generatedBoundTreeReverse(values) == reverseRuntimeTree(values) and
        codecRoundTrip and rawRoundTrip and recursiveRawRoundTrip and
        malformedTreeRejected,
    )
  if not customCodecCases:
    quit(1)

  let nestedVectorCases = forAll(
    "nested length-indexed Vec values recurse through sequence codecs", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(seed: int): bool =
      let matrix = @[
        @[seed, seed + 1],
        @[seed + 2, seed + 3],
        @[seed + 4, seed + 5]]
      let runtime = generatedNestedVectorIdentityRuntimeValue[2, 3](matrix)
      let rawRuntime = generatedNestedVectorIdentityRuntimeValue[2, 3](
        [runtime.value])
      let rawInput = runtimeIntMatrix(matrix, runtime.globals)
      let rawInputRuntime = generatedNestedVectorIdentityRuntimeValue[2, 3](
        [rawInput])
      var rejectedMalformedNestedInput = false
      try:
        let malformed = runtimeIntMatrix(@[matrix[0], matrix[1] & @[seed]],
          runtime.globals)
        discard generatedNestedVectorIdentityRuntimeValue[2, 3]([malformed])
      except ValueError:
        rejectedMalformedNestedInput = true
      generatedNestedVectorIdentity[2, 3](matrix) == matrix and
        decodeRuntimeIntMatrix(runtime.value, 3, runtime.globals) == matrix and
        decodeRuntimeIntMatrix(rawRuntime.value, 3, rawRuntime.globals) == matrix and
        decodeRuntimeIntMatrix(rawInputRuntime.value, 3,
          rawInputRuntime.globals) == matrix and rejectedMalformedNestedInput,
    shrinkInt)
  if not nestedVectorCases:
    quit(1)

  let dependentRecordCases = forAll(
    "dependent records validate earlier Nat fields against Vec lengths",
    r, 200,
    proc(r: var Rng): tuple[prefixLength, suffixLength, seed: int] =
      (r.genInt(0, 4), r.genInt(0, 4), r.genInt(-1000, 1000)),
    proc(input: tuple[prefixLength, suffixLength, seed: int]): bool =
      let length = input.prefixLength + input.suffixLength
      var values = newSeq[int](length)
      for i in 0 ..< values.len:
        values[i] = input.seed + i
      let value = RuntimeSizedVec(prefixLength: input.prefixLength,
        suffixLength: input.suffixLength, values: values)
      let runtime = generatedSizedVecIdentityRuntimeValue(value)
      let rawRuntime = generatedSizedVecIdentityRuntimeValue([runtime.value])
      let malformedRawRecord = pairValue(natToValue(input.prefixLength,
        runtime.globals), pairValue(natToValue(input.suffixLength,
        runtime.globals), pairValue(runtimeIntVector(values & @[input.seed],
        runtime.globals), unitValue())))
      var rawRecordMismatchRejected = false
      try:
        discard generatedSizedVecIdentityRuntimeValue([malformedRawRecord])
      except ValueError:
        rawRecordMismatchRejected = true
      let runtimeLength = valueToNat(runtimePairFirst(runtime.value),
        runtime.globals) + valueToNat(runtimePairFirst(
          runtimePairSecond(runtime.value)), runtime.globals)
      let rawLength = valueToNat(runtimePairFirst(rawRuntime.value),
        rawRuntime.globals) + valueToNat(runtimePairFirst(
          runtimePairSecond(rawRuntime.value)), rawRuntime.globals)
      generatedSizedVecIdentity(value) == value and
        rawRecordMismatchRejected and
        runtimeLength == length and
        decodeRuntimeIntVector(runtimePairFirst(
          runtimePairSecond(runtimePairSecond(runtime.value))), runtimeLength,
          runtime.globals) == values and
        rawLength == length and
        decodeRuntimeIntVector(runtimePairFirst(
          runtimePairSecond(runtimePairSecond(rawRuntime.value))), rawLength,
          rawRuntime.globals) == values)
  if not dependentRecordCases:
    quit(1)
  var dependentRecordMismatchRejected = false
  try:
    discard generatedSizedVecIdentity(RuntimeSizedVec(prefixLength: 1,
      suffixLength: 2, values: @[1, 2]))
  except ValueError as error:
    dependentRecordMismatchRejected = "runtime Vec length mismatch" in error.msg
  doAssert dependentRecordMismatchRejected

  let genericBoolCases = forAll(
    "Bool generic values are available in checked runtime bodies", r, 200,
    proc(r: var Rng): tuple[ignored: int, expected: bool] =
      (r.genInt(-1000, 1000), r.genBool()),
    proc(input: tuple[ignored: int, expected: bool]): bool =
      let runtime = if input.expected:
        generatedGenericBoolValueRuntimeValue[true](input.ignored)
      else:
        generatedGenericBoolValueRuntimeValue[false](input.ignored)
      let rawRuntime = if input.expected:
        generatedGenericBoolValueRuntimeValue[true]([intToValue(input.ignored)])
      else:
        generatedGenericBoolValueRuntimeValue[false]([intToValue(input.ignored)])
      let typedResult = if input.expected:
        generatedGenericBoolValue[true](input.ignored)
      else:
        generatedGenericBoolValue[false](input.ignored)
      typedResult == input.expected and
        generatedGenericBoolValueDynamic(input.expected, input.ignored) ==
          input.expected and
        valueToBool(runtime.value, runtime.globals) == input.expected and
        valueToBool(rawRuntime.value, rawRuntime.globals) == input.expected)
  if not genericBoolCases:
    quit(1)

  let genericIntCases = forAll(
    "Int generic values are available in checked runtime bodies", r, 200,
    proc(r: var Rng): tuple[selector: int, ignored: int] =
      (r.genInt(0, 4), r.genInt(-1000, 1000)),
    proc(input: tuple[selector: int, ignored: int]): bool =
      case input.selector
      of 0: checkGenericIntValueAt[-17](input.ignored)
      of 1: checkGenericIntValueAt[-1](input.ignored)
      of 2: checkGenericIntValueAt[0](input.ignored)
      of 3: checkGenericIntValueAt[23](input.ignored)
      else: checkGenericIntValueAt[1000](input.ignored))
  if not genericIntCases:
    quit(1)

  let genericMappedCases = forAll(
    "explicitly mapped opaque values are available as runtime generics",
    r, 200,
    proc(r: var Rng): tuple[selector: int, ignored: int] =
      (r.genInt(0, 2), r.genInt(-1000, 1000)),
    proc(input: tuple[selector: int, ignored: int]): bool =
      case input.selector
      of 0: checkGenericChannelValueAt[
        ChannelHandle(id: 0, label: "generic-zero")](input.ignored)
      of 1: checkGenericChannelValueAt[
        ChannelHandle(id: 17, label: "generic-seventeen")](input.ignored)
      else: checkGenericChannelValueAt[
        ChannelHandle(id: -9, label: "generic-negative")](input.ignored))
  if not genericMappedCases:
    quit(1)

  let genericEnumCases = forAll(
    "mapped data constructors are available as runtime generics", r, 200,
    proc(r: var Rng): tuple[selector: int, ignored: int] =
      (r.genInt(0, 2), r.genInt(-1000, 1000)),
    proc(input: tuple[selector: int, ignored: int]): bool =
      case input.selector
      of 0: checkGenericSignalValueAt[signalStop](input.ignored)
      of 1: checkGenericSignalValueAt[signalCaution](input.ignored)
      else: checkGenericSignalValueAt[signalGo](input.ignored))
  if not genericEnumCases:
    quit(1)

  let callbackBridgeCases = forAll(
    "Nim closures cross into checked function arguments",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let factor = 3
      let callback: proc(value: int): int {.closure.} =
        proc(value: int): int = value * factor + 7
      generatedApplyNimCallback(callback, value) == value * factor + 7,
    shrinkInt)
  if not callbackBridgeCases:
    quit(1)

  let recordCallbackCases = forAll(
    "callable fields in mapped Nim records cross into Eponym",
    r, 200,
    proc(r: var Rng): tuple[input, multiplier, offset: int] =
      (r.genInt(-1000, 1000), r.genInt(-10, 10), r.genInt(-1000, 1000)),
    proc(input: tuple[input, multiplier, offset: int]): bool =
      let callback: NimIntCallback = proc(value: int): int =
        value * input.multiplier + input.offset
      let host = RuntimeCallbackRecord(callback: callback)
      let expected = input.input * input.multiplier + input.offset
      let typed = generatedApplyRecordCallback(host, input.input)
      let runtime = generatedApplyRecordCallbackRuntimeValue(host, input.input)
      typed == expected and valueToInt(runtime.value) == expected)
  if not recordCallbackCases:
    quit(1)

  let returnedClosureCases = forAll(
    "checked function results become callable Nim closures",
    r, 200,
    proc(r: var Rng): (int, int) = r.genPair(
      proc(r: var Rng): int = r.genInt(-1000, 1000),
      proc(r: var Rng): int = r.genInt(-1000, 1000)),
    proc(pair: (int, int)): bool =
      let adder = generatedAdder(pair[0])
      adder(pair[1]) == pair[0] + pair[1],
    proc(pair: (int, int)): seq[(int, int)] =
      pair.shrinkPair(shrinkInt, shrinkInt))
  if not returnedClosureCases:
    quit(1)

  for signal in [signalStop, signalCaution, signalGo]:
    if generatedSignalIdentity(signal) != signal:
      quit(1)
  let enumCodecCases = forAll(
    "nullary Eponym data constructors map to Nim enum values",
    r, 200,
    proc(r: var Rng): int = r.genInt(0, 2),
    proc(ordinal: int): bool =
      let signal = case ordinal
        of 0: signalStop
        of 1: signalCaution
        else: signalGo
      generatedSignalIdentity(signal) == signal,
    shrinkInt)
  if not enumCodecCases:
    quit(1)

  let quinaryWrapperCases = forAll(
    "five-argument opaque postulate dispatch", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let channel = ChannelHandle(id: id, label: "ch")
      let message = $id
      let actual = generatedRouteWithSampleRole(channel, message, id,
        -id, id * 2)
      actual.id == id and actual.label == "ch:" & message & "#" & $id &
        "/" & $(-id) & "/" & $(id * 2),
    shrinkInt)
  if not quinaryWrapperCases:
    quit(1)

  var opaqueBindings = initRuntimeBindings()
  bindHostOpaqueUnary[ChannelHandle](opaqueBindings, cachedGlobals,
    "rotateChannel", "Channel", hostRotateChannel)
  let originalChannel = ChannelHandle(id: 17, label: "socket")
  let opaqueResult = callValueFuncDir(baseDir, identityProgram, "opaqueRole",
    @[toHostValue(originalChannel)], opaqueBindings)
  let rotatedChannel = valueToHost[ChannelHandle](opaqueResult)
  if rotatedChannel.id != 18 or rotatedChannel.label != "socket*":
    quit(1)

  var binaryOpaqueBindings = initRuntimeBindings()
  bindHostOpaqueBinary[ChannelHandle, string, ChannelHandle](
    binaryOpaqueBindings, cachedGlobals, "routeChannel", "Channel", "Message",
    "Channel", hostRouteChannel)
  let routedValue = callValueFuncDir(baseDir, identityProgram, "routeRole",
    @[toHostValue(originalChannel), toHostValue("payload")],
    binaryOpaqueBindings)
  let routedChannel = valueToHost[ChannelHandle](routedValue)
  if routedChannel.id != originalChannel.id or
      routedChannel.label != "socket:payload":
    quit(1)
  var ternaryOpaqueBindings = initRuntimeBindings()
  bindHostOpaqueTernary[ChannelHandle, string, int, ChannelHandle](
    ternaryOpaqueBindings, cachedGlobals, "routeChannelWithId", "Channel",
    "Message", "RequestId", "Channel", hostRouteChannelWithId)
  let routedWithIdCases = forAll(
    "three-argument opaque postulate dispatch", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let channel = ChannelHandle(id: id, label: "ch")
      let message = $id
      let requestId = -id
      let value = callValueFuncDir(baseDir, identityProgram,
        "routeWithIdRole", @[toHostValue(channel), toHostValue(message),
          toHostValue(requestId)], ternaryOpaqueBindings)
      let actual = valueToHost[ChannelHandle](value)
      actual.id == id and actual.label == "ch:" & message & "#" &
        $requestId,
    shrinkInt)
  if not routedWithIdCases:
    quit(1)
  var quaternaryOpaqueBindings = initRuntimeBindings()
  bindHostOpaqueQuaternary[ChannelHandle, string, int, int, ChannelHandle](
    quaternaryOpaqueBindings, cachedGlobals, "routeChannelWithPhase",
    "Channel", "Message", "RequestId", "Phase", "Channel",
    hostRouteChannelWithPhase)
  let routedWithPhaseCases = forAll(
    "four-argument opaque postulate dispatch", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let channel = ChannelHandle(id: id, label: "ch")
      let message = $id
      let requestId = -id
      let phase = id mod 7
      let value = callValueFuncDir(baseDir, identityProgram,
        "routeWithPhaseRole", @[toHostValue(channel), toHostValue(message),
          toHostValue(requestId), toHostValue(phase)], quaternaryOpaqueBindings)
      let actual = valueToHost[ChannelHandle](value)
      actual.id == id and actual.label == "ch:" & message & "#" &
        $requestId & "/" & $phase,
    shrinkInt)
  if not routedWithPhaseCases:
    quit(1)
  let futureAdapterCases = forAll(
    "opaque Future[T] results from typed postulate adapters", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let future = generatedFutureRole(ChannelHandle(id: id, label: "ch"))
      future.finished and future.read() == id,
    shrinkInt)
  if not futureAdapterCases:
    quit(1)
  let callbackArgumentCases = forAll(
    "Nim closures passed through checked opaque callback parameters", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(offset: int): bool =
      let callback: NimIntCallback = proc(value: int): int = value + offset
      generatedCallbackRole(callback, offset * 2) == offset * 3,
    shrinkInt)
  if not callbackArgumentCases:
    quit(1)
  let mappedCallbackCases = forAll(
    "multi-argument callbacks use mapped opaque Nim values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let input = ChannelHandle(id: id, label: "callback-" & $id)
      let callback: proc(channel: ChannelHandle,
          message: string): ChannelHandle {.closure.} =
        proc(channel: ChannelHandle, message: string): ChannelHandle =
          result = channel
          result.label.add("/" & message)
      generatedApplyMappedCallback(callback, input, "mapped") ==
        ChannelHandle(id: id, label: "callback-" & $id & "/mapped"),
    shrinkInt)
  if not mappedCallbackCases:
    quit(1)
  let mappedReturnedCallbackCases = forAll(
    "checked multi-argument closures return mapped opaque Nim values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let input = ChannelHandle(id: id, label: "returned-" & $id)
      generatedReturnMappedCallback()(input, "mapped") ==
        ChannelHandle(id: id, label: "returned-" & $id & ":mapped"),
    shrinkInt)
  if not mappedReturnedCallbackCases:
    quit(1)
  let twoArgumentCallbackCases = forAll(
    "multi-argument Nim closures cross checked Eponym functions", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(seed: int): bool =
      let callback: proc(left, right: int): int {.closure.} =
        proc(left, right: int): int = left * 2 + right
      generatedApplyTwoArgumentCallback(callback, seed, -seed) == seed and
        generatedTwoArgumentAdder(seed)(seed + 1, seed + 2) ==
          seed + (seed + 1) + (seed + 2),
    shrinkInt)
  if not twoArgumentCallbackCases:
    quit(1)
  let generatedSixArgumentBindingCases = forAll(
    "typed postulate adapters support six curried arguments", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(a: int): bool =
      generatedSumSix(a, a + 1, a + 2, a + 3, a + 4, a + 5) ==
        6 * a + 15,
    shrinkInt)
  if not generatedSixArgumentBindingCases:
    quit(1)
  var wrongBinaryMappingRejected = false
  try:
    var wrongBindings = initRuntimeBindings()
    bindHostOpaqueBinary[ChannelHandle, string, ChannelHandle](wrongBindings,
      cachedGlobals, "routeChannel", "Channel", "Channel", "Channel",
      hostRouteChannel)
  except ValueError:
    wrongBinaryMappingRejected = true
  if not wrongBinaryMappingRejected:
    quit(1)
  let opaqueBinaryDispatch = forAll(
    "two-argument opaque postulate dispatch",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let channel = ChannelHandle(id: id, label: "ch")
      let message = $id
      let value = callValueFuncDir(baseDir, identityProgram, "routeRole",
        @[toHostValue(channel), toHostValue(message)], binaryOpaqueBindings)
      let actual = valueToHost[ChannelHandle](value)
      actual.id == id and actual.label == "ch:" & message,
    shrinkInt)
  if not opaqueBinaryDispatch:
    quit(1)

  var wrongOpaqueMappingRejected = false
  try:
    var wrongOpaqueBindings = initRuntimeBindings()
    bindHostOpaqueUnary[ChannelHandle](wrongOpaqueBindings, cachedGlobals,
      "rotateChannel", "WrongType", hostRotateChannel)
  except ValueError:
    wrongOpaqueMappingRejected = true
  var wrongNimOpaqueTypeRejected = false
  try:
    discard valueToHost[seq[int]](toHostValue(originalChannel))
  except ValueError:
    wrongNimOpaqueTypeRejected = true
  var opaqueConversionRejected = false
  try:
    var supply = Supply()
    areEqual(supply, vStar(), toHostValue(originalChannel),
             toHostValue(originalChannel))
  except ValueError:
    opaqueConversionRejected = true
  if not wrongOpaqueMappingRejected or not wrongNimOpaqueTypeRejected or
      not opaqueConversionRejected:
    quit(1)

  let opaqueRoundTrips = forAll("arbitrary Nim objects cross as opaque Values",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let value = ChannelHandle(id: id, label: $id)
      let decoded = valueToHost[ChannelHandle](toHostValue(value))
      decoded.id == value.id and decoded.label == value.label,
    shrinkInt)
  if not opaqueRoundTrips:
    quit(1)

  let mutableHostAdapter = forAll(
    "var Nim postulate adapters mutate mapped reference values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(initial: int): bool =
      let counter = MutableCounter(value: initial)
      let inspected = inspectChecked(counter)
      let generated = incrementChecked(counter)
      let runtimeInspection = inspectCheckedRuntimeValue(counter)
      let runtime = incrementCheckedRuntimeValue(counter)
      let runtimeCounter = valueToHost[MutableCounter](runtime.value)
      inspected == counter and
        valueToHost[MutableCounter](runtimeInspection.value) == counter and
        generated == counter and runtimeCounter == counter and
        counter.value == initial + 2,
    shrinkInt)
  if not mutableHostAdapter:
    quit(1)

  let mutableObjectAdapter = forAll(
    "var adapter returns updates to value objects", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(initial: int): bool =
      let counter = ValueCounter(value: initial)
      let updated = incrementValueCounterChecked(counter)
      counter.value == initial and updated.value == initial + 1,
    shrinkInt)
  if not mutableObjectAdapter:
    quit(1)

  let alternateHostDispatch = forAll("runtime bindings stay local to each call",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      var bindings = initRuntimeBindings()
      bindings.bindHostIntUnary(cachedGlobals, "hostStep", hostTripleNim)
      let value = callValueFuncDir(baseDir, identityProgram, "throughHelper",
        @[intToValue(n)], bindings)
      valueToInt(value) == hostTripleNim(n),
    shrinkInt)
  if not alternateHostDispatch:
    quit(1)

  var wrongEponymTypeRejected = false
  try:
    var wrongTypeBindings = initRuntimeBindings()
    wrongTypeBindings.bindHostIntUnary(cachedGlobals, "hostNat", hostStepNim)
  except ValueError:
    wrongEponymTypeRejected = true
  var duplicateBindingRejected = false
  try:
    runtimeBindings.bindHostIntUnary(cachedGlobals, "hostStep", hostStepNim)
  except ValueError:
    duplicateBindingRejected = true
  if not wrongEponymTypeRejected or not duplicateBindingRejected:
    quit(1)

  echo "test_runtime_value_bridge: Value calls, postulate identity, and typed host dispatch ok"
