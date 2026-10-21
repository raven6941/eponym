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
proc hostNimcallIncrement(value: int): int = value + 1
proc hostCdeclStepNim(value: int): int {.cdecl.} = value + 9
proc hostString(value: string): string = value
proc hostFailureNim(value: int): int =
  raise newException(IOError, "host adapter failed")
proc rawRuntimeIdentity(value: Value): Value = value
proc makeIndexedRuntimeValues(length: int): seq[int] =
  for i in 0 ..< length: result.add(i - length)
proc makeWrongIndexedRuntimeValues(length: int): seq[int] =
  newSeq[int](length + 1)
proc checkDependentVectorCallback(length: int, values: seq[int]): int =
  if values.len != length:
    raise newException(ValueError, "callback Vec length mismatch")
  length
proc identityDependentVectorCallback(length: int,
    values: seq[int]): seq[int] =
  if values.len != length:
    raise newException(ValueError, "callback Vec length mismatch")
  values
proc runtimeTreePayloads(value: Value, globals: Globals): seq[int] =
  var current = value
  while true:
    let variant = valueToRuntimeVariant(current, globals, "RuntimeTree",
      ["treeEmpty", "treeNode"])
    if variant.constructor == "treeEmpty": return
    result.add(valueToInt(variant.arguments[0]))
    current = variant.arguments[1]

type ChannelHandle = object
  id: int
  label: string

type NimIntCallback = proc(value: int): int {.closure.}
type RawRuntimeCallback = proc(value: Value): Value {.closure.}

type RuntimePoint = object
  x: int
  channel: ChannelHandle

type RuntimeEnvelope = object
  point: RuntimePoint
  note: string

type RuntimeSizedVec = object
  prefixLength: int
  suffixLength: int
  values: seq[int]

type RuntimeCheckedSizedVec = object
  length: int
  values: seq[seq[int]]

type RuntimeDependentPairEnvelope = object
  base: int
  payload: tuple[count: int, values: seq[int]]

type IndexedChannelHandle = object
  index: int
  label: string

type BaseRuntimeHandle = ref object of RootObj
  id: int

type DerivedRuntimeHandle = ref object of BaseRuntimeHandle
  label: string

type RuntimeSignal = enum
  signalStop, signalCaution, signalGo

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

proc hostWrongRoute(channel: int, message: string): int = channel + message.len

proc hostSumSix(a, b, c, d, e, f: int): int = a + b + c + d + e + f

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
  postulate(hostPlusSeven, Int -> Int)
  bindPostulate(hostPlusSeven, hostStepNim)
  proc generatedCheckedRole(value: Int): Int = hostPlusSeven(value)
  proc generatedDefault(value: Int = 42): Int = value
  proc generatedAdd(left: Int, right: Int): Int = addInt(left, right)
  proc generatedNamedAdd(left: Int, right: Int): Int =
    generatedAdd(right = right, left = left)
  proc generatedNamedAlias(left: Int, right: Int): Int =
    let operation = generatedAdd
    operation(right = right, left = left)
  proc generatedDefaultThenValue(value: Int = 42,
      adjustment: Int): Int = addInt(value, adjustment)
  proc generatedDefaultGap(adjustment: Int): Int =
    generatedDefaultThenValue(adjustment = adjustment)
  proc generatedTrailingDefault(value: Int, adjustment: Int = 5): Int =
    addInt(value, adjustment)
  proc generatedTrailingDefaultCall(value: Int): Int =
    generatedTrailingDefault(value)
  runtimeValue(generatedDefault)
  proc generatedNatId(value: Nat): Nat = value
  proc generatedSigmaId(value: Sig(Nat, Int)): Sig(Nat, Int) = value
  proc generatedArithmetic(left: Int, right: Int, scale: Int): Int =
    let difference = left - right
    let subtotal = difference + -right
    subtotal * scale
  proc generatedChooseTrue(): Int =
    if true: addInt(19, 0) else: addInt(17, 0)
  proc generatedChooseFalse(): Int =
    if false: addInt(19, 0) else: addInt(17, 0)

eponymBlock:
  import "fixtures/runtime_imported_value.ep"
  bindPostulate(importedStep, hostStepNim)
  runtimeType(Channel, ChannelHandle)
  runtimeType(Sample, int)
  runtimeList(List)
  runtimeValue(importedIdentity)
  runtimeValue(importedGenericIdentity)
  runtimeValue(importedListMap)
  runtimeValue(importedApply)

eponymBlock:
  import "fixtures/runtime_imported_indexed_callback.ep"
  runtimeVector(Vec)
  runtimeValue(importedApplyVectorCallback)

eponymBlock:
  import "fixtures/runtime_imported_dependent_callback.ep"
  runtimeVector(Vec)
  runtimeValue(importedDependentVectorCallback)

eponymBlock:
  import "fixtures/runtime_imported_vec.ep"
  runtimeVector(Vec)
  runtimeValue(importedVectorIdentity)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  import "../lib/bool.ep"
  runtimeVariant(RuntimeTree)
  runtimeVariant(SizedTree)
  runtimeVariant(SizedVector)
  runtimeValue(treeIdentity)
  proc genericIndexedTreeProjection[length: Nat,
      tree: SizedTree[length]](ignored: Int): SizedTree[length] = tree
  runtimeValue(genericIndexedTreeProjection)
  proc genericConditionalIndexedTreeProjection[b: Bool, n, m: Nat,
      tree: SizedTree[if b: n else: m]](ignored: Int):
      SizedTree[if b: n else: m] = tree
  runtimeValue(genericConditionalIndexedTreeProjection)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  import "../lib/bool.ep"
  proc genericUnmappedTreeSeed(): RuntimeTree = treeEmpty
  runtimeValue(genericUnmappedTreeSeed)
  proc genericConditionalRawTreeProjection[b: Bool, n, m: Nat,
      tree: SizedTree[if b: n else: m]](ignored: Int):
      SizedTree[if b: n else: m] = tree
  runtimeValue(genericConditionalRawTreeProjection)

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
    if value: false else: true

eponymBlock:
  proc generatedGenericIdentity[A: Univ](value: A): A = value
  runtimeValue(generatedGenericIdentity)

eponymBlock:
  postulate(Int, Univ)
  postulate(Token, Univ)
  proc generatedTokenIdentity(value: Token): Token = value
  runtimeValue(generatedTokenIdentity)
  proc generatedGenericPiWitnessProbe[
      callback: Pi(value: Token, Token)](ignored: Int): Int = ignored
  runtimeValue(generatedGenericPiWitnessProbe)

eponymBlock:
  postulate(Int, Univ)
  postulate(Nat, Univ)
  postulate(Token, Univ)
  postulate(tokenValue, Token)
  proc generatedSigmaWitnessSeed(): Int = 0
  runtimeValue(generatedSigmaWitnessSeed)
  proc generatedGenericNestedSigmaWitnessProbe[
      pair: Sig(first: Token, Sig(count: Nat, Token))](ignored: Int): Int =
    ignored
  runtimeValue(generatedGenericNestedSigmaWitnessProbe)

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  proc generatedDependentSigmaWitnessSeed(): Int = 0
  runtimeValue(generatedDependentSigmaWitnessSeed)
  proc generatedGenericDependentSigmaWitnessProbe[
      pair: Sig(length: Nat, Vec[Int, length])](ignored: Int): Int = ignored
  runtimeValue(generatedGenericDependentSigmaWitnessProbe)
  proc generatedRawDependentSigmaGenericProbe[
      pair: Sig(length: Nat, Vec[Int, length])](ignored: Int): Int = ignored
  runtimeValue(generatedRawDependentSigmaGenericProbe)

eponymBlock:
  import "../lib/nat.ep"
  def(checkedNatIdentity, Nat -> Nat):
    clause([zero], zero)
    clause([suc(n)], suc(n))
  runtimeValue(checkedNatIdentity)

eponymBlock:
  import "../lib/nat.ep"
  def(checkedNatAdd, Nat -> Nat -> Nat):
    clause([zero, m], m)
    clause([suc(n), m], suc(checkedNatAdd(n, m)))
  runtimeValue(checkedNatAdd)

eponymBlock:
  postulate(Channel, Univ)
  runtimeType(Channel, ChannelHandle)
  proc generatedGenericMappedCallback[A: Univ](
      callback: proc(value: A): A {.closure.}, value: A): A =
    callback(value)
  runtimeValue(generatedGenericMappedCallback)

eponymBlock:
  import "../lib/vec.ep"
  postulate(Channel, Univ)
  runtimeType(Channel, ChannelHandle)
  runtimeVector(Vec)
  proc generatedGenericCallbackOverVector[A: Univ](
      callback: proc(value: A): A {.closure.}, values: Vec[A, 2]):
      Vec[A, 2] = vmap(callback, values)
  runtimeValue(generatedGenericCallbackOverVector)

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
  import "../lib/vec.ep"
  postulate(Int, Univ)
  postulate(Channel, Univ)
  runtimeType(Channel, ChannelHandle)
  runtimeVector(Vec)
  proc generatedConditionalGenericVectorValue[b: Bool, n, m: Nat,
      values: Vec[Int, (if b: n else: m)]](ignored: Int):
      Vec[Int, (if b: n else: m)] = values
  proc generatedConditionalGenericSigmaValue[b: Bool, n, m: Nat,
      pair: Sig(length: Nat, Vec[Int, (if b: n else: m)])](ignored: Int):
      Sig(length: Nat, Vec[Int, (if b: n else: m)]) = pair
  proc generatedAndConditionalVectorValue[b, c: Bool, n, m: Nat,
      values: Vec[Int, (if b and c: n else: m)]](ignored: Int):
      Vec[Int, (if b and c: n else: m)] = values
  proc generatedNotConditionalVectorValue[b: Bool, n, m: Nat,
      values: Vec[Int, (if not b: n else: m)]](ignored: Int):
      Vec[Int, (if not b: n else: m)] = values
  proc generatedOrConditionalVectorValue[b, c: Bool, n, m: Nat,
      values: Vec[Int, (if b or c: n else: m)]](ignored: Int):
      Vec[Int, (if b or c: n else: m)] = values
  runtimeValue(generatedConditionalGenericVectorValue)
  runtimeValue(generatedConditionalGenericSigmaValue)
  runtimeValue(generatedAndConditionalVectorValue)
  runtimeValue(generatedNotConditionalVectorValue)
  runtimeValue(generatedOrConditionalVectorValue)
  proc generatedVectorIdentity[A: Univ, n: Nat](
      values: Vec[A, n]): Vec[A, n] = values
  runtimeValue(generatedVectorIdentity)
  proc generatedVectorSucIndex[n: Nat](
      values: Vec[Int, suc(n)]): Nat = n
  proc generatedVectorAddIndex[m, n: Nat](
      values: Vec[Int, add(m, n)]): Int = addInt(0, 0)
  proc generatedNestedVectorIdentity[m, n: Nat](
      values: Vec[Vec[Int, m], n]): Vec[Vec[Int, m], n] = values
  proc generatedGenericVectorValueBinder[n: Nat,
      values: Vec[Int, n]](ignored: Int): Vec[Int, n] = values
  proc generatedGenericSigmaValueBinder[
      pair: Sig(marker: Int, Vec[Int, 2])](ignored: Int):
      Sig(marker: Int, Vec[Int, 2]) = pair
  proc generatedGenericDependentSigmaValueBinder[
      pair: Sig(length: Nat, Vec[Int, length])](ignored: Int):
      Sig(length: Nat, Vec[Int, length]) = pair
  proc generatedValidatedDependentSigmaValueBinder[
      pair: Sig(length: Nat, Vec[Int, length])](ignored: Int):
      Sig(length: Nat, Vec[Int, length]) = pair
  proc generatedGenericPiCallbackBinder[
      callback: Pi(value: Int, Int)](value: Int): Int = callback(value)
  proc generatedGenericPiBinaryCallbackBinder[
      callback: Pi(left: Int, right: Int, Int)](left, right: Int): Int =
    callback(left, right)
  proc generatedDependentPiCallbackBinder[
      callback: Pi(length: Nat, values: Vec[Int, length],
                   Vec[Int, length])](length: Nat,
                                      values: Vec[Int, length]):
      Vec[Int, length] = callback(length, values)
  proc generatedComputedDependentPiCallbackBinder[
      callback: Pi(left: Nat, right: Nat,
        values: Vec[Int, add(left, right)], Vec[Int, add(left, right)])](
        left, right: Nat, values: Vec[Int, add(left, right)]):
      Vec[Int, add(left, right)] = callback(left, right, values)
  proc generatedApplyNestedPiCallback[
      callback: Pi(inner: Pi(value: Int, Int), Int)](
        inner: Pi(value: Int, Int)): Int = callback(inner)
  proc generatedReturnNestedPiCallback[
      callback: Pi(value: Int, Pi(seed: Int, Int))](value: Int):
      Pi(seed: Int, Int) = callback(value)
  runtimeValue(generatedNestedVectorIdentity)
  runtimeValue(generatedGenericVectorValueBinder)
  runtimeValue(generatedGenericSigmaValueBinder)
  runtimePairTrusted(generatedGenericDependentSigmaValueBinder)
  runtimeValue(generatedGenericDependentSigmaValueBinder)
  runtimeValue(generatedValidatedDependentSigmaValueBinder)
  runtimeValue(generatedGenericPiCallbackBinder)
  runtimeValue(generatedGenericPiBinaryCallbackBinder)
  runtimeValue(generatedDependentPiCallbackBinder)
  runtimeValue(generatedComputedDependentPiCallbackBinder)
  runtimeValue(generatedApplyNestedPiCallback)
  runtimeValue(generatedReturnNestedPiCallback)
  proc generatedDependentPairVecIdentity(
      value: Sig(length: Nat, Sig(marker: Int, Vec[Int, length]))):
      Sig(length: Nat, Sig(marker: Int, Vec[Int, length])) = value
  runtimePairTrusted(generatedDependentPairVecIdentity)
  proc generatedGenericDependentPairValueBinder[
      pair: Sig(length: Nat, Vec[Int, length])](ignored: Int):
      Sig(length: Nat, Vec[Int, length]) = pair
  runtimePairTrusted(generatedGenericDependentPairValueBinder)
  runtimeValue(generatedGenericDependentPairValueBinder)
  proc generatedValidatedDependentPairValueBinder[
      pair: Sig(length: Nat, Vec[Vec[Int, length], suc(length)])](ignored: Int):
      Sig(length: Nat, Vec[Vec[Int, length], suc(length)]) = pair
  runtimeValue(generatedValidatedDependentPairValueBinder)
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
  proc generatedGenericSizedVecValueBinder[value: SizedVec](
      ignored: Int): SizedVec = value
  runtimeValue(generatedGenericSizedVecValueBinder)
  record(CheckedSizedVec):
    field(length, Nat)
    field(values, Vec[Vec[Int, length], suc(length)])
  runtimeType(CheckedSizedVec, RuntimeCheckedSizedVec)
  proc generatedValidatedDependentRecordValue[value: CheckedSizedVec](
      ignored: Int): CheckedSizedVec = value
  runtimeValue(generatedValidatedDependentRecordValue)

eponymBlock:
  postulate(Channel, Univ)
  runtimeType(Channel, ChannelHandle)
  proc generatedMappedGenericPiCallbackBinder[
      callback: Pi(value: Channel, Channel)](value: Channel): Channel =
    callback(value)
  runtimeValue(generatedMappedGenericPiCallbackBinder)

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
  proc generatedEmptyIntList(): List[Int] = (nil)
  runtimeValue(generatedEmptyIntList)
  proc generatedBoundEmptyIntList(): List[Int] =
    let values: List[Int] = nil
    values
  runtimeValue(generatedBoundEmptyIntList)
  proc generatedListIdentity[A: Univ](values: List[A]): List[A] = values
  runtimeValue(generatedListIdentity)
  proc generatedGenericListValueBinder[values: List[Int]](
      ignored: Int): List[Int] = values
  runtimeValue(generatedGenericListValueBinder)

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
  proc generatedGenericOptionValueBinder[value: Option[Int]](
      ignored: Int): Option[Int] = value
  runtimeValue(generatedGenericOptionValueBinder)

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
  typedResult == index and valueToInt(runtime.value) == index and
    valueToInt(rawRuntime.value) == index and
    generatedGenericIntValueDynamic(index, ignored) == index

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

proc encodeRuntimeSizedTree(values: seq[int], globals: Globals): Value =
  let encodedTree = encodeRuntimeTree(values, globals)
  runtimeVariantToValue(RuntimeVariant(constructor: "sizedTree",
    arguments: @[natToValue(values.len, globals), encodedTree]), globals,
    "SizedTree", ["sizedTree"])

proc decodeRuntimeSizedTree(value: Value, globals: Globals): seq[int] =
  let variant = valueToRuntimeVariant(value, globals, "SizedTree",
    ["sizedTree"])
  if variant.arguments.len != 2:
    raise newException(ValueError, "SizedTree has an invalid runtime spine")
  let length = valueToNat(variant.arguments[0], globals)
  result = decodeRuntimeTree(variant.arguments[1], globals)
  if result.len != length:
    raise newException(ValueError, "SizedTree index does not match payload")

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)
  data(Tree, Univ):
    proc treeEmpty(): Tree
    proc treeNode(value: Int, tail: Tree): Tree
  runtimeCodec(Tree, seq[int], encodeRuntimeTree, decodeRuntimeTree)
  runtimeVector(Vec)
  postulate(treeReverse, Tree -> Tree)
  bindPostulate(treeReverse, reverseRuntimeTree, Tree)
  proc generatedTreeIdentity(value: Tree): Tree = value
  runtimeValue(generatedTreeIdentity)
  proc generatedBoundTreeReverse(value: Tree): Tree = treeReverse(value)
  proc generatedGenericTreeVectorMap[A: Univ, n: Nat](
      callback: proc(value: A): A {.closure.}, values: Vec[A, n]): Vec[A, n] =
    vmap(callback, values)
  runtimeValue(generatedGenericTreeVectorMap)
  proc generatedGenericTreeValueBinder[tree: Tree](ignored: Int): Tree = tree
  runtimeValue(generatedGenericTreeValueBinder)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  runtimeCodec(SizedTree, seq[int], encodeRuntimeSizedTree,
    decodeRuntimeSizedTree)
  proc generatedGenericSizedTreeBinder[length: Nat,
      tree: SizedTree[length]](ignored: Int): SizedTree[length] = tree
  runtimeValue(generatedGenericSizedTreeBinder)
  proc generatedDependentCustomPiCallbackBinder[
      callback: Pi(length: Nat, tree: SizedTree[length],
                   SizedTree[length])](length: Nat,
                                        tree: SizedTree[length]):
      SizedTree[length] = callback(length, tree)
  runtimeValue(generatedDependentCustomPiCallbackBinder)
  proc generatedValidatedCustomDependentSigmaBinder[
      pair: Sig(length: Nat, SizedTree[length])](ignored: Int):
      Sig(length: Nat, SizedTree[length]) = pair
  runtimeValue(generatedValidatedCustomDependentSigmaBinder)

eponymBlock:
  postulate(Int, Univ)
  proc generatedApplyNimCallback(
      callback: proc(value: Int): Int {.closure.}, value: Int): Int =
    callback(value)
  proc generatedApplyNimcallCallback(
      callback: proc(value: Int): Int, value: Int): Int =
    callback(value)
  proc generatedApplyCdeclCallback(
      callback: proc(value: Int): Int {.cdecl.}, value: Int): Int =
    callback(value)
  proc generatedAdder(seed: Int): proc(value: Int): Int {.closure.} =
    lam(value, Int, addInt(seed, value))
  proc generatedApplyTwoArgumentCallback(
      callback: proc(left, right: Int): Int {.closure.},
      left, right: Int): Int =
    let reordered = callback
    reordered(right = right, left = left)
  runtimeValue(generatedApplyTwoArgumentCallback)
  proc generatedTwoArgumentAdder(seed: Int):
      proc(left, right: Int): Int {.closure.} =
    lam(left, Int, lam(right, Int, addInt(seed, addInt(left, right))))

eponymBlock:
  postulate(Int, Univ)
  postulate(Token, Univ)
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
      length: Nat): Vec[Int, length] = callback(length)
  runtimeValue(generatedApplyIndexedCallback)
  proc generatedApplyDependentVectorCallback(
      callback: proc(length: Nat, values: Vec[Int, length]): Nat {.closure.},
      length: Nat, values: Vec[Int, length]): Nat = callback(length, values)
  proc generatedDependentVectorCallback():
      proc(length: Nat, values: Vec[Int, length]): Nat {.closure.} =
    lam(length, Nat, lam(values, Vec[Int, length], length))
  runtimeValue(generatedApplyDependentVectorCallback)
  runtimeValue(generatedDependentVectorCallback)

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
  doAssert compiles(generatedApplyNimCallback(proc(value: int): int = value, 1))
  doAssert compiles(generatedApplyNimcallCallback(hostNimcallIncrement, 1))
  doAssert compiles(generatedApplyCdeclCallback(hostCdeclStepNim, 1))
  doAssert not compiles(generatedApplyNimCallback(
    proc(value: string): string = value, 1))
  doAssert compiles(generatedAdder(3)(4))
  doAssert compiles(generatedApplyTwoArgumentCallback(
    proc(left, right: int): int = left + right, 1, 2))
  doAssert compiles(generatedGenericPiCallbackBinderDynamic(
    proc(value: int): int {.closure.} = value, 1))
  doAssert not compiles(generatedGenericPiCallbackBinderDynamic(
    proc(value: string): string {.closure.} = value, 1))
  doAssert compiles(generatedGenericPiBinaryCallbackBinderDynamic(
    proc(left, right: int): int {.closure.} = left + right, 1, 2))
  doAssert not compiles(generatedGenericPiBinaryCallbackBinderDynamic(
    proc(left: string, right: int): int {.closure.} = right, 1, 2))
  doAssert compiles(generatedDependentPiCallbackBinderDynamic(
    proc(length: int, values: seq[int]): seq[int] {.closure.} = values,
    3, @[1, 2, 3]))
  doAssert not compiles(generatedDependentPiCallbackBinderDynamic(
    proc(length: string, values: seq[int]): seq[int] {.closure.} = values,
    3, @[1, 2, 3]))
  doAssert compiles(generatedComputedDependentPiCallbackBinderDynamic(
    proc(left, right: int, values: seq[int]): seq[int] {.closure.} = values,
    2, 3, @[1, 2, 3, 4, 5]))
  doAssert not compiles(generatedComputedDependentPiCallbackBinderDynamic(
    proc(left: string, right: int, values: seq[int]): seq[int] {.closure.} =
      values,
    2, 3, @[1, 2, 3, 4, 5]))
  doAssert compiles(generatedApplyNestedPiCallbackDynamic(
    proc(inner: proc(value: int): int {.closure.}): int {.closure.} =
      inner(3),
    proc(value: int): int {.closure.} = value + 1))
  doAssert not compiles(generatedApplyNestedPiCallbackDynamic(
    proc(inner: proc(value: string): string {.closure.}): string {.closure.} =
      inner("wrong"),
    proc(value: int): int {.closure.} = value + 1))
  doAssert compiles(generatedGenericPiCallbackBinderDynamic(hostStepNim, 2))
  doAssert compiles(generatedGenericPiCallbackBinderDynamic(
    hostCdeclStepNim, 2))
  doAssert not compiles(generatedGenericPiCallbackBinderDynamic(
    proc(value: string): string = value, 2))
  doAssert compiles(generatedReturnNestedPiCallbackDynamic(
    proc(value, seed: int): int {.closure.} = value + seed,
    3))
  doAssert not compiles(generatedReturnNestedPiCallbackDynamic(
    proc(value: string, seed: int): string {.closure.} = value & $seed,
    3))
  doAssert compiles(generatedDependentCustomPiCallbackBinderDynamic(
    proc(length: int, tree: seq[int]): seq[int] {.closure.} = tree,
    3, @[1, 2, 3]))
  doAssert not compiles(generatedDependentCustomPiCallbackBinderDynamic(
    proc(length: string, tree: seq[int]): seq[int] {.closure.} = tree,
    3, @[1, 2, 3]))
  doAssert compiles(generatedMappedGenericPiCallbackBinderDynamic(
    proc(value: ChannelHandle): ChannelHandle {.closure.} = value,
    ChannelHandle(id: 1)))
  doAssert not compiles(generatedMappedGenericPiCallbackBinderDynamic(
    proc(value: int): int {.closure.} = value, ChannelHandle(id: 1)))
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
  proc generatedPointRebuild(value: Point): Point =
    mkPoint(value.x, value.channel)
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
    Channel(0) -> Sig(index: Nat, Channel(index)))
  bindPostulatePairTrusted(splitIndexedChannel, hostIndexedChannelParts,
    Channel, Nat, Channel)
  runtimePairTrusted(generatedSplitIndexedChannel)
  postulate(repeatIndexedChannel,
    Pi(index: Nat, channel: Channel(index),
       Sig(first: Channel(index), Channel(index))))
  bindPostulatePair(repeatIndexedChannel, hostRepeatIndexedChannel,
    Nat, Channel, Channel, Channel)
  proc generatedIndexedChannelIndex(channel: Channel(0)): Nat =
    fst(splitIndexedChannel(channel))
  proc generatedSplitIndexedChannel(channel: Channel(0)):
      Sig(index: Nat, Channel(index)) =
    splitIndexedChannel(channel)
  proc generatedRepeatIndexedChannel(index: Nat, channel: Channel(index)):
      Sig(first: Channel(index), Channel(index)) =
    repeatIndexedChannel(index, channel)

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
      Sig(marker: Int, Vec[Int, index]) = makeVectorForIndex(index, seed)
  runtimePairTrusted(generatedVectorForIndex)

eponymBlock:
  import "fixtures/runtime_pair_postulate.ep"
  runtimeVector(Vec)
  bindPostulatePairTrusted(makeVectorForIndex, hostMakeVectorForIndex,
    Nat, Int, Int, Vec)
  proc generatedImportedVectorForIndex(index: Nat, seed: Int):
      Sig(marker: Int, Vec[Int, index]) = makeVectorForIndex(index, seed)
  runtimePairTrusted(generatedImportedVectorForIndex)

eponymBlock:
  import "fixtures/runtime_imported_named.ep"
  proc generatedImportedNamed(left, right: Int): Int =
    importedPick(right = right, left = left)

eponymBlock:
  postulate(BaseHandle, Univ)
  postulate(DerivedHandle, Univ)
  runtimeType(BaseHandle, BaseRuntimeHandle)
  runtimeType(DerivedHandle, DerivedRuntimeHandle)
  proc mappedGenericIdentity[A: Univ](value: A): A = value
  runtimeValue(mappedGenericIdentity)

static:
  doAssert compiles(generatedCheckedRole(35))
  doAssert compiles(generatedDefault())
  doAssert compiles(generatedDefault(7))
  doAssert compiles(generatedDefault(value = 7))
  doAssert compiles(generatedDefaultRuntimeValue())
  doAssert compiles(generatedDefaultRuntimeValue(value = 7))
  doAssert compiles(generatedAdd(20, 22))
  doAssert compiles(generatedNamedAdd(20, 22))
  doAssert compiles(generatedNamedAlias(20, 22))
  doAssert compiles(generatedDefaultGap(10))
  doAssert compiles(generatedTrailingDefaultCall(10))
  doAssert compiles(generatedImportedNamed(20, 22))
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
  doAssert compiles(generatedPointRebuild(RuntimePoint(x: 17,
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
  let boundRuntime = runtimeResultRuntimeValue()
  doAssert boundRuntime.value.whnfKind == wInt
  doAssert boundRuntime.value.whnfIntVal == 42
  let baseDir = currentSourcePath().parentDir.parentDir
  var r = initRng(424242'u64)

  let variantSrc = readFile(baseDir / "tests/fixtures/runtime_variant.ep")
  let variantGlobals = getGlobalsDir(baseDir, variantSrc)
  let runtimeNatType = runtimeGlobalValue(variantGlobals, "Nat")
  let runtimeIntType = runtimeGlobalValue(variantGlobals, "Int")
  let runtimeTreeType = runtimeGlobalValue(variantGlobals, "RuntimeTree")
  let runtimePairType = runtimeSigmaType(runtimeIntType, runtimeNatType)
  let sigmaTypeCases = forAll(
    "runtime Sigma type witnesses validate pair payloads", r, 200,
    proc(r: var Rng): tuple[integer, natural: int] =
      (r.genInt(-1000, 1000), r.genInt(0, 1000)),
    proc(input: tuple[integer, natural: int]): bool =
      let pair = pairValue(intToValue(input.integer),
        natToValue(input.natural, variantGlobals))
      validateRuntimeValueAgainstType(pair, runtimePairType, variantGlobals)
      true)
  if not sigmaTypeCases:
    quit(1)
  var wrongSigmaFieldRejected = false
  try:
    validateRuntimeValueAgainstType(
      pairValue(intToValue(1), intToValue(2)), runtimePairType,
      variantGlobals)
  except ValueError:
    wrongSigmaFieldRejected = true
  doAssert wrongSigmaFieldRejected

  let runtimeSizedTreeType = runtimeDependentSigmaType(runtimeNatType,
    variantGlobals, proc(length: Value): Value =
      callRuntimeValue(runtimeGlobalValue(variantGlobals, "SizedTree"),
        [length]))
  let dependentSigmaCases = forAll(
    "runtime dependent Sigma witnesses validate selected indexed fields",
    r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let tree = runtimeVariantToValue(RuntimeVariant(
        constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
        ["treeEmpty", "treeNode"])
      let sizedTree = runtimeVariantToValue(RuntimeVariant(
        constructor: "sizedTree",
        arguments: @[natToValue(length, variantGlobals), tree]),
        variantGlobals, "SizedTree", ["sizedTree"])
      let value = pairValue(natToValue(length, variantGlobals), sizedTree)
      validateRuntimeValueAgainstType(value, runtimeSizedTreeType,
        variantGlobals)
      true)
  if not dependentSigmaCases:
    quit(1)
  var wrongDependentSigmaFieldRejected = false
  try:
    let tree = runtimeVariantToValue(RuntimeVariant(
      constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
      ["treeEmpty", "treeNode"])
    let sizedTree = runtimeVariantToValue(RuntimeVariant(
      constructor: "sizedTree",
      arguments: @[natToValue(4, variantGlobals), tree]),
      variantGlobals, "SizedTree", ["sizedTree"])
    validateRuntimeValueAgainstType(
      pairValue(natToValue(3, variantGlobals), sizedTree),
      runtimeSizedTreeType, variantGlobals)
  except ValueError:
    wrongDependentSigmaFieldRejected = true
  doAssert wrongDependentSigmaFieldRejected

  let runtimeIdentity = eval(variantGlobals["treeIdentity"].tm, @[])
  let runtimeArrow = runtimeArrowType(runtimeTreeType, runtimeTreeType)
  validateRuntimeValueType(runtimeIdentity, runtimeArrow, variantGlobals)
  let inferredFunctionType = runtimeValueTypeOf(runtimeIdentity,
    variantGlobals)
  validateRuntimeValueType(runtimeIdentity, inferredFunctionType,
    variantGlobals)
  let runtimeTypeInferenceCases = forAll(
    "runtime type inference preserves primitive values and checked functions",
    r, 200,
    proc(r: var Rng): int = r.genInt(0, 1000),
    proc(n: int): bool =
      let natType = runtimeValueTypeOf(natToValue(n, variantGlobals),
        variantGlobals)
      let intType = runtimeValueTypeOf(intToValue(n), variantGlobals)
      natType.whnfKind == wRef and
        natType.whnfRefId == runtimeNatType.whnfRefId and
        intType.whnfKind == wRef and
        intType.whnfRefId == runtimeIntType.whnfRefId)
  if not runtimeTypeInferenceCases:
    quit(1)
  let witnessSource = """
postulate Int : Type 0
postulate Token : Type 0
proc generatedTokenIdentity (value : Token) : Token = value
"""
  let tokenIdentityValue = callValueFuncDir(baseDir, witnessSource,
    "generatedTokenIdentity", [])
  let genericPiExpressionCases = forAll(
    "generated runtime type expressions reify named Pi binders", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let returned = generatedGenericPiWitnessProbeRuntimeValueDynamic(
        tokenIdentityValue, value)
      valueToInt(returned.value) == value)
  if not genericPiExpressionCases:
    quit(1)
  var wrongGenericPiExpressionRejected = false
  try:
    discard generatedGenericPiWitnessProbeRuntimeValueDynamic(
      intToValue(1), 0)
  except ValueError:
    wrongGenericPiExpressionRejected = true
  doAssert wrongGenericPiExpressionRejected
  let sigmaWitnessGlobals = generatedSigmaWitnessSeedRuntimeValue().globals
  let sigmaWitnessToken = runtimeGlobalValue(sigmaWitnessGlobals, "tokenValue")
  let genericNestedSigmaExpressionCases = forAll(
    "generated runtime type expressions reify nested Sigma binders", r, 200,
    proc(r: var Rng): tuple[count, ignored: int] =
      (r.genInt(0, 100), r.genInt(-1000, 1000)),
    proc(input: tuple[count, ignored: int]): bool =
      let pair = pairValue(sigmaWitnessToken,
        pairValue(natToValue(input.count, sigmaWitnessGlobals),
          sigmaWitnessToken))
      let returned = generatedGenericNestedSigmaWitnessProbeRuntimeValueDynamic(
        pair, input.ignored)
      valueToInt(returned.value) == input.ignored)
  if not genericNestedSigmaExpressionCases:
    quit(1)
  var wrongNestedSigmaValueRejected = false
  try:
    let malformed = pairValue(sigmaWitnessToken,
      pairValue(intToValue(1), sigmaWitnessToken))
    discard generatedGenericNestedSigmaWitnessProbeRuntimeValueDynamic(
      malformed, 0)
  except ValueError:
    wrongNestedSigmaValueRejected = true
  doAssert wrongNestedSigmaValueRejected
  let dependentSigmaWitnessGlobals =
    generatedDependentSigmaWitnessSeedRuntimeValue().globals
  let genericDependentSigmaExpressionCases = forAll(
    "generated type expressions validate dependent Sigma Vec fields", r,
    200,
    proc(r: var Rng): tuple[length, ignored: int] =
      (r.genInt(0, 20), r.genInt(-1000, 1000)),
    proc(input: tuple[length, ignored: int]): bool =
      var elements = newSeq[int](input.length)
      for i in 0 ..< input.length:
        elements[i] = input.ignored + i
      let pair = (input.length, elements)
      let returned = generatedGenericDependentSigmaWitnessProbeRuntimeValueDynamic(
        pair, input.ignored)
      valueToInt(returned.value) == input.ignored)
  if not genericDependentSigmaExpressionCases:
    quit(1)
  var wrongDependentSigmaWitnessRejected = false
  try:
    discard generatedGenericDependentSigmaWitnessProbeRuntimeValueDynamic(
      (3, @[3, 4]), 0)
  except ValueError:
    wrongDependentSigmaWitnessRejected = true
  doAssert wrongDependentSigmaWitnessRejected
  let rawDependentSigmaCases = forAll(
    "raw generic dependent Sigma values validate their Vec index", r, 200,
    proc(r: var Rng): tuple[length, ignored: int] =
      (r.genInt(0, 20), r.genInt(-1000, 1000)),
    proc(input: tuple[length, ignored: int]): bool =
      var elements = newSeq[int](input.length)
      for i in 0 ..< input.length:
        elements[i] = input.ignored + i
      let pair = (input.length, elements)
      let returned = generatedRawDependentSigmaGenericProbeRuntimeValueDynamic(
        pair, input.ignored)
      valueToInt(returned.value) == input.ignored)
  if not rawDependentSigmaCases:
    quit(1)
  var wrongRawDependentSigmaRejected = false
  try:
    discard generatedRawDependentSigmaGenericProbeRuntimeValueDynamic(
      (3, @[3, 4]), 0)
  except ValueError:
    wrongRawDependentSigmaRejected = true
  doAssert wrongRawDependentSigmaRejected
  var malformedNatTypeInferenceRejected = false
  try:
    let malformedNat = callRuntimeValue(
      eval(variantGlobals["suc"].tm, @[]), [intToValue(1)])
    discard runtimeValueTypeOf(malformedNat, variantGlobals)
  except ValueError:
    malformedNatTypeInferenceRejected = true
  doAssert malformedNatTypeInferenceRejected
  let runtimeDependentArrow = runtimeDependentArrowType(runtimeTreeType,
    variantGlobals, proc(_: Value): Value = runtimeTreeType)
  validateRuntimeValueType(runtimeIdentity, runtimeDependentArrow,
    variantGlobals)
  var wrongArrowDomainRejected = false
  try:
    validateRuntimeValueType(runtimeIdentity,
      runtimeArrowType(runtimeNatType, runtimeTreeType), variantGlobals)
  except ValueError:
    wrongArrowDomainRejected = true
  doAssert wrongArrowDomainRejected

  const runtimeTreeConstructors = ["treeEmpty", "treeNode"]
  let rawVariantCases = forAll(
    "generic structural codecs preserve payload-bearing data constructors",
    r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      var values: seq[int] = @[]
      for i in 0 ..< length: values.add(i)
      let tree = encodeRuntimeTree(values, variantGlobals)
      let typedRoundTrip = runtimeVariantToValue(
        treeIdentity(valueToRuntimeVariant(tree, variantGlobals,
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
  let dependentVariantCases = forAll(
    "runtime variants validate dependent constructor payload types", r, 200,
    proc(r: var Rng): tuple[length: int, values: seq[int]] =
      let length = r.genInt(0, 20)
      var values: seq[int] = @[]
      for _ in 0 ..< length: values.add(r.genInt(-1000, 1000))
      (length, values),
    proc(input: tuple[length: int, values: seq[int]]): bool =
      let vector = seqToVecValue[int](input.values, input.length,
        variantGlobals, "Vec",
        proc(item: int, _: Globals): Value = intToValue(item),
        runtimeGlobalValue(variantGlobals, "Int"))
      let wrapped = runtimeVariantToValue(RuntimeVariant(
        constructor: "sizedVector",
        arguments: @[natToValue(input.length, variantGlobals), vector]),
        variantGlobals, "SizedVector", ["sizedVector"])
      let decoded = valueToRuntimeVariant(wrapped, variantGlobals,
        "SizedVector", ["sizedVector"])
      valueToNat(decoded.arguments[0], variantGlobals) == input.length and
        vecValueToSeq[int](decoded.arguments[1], input.length,
          variantGlobals, "Vec",
          proc(item: Value, _: Globals): int = valueToInt(item)) ==
            input.values)
  if not dependentVariantCases:
    quit(1)
  var wrongRuntimeVariantPayloadRejected = false
  try:
    discard runtimeVariantToValue(RuntimeVariant(
      constructor: "treeNode",
      arguments: @[intToValue(1), intToValue(2)]), variantGlobals,
      "RuntimeTree", ["treeEmpty", "treeNode"])
  except ValueError as error:
    wrongRuntimeVariantPayloadRejected = "argument 1 has the wrong type" in
      error.msg
  doAssert wrongRuntimeVariantPayloadRejected
  var wrongDependentRuntimeVariantPayloadRejected = false
  try:
    let wrongLength = seqToVecValue[int](@[10, 20], 2, variantGlobals,
      "Vec", proc(item: int, _: Globals): Value = intToValue(item),
      runtimeGlobalValue(variantGlobals, "Int"))
    discard runtimeVariantToValue(RuntimeVariant(
      constructor: "sizedVector",
      arguments: @[natToValue(3, variantGlobals), wrongLength]),
      variantGlobals, "SizedVector", ["sizedVector"])
  except ValueError:
    wrongDependentRuntimeVariantPayloadRejected = true
  doAssert wrongDependentRuntimeVariantPayloadRejected
  let malformedTree = callRuntimeValue(
    eval(variantGlobals["treeNode"].tm, @[]),
    @[intToValue(1), intToValue(2)])
  var malformedTreeTypeRejected = false
  try:
    validateRuntimeValueAgainstType(malformedTree,
      runtimeGlobalValue(variantGlobals, "RuntimeTree"), variantGlobals)
  except ValueError:
    malformedTreeTypeRejected = true
  doAssert malformedTreeTypeRejected
  var malformedGenericVariantRejected = false
  try:
    let malformedSizedTree = callRuntimeValue(
      eval(variantGlobals["sizedTree"].tm, @[]),
      @[natToValue(3, variantGlobals), intToValue(4)])
    let rawVariant = valueToRuntimeVariant(malformedSizedTree,
      variantGlobals, "SizedTree", ["sizedTree"])
    discard genericIndexedTreeProjectionRuntimeValueDynamic(3, rawVariant, 0)
  except ValueError:
    malformedGenericVariantRejected = true
  doAssert malformedGenericVariantRejected
  let malformedConstructorCases = forAll(
    "raw constructor checks reject primitive values in unrelated fields", r,
    200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let malformed = callRuntimeValue(
        eval(variantGlobals["treeNode"].tm, @[]),
        @[intToValue(1), intToValue(value)])
      try:
        validateRuntimeValueAgainstType(malformed,
          runtimeGlobalValue(variantGlobals, "RuntimeTree"), variantGlobals)
        false
      except ValueError:
        true,
    shrinkInt)
  if not malformedConstructorCases:
    quit(1)
  let appliedGenericTypeCases = forAll(
    "unmapped applied generic domains check their runtime indices", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let tree = runtimeVariantToValue(RuntimeVariant(
        constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
        runtimeTreeConstructors)
      let indexed = runtimeVariantToValue(RuntimeVariant(
        constructor: "sizedTree",
        arguments: @[natToValue(length, variantGlobals), tree]),
        variantGlobals, "SizedTree", ["sizedTree"])
      let projected = genericIndexedTreeProjectionRuntimeValueDynamic(
        length, valueToRuntimeVariant(indexed, variantGlobals,
          "SizedTree", ["sizedTree"]), 0)
      let decoded = valueToRuntimeVariant(projected.value, variantGlobals,
        "SizedTree", ["sizedTree"])
      decoded.constructor == "sizedTree" and
        valueToNat(decoded.arguments[0], variantGlobals) == length and
        decoded.arguments[1].whnfRefId == tree.whnfRefId,
    shrinkInt)
  if not appliedGenericTypeCases:
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
      valueToRuntimeVariant(wrongIndexedTree, variantGlobals,
        "SizedTree", ["sizedTree"]), 0)
  except ValueError:
    appliedGenericIndexRejected = true
  doAssert appliedGenericIndexRejected
  let conditionalAppliedGenericCases = forAll(
    "conditional applied generic domains validate RuntimeVariant values", r,
    200,
    proc(r: var Rng): tuple[condition: bool, yesLength, noLength: int] =
      (r.genBool(), r.genInt(0, 20), r.genInt(0, 20)),
    proc(input: tuple[condition: bool, yesLength, noLength: int]): bool =
      let expectedLength = if input.condition:
        input.yesLength else: input.noLength
      let tree = runtimeVariantToValue(RuntimeVariant(
        constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
        runtimeTreeConstructors)
      let indexed = runtimeVariantToValue(RuntimeVariant(
        constructor: "sizedTree",
        arguments: @[natToValue(expectedLength, variantGlobals), tree]),
        variantGlobals, "SizedTree", ["sizedTree"])
      let mapped = valueToRuntimeVariant(indexed, variantGlobals,
        "SizedTree", ["sizedTree"])
      let typed = genericConditionalIndexedTreeProjectionDynamic(
        input.condition, input.yesLength, input.noLength, mapped, 0)
      let runtime = genericConditionalIndexedTreeProjectionRuntimeValueDynamic(
        input.condition, input.yesLength, input.noLength, mapped, 0)
      let rawSeed = genericUnmappedTreeSeedRuntimeValue()
      let rawIndexed = callRuntimeValue(
        runtimeGlobalValue(rawSeed.globals, "sizedTree"),
        [natToValue(expectedLength, rawSeed.globals), rawSeed.value])
      let raw = genericConditionalRawTreeProjectionRuntimeValueDynamic(
        input.condition, input.yesLength, input.noLength, rawIndexed, 0)
      let runtimeValue = valueToRuntimeVariant(runtime.value, runtime.globals,
        "SizedTree", ["sizedTree"])
      let rawVariant = valueToRuntimeVariant(raw.value, raw.globals,
        "SizedTree", ["sizedTree"])
      typed.constructor == "sizedTree" and
        valueToNat(typed.arguments[0], variantGlobals) == expectedLength and
        valueToNat(runtimeValue.arguments[0], runtime.globals) ==
          expectedLength and
        valueToNat(rawVariant.arguments[0], raw.globals) == expectedLength,
    proc(input: tuple[condition: bool, yesLength, noLength: int]):
        seq[tuple[condition: bool, yesLength, noLength: int]] = @[])
  if not conditionalAppliedGenericCases:
    quit(1)
  let tree = runtimeVariantToValue(RuntimeVariant(
    constructor: "treeEmpty"), variantGlobals, "RuntimeTree",
    runtimeTreeConstructors)
  let wrongLength = runtimeVariantToValue(RuntimeVariant(
    constructor: "sizedTree", arguments: @[natToValue(9, variantGlobals),
      tree]), variantGlobals, "SizedTree", ["sizedTree"])
  let wrongConditionalTree = valueToRuntimeVariant(wrongLength,
    variantGlobals, "SizedTree", ["sizedTree"])
  var typedConditionalAppliedMismatchRejected = false
  try:
    discard genericConditionalIndexedTreeProjectionDynamic(
      true, 3, 4, wrongConditionalTree, 0)
  except ValueError:
    typedConditionalAppliedMismatchRejected = true
  doAssert typedConditionalAppliedMismatchRejected
  var runtimeConditionalAppliedMismatchRejected = false
  try:
    discard genericConditionalIndexedTreeProjectionRuntimeValueDynamic(
      true, 3, 4, wrongConditionalTree, 0)
  except ValueError:
    runtimeConditionalAppliedMismatchRejected = true
  doAssert runtimeConditionalAppliedMismatchRejected
  let rawSeed = genericUnmappedTreeSeedRuntimeValue()
  let rawWrongLength = callRuntimeValue(
    runtimeGlobalValue(rawSeed.globals, "sizedTree"),
    [natToValue(9, rawSeed.globals), rawSeed.value])
  var rawConditionalAppliedMismatchRejected = false
  try:
    discard genericConditionalRawTreeProjectionRuntimeValueDynamic(
      true, 3, 4, rawWrongLength, 0)
  except ValueError:
    rawConditionalAppliedMismatchRejected = true
  doAssert rawConditionalAppliedMismatchRejected
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

  let importedGenericIdentityCases = forAll(
    "typed wrappers reconstruct imported polymorphic identities", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      let typedRuntime = importedGenericIdentityRuntimeValue[int](value)
      let rawRuntime = importedGenericIdentityRuntimeValueRaw(
        [vType(0), intToValue(value)])
      let channel = ChannelHandle(id: value, label: "imported/" & $value)
      let typedChannelRuntime =
        importedGenericIdentityRuntimeValue[ChannelHandle](channel)
      importedGenericIdentity[int](value) == value and
        valueToHost[int](typedRuntime.value) == value and
        valueToInt(rawRuntime.value) == value and
        importedGenericIdentity[ChannelHandle](channel) == channel and
        valueToHost[ChannelHandle](typedChannelRuntime.value) == channel,
    shrinkInt)
  if not importedGenericIdentityCases:
    quit(1)

  let importedGenericCallbackCases = forAll(
    "imported polymorphic list map bridges a Nim closure", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 12), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var channels = newSeq[ChannelHandle](input.length)
      var expected = newSeq[int](input.length)
      for i in 0 ..< input.length:
        channels[i] = ChannelHandle(id: input.seed + i,
          label: "map/" & $(input.seed + i))
        expected[i] = input.seed + i
      let mapper: proc(value: ChannelHandle): int {.closure.} =
        proc(value: ChannelHandle): int = value.id
      let direct = importedListMap[ChannelHandle, int](mapper, channels)
      let runtime = importedListMapRuntimeValue[ChannelHandle, int](mapper,
        channels)
      direct == expected and
        listValueToSeq[int](runtime.value, runtime.globals, "List",
          proc(item: Value, _: Globals): int = valueToHost[int](item)) == direct)
  if not importedGenericCallbackCases:
    quit(1)

  let importedIndexedCallbackCases = forAll(
    "imported callbacks enforce an outer dependent Vec index", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 12), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
      let mapper: proc(values: seq[int]): seq[int] {.closure.} =
        proc(values: seq[int]): seq[int] =
          var mapped = newSeq[int](values.len)
          for i, value in values:
            mapped[i] = value * 2
          mapped
      let direct = importedApplyVectorCallback(input.length, mapper, values)
      let runtime = importedApplyVectorCallbackRuntimeValue(input.length,
        mapper, values)
      var expected = newSeq[int](values.len)
      for i, value in values:
        expected[i] = value * 2
      direct == expected and
        vecValueToSeq[int](runtime.value, input.length, runtime.globals,
          "Vec", proc(item: Value, _: Globals): int = valueToInt(item)) ==
            expected)
  if not importedIndexedCallbackCases:
    quit(1)
  let identityVector: proc(values: seq[int]): seq[int] {.closure.} =
    proc(values: seq[int]): seq[int] = values
  var importedIndexedCallbackInputMismatchRejected = false
  try:
    discard importedApplyVectorCallback(3, identityVector, @[1, 2])
  except ValueError as error:
    importedIndexedCallbackInputMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert importedIndexedCallbackInputMismatchRejected
  let wrongLengthVectorResult: proc(values: seq[int]): seq[int] {.closure.} =
    proc(values: seq[int]): seq[int] = values & 0
  var importedIndexedCallbackResultMismatchRejected = false
  try:
    discard importedApplyVectorCallback(3, wrongLengthVectorResult,
      @[1, 2, 3])
  except ValueError as error:
    importedIndexedCallbackResultMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert importedIndexedCallbackResultMismatchRejected

  let importedCallbackLocalIndexCases = forAll(
    "imported callback binders carry Vec indices through both codecs", r,
    200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 12), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
      let direct = importedDependentVectorCallback(
        identityDependentVectorCallback, input.length, values)
      let runtime = importedDependentVectorCallbackRuntimeValue(
        identityDependentVectorCallback, input.length, values)
      direct == values and
        vecValueToSeq[int](runtime.value, input.length, runtime.globals,
          "Vec", proc(item: Value, _: Globals): int = valueToInt(item)) ==
            values)
  if not importedCallbackLocalIndexCases:
    quit(1)
  var importedCallbackLocalInputMismatchRejected = false
  try:
    discard importedDependentVectorCallback(identityDependentVectorCallback,
      3, @[1, 2])
  except ValueError as error:
    importedCallbackLocalInputMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert importedCallbackLocalInputMismatchRejected
  let wrongDependentVectorCallback: proc(length: int,
      values: seq[int]): seq[int] {.closure.} =
    proc(length: int, values: seq[int]): seq[int] = @[length]
  var importedCallbackLocalResultMismatchRejected = false
  try:
    discard importedDependentVectorCallback(wrongDependentVectorCallback,
      3, @[1, 2, 3])
  except ValueError as error:
    importedCallbackLocalResultMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert importedCallbackLocalResultMismatchRejected

  let importedDependentVectorCases = forAll(
    "typed imported wrappers carry dependent Vec indices", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(length: int): bool =
      let values = makeIndexedRuntimeValues(length)
      let direct = importedVectorIdentity(length, values)
      let runtime = importedVectorIdentityRuntimeValue(length, values)
      let decoded = vecValueToSeq[int](runtime.value, length, runtime.globals,
        "Vec", proc(item: Value, _: Globals): int = valueToInt(item))
      direct == values and decoded == values,
    shrinkInt)
  if not importedDependentVectorCases:
    quit(1)
  var importedVectorMismatchRejected = false
  try:
    discard importedVectorIdentity(3, @[1, 2])
  except ValueError as error:
    importedVectorMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert importedVectorMismatchRejected

  let tokenValue = makeRuntimeTokenRuntimeValue().value
  let unmappedGenericCases = forAll(
    "dynamic wrappers accept unmapped indexed Values", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(ignored: int): bool =
      let tokenProjection = genericRuntimeTokenProjectionRuntimeValueDynamic(
        tokenValue, ignored)
      tokenProjection.value.whnfKind == tokenValue.whnfKind and
        tokenProjection.value.whnfRefId == tokenValue.whnfRefId,
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
      let callback: RawRuntimeCallback =
        generatedRawTokenCallbackEcho(rawRuntimeIdentity)
      let wrapperResult = valueToInt(callback(intToValue(value))) == value
      let runtime = generatedRawTokenCallbackEchoRuntimeValue(
        rawRuntimeIdentity)
      let runtimeResult = valueToInt(callRuntimeValue(runtime.value,
        [intToValue(value)])) == value
      wrapperResult and runtimeResult,
    shrinkInt)
  if not rawCallbackCases:
    quit(1)

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
  let generatedTypedWrappersWork = generatedDefault() == 42 and
    generatedDefault(17) == 17 and
    valueToInt(generatedDefaultRuntimeValue().value) == 42 and
    valueToInt(generatedDefaultRuntimeValue(value = 17).value) == 17 and
    generatedAdd(20, 22) == 42 and generatedNamedAdd(20, 22) == 42 and
    generatedNatId(17) == 17 and generatedArithmetic(5, 7, 3) == -27 and
    generatedSigmaId((17, -9)) == (17, -9) and
    generatedOpaqueSigmaId((17, ChannelHandle(id: 1))) ==
      (17, ChannelHandle(id: 1))
  let generatedDefaultCases = forAll(
    "generated wrappers preserve omitted and overridden Nim defaults", r,
    200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      generatedDefault() == 42 and generatedDefault(value) == value and
      valueToInt(generatedDefaultRuntimeValue().value) == 42 and
      valueToInt(generatedDefaultRuntimeValue(value = value).value) == value,
    shrinkInt)
  if not generatedDefaultCases:
    quit(1)
  let namedArgumentCalls = forAll(
    "named arguments preserve checked callable parameter order", r, 200,
    proc(r: var Rng): tuple[left, right: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[left, right: int]): bool =
      generatedNamedAdd(input.left, input.right) == input.left + input.right and
      generatedNamedAlias(input.left, input.right) ==
        input.left + input.right,
    proc(input: tuple[left, right: int]):
        seq[tuple[left, right: int]] = @[])
  if not namedArgumentCalls:
    quit(1)
  let importedNamedArgumentCalls = forAll(
    "named arguments reorder imported checked callables", r, 200,
    proc(r: var Rng): tuple[left, right: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[left, right: int]): bool =
      generatedImportedNamed(input.left, input.right) == input.left,
    proc(input: tuple[left, right: int]):
        seq[tuple[left, right: int]] = @[])
  if not importedNamedArgumentCalls:
    quit(1)
  let checkedCallDefaults = forAll(
    "checked procedure calls apply positional and named defaults", r, 200,
    proc(r: var Rng): tuple[value, adjustment: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[value, adjustment: int]): bool =
      generatedDefaultGap(input.adjustment) == 42 + input.adjustment and
      generatedTrailingDefaultCall(input.value) == input.value + 5 and
      generatedDefaultThenValue(input.value, input.adjustment) ==
        input.value + input.adjustment,
    proc(input: tuple[value, adjustment: int]):
        seq[tuple[value, adjustment: int]] = @[])
  if not checkedCallDefaults:
    quit(1)
  let generatedRecordRoundTrips = forAll(
    "structural record codec preserves primitive and opaque fields", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let input = RuntimePoint(x: abs(n mod 1000),
        channel: ChannelHandle(id: n, label: "point-" & $n))
      generatedPointRebuild(input) == input,
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
      wrapperRoundTrip and runtimeRoundTrip and pairRoundTrip and
        importedPairRoundTrip and inputMismatchRejected and
        adapterMismatchRejected and importedAdapterMismatchRejected,
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
      let input = (length, (n, values))
      let roundTrips = generatedDependentPairVecIdentity(input) == input
      let badValues = if values.len == 0: @[n] else: values[0 ..< values.len - 1]
      var mismatchRejected = false
      try:
        discard generatedDependentPairVecIdentity((length, (n, badValues)))
      except ValueError:
        mismatchRejected = true
      roundTrips and mismatchRejected,
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
      let input = (outerLength, (innerLength, values))
      let roundTrips = generatedShadowedDependentPairVecIdentity(input) == input
      var mismatchRejected = false
      try:
        discard generatedShadowedDependentPairVecIdentity(
          (outerLength, (innerLength, values & @[n])))
      except ValueError:
        mismatchRejected = true
      roundTrips and mismatchRejected,
    shrinkInt)
  if not generatedTrustedDependentResultCases:
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
  let malformedZero = eval(
    tmApp(cachedGlobals["zero"].tm, tmInt(1)), @[])
  var appliedZeroRejected = false
  try:
    discard valueToNat(malformedZero, cachedGlobals)
  except ValueError:
    appliedZeroRejected = true
  if not appliedZeroRejected:
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

  let genericCallbackInferenceCases = forAll(
    "generic callback type infers from a later mapped value", r, 200,
    proc(r: var Rng): tuple[id, delta: int] =
      (r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[id, delta: int]): bool =
      let value = ChannelHandle(id: input.id, label: "generic-callback")
      let callback: proc(value: ChannelHandle): ChannelHandle {.closure.} =
        proc(value: ChannelHandle): ChannelHandle =
          ChannelHandle(id: value.id + input.delta,
            label: value.label & "/callback")
      let expected = callback(value)
      let typed = generatedGenericMappedCallback(callback, value)
      let runtime = generatedGenericMappedCallbackRuntimeValue(callback, value)
      validateRuntimeValueType(runtime.value,
        runtimeGlobalValue(runtime.globals, "Channel"), runtime.globals)
      typed == expected and
        valueToHost[ChannelHandle](runtime.value) == expected)
  if not genericCallbackInferenceCases:
    quit(1)

  let genericCallbackVectorInferenceCases = forAll(
    "generic callback type infers from a later mapped vector argument", r, 200,
    proc(r: var Rng): tuple[first, second: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[first, second: int]): bool =
      let values = @[ChannelHandle(id: input.first, label: "first"),
        ChannelHandle(id: input.second, label: "second")]
      let callback: proc(value: ChannelHandle): ChannelHandle {.closure.} =
        proc(value: ChannelHandle): ChannelHandle =
          ChannelHandle(id: value.id + 1, label: value.label & "/returned")
      let expected = @[callback(values[0]), callback(values[1])]
      let typed = generatedGenericCallbackOverVector(callback, values)
      let runtime = generatedGenericCallbackOverVectorRuntimeValue(callback,
        values)
      let expectedRuntimeType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Vec"),
        [runtimeGlobalValue(runtime.globals, "Channel"),
         natToValue(2, runtime.globals)])
      validateRuntimeValueType(runtime.value, expectedRuntimeType,
        runtime.globals)
      let decoded = vecValueToSeq[ChannelHandle](runtime.value, 2,
        runtime.globals, "Vec",
        proc(item: Value, _: Globals): ChannelHandle =
          valueToHost[ChannelHandle](item))
      var typedLengthRejected = false
      try:
        discard generatedGenericCallbackOverVector(callback, @[values[0]])
      except ValueError as error:
        typedLengthRejected = "runtime Vec length mismatch" in error.msg
      var runtimeLengthRejected = false
      try:
        discard generatedGenericCallbackOverVectorRuntimeValue(callback,
          @[values[0]])
      except ValueError as error:
        runtimeLengthRejected = "runtime Vec length mismatch" in error.msg
      typed == expected and decoded == expected and
        typedLengthRejected and runtimeLengthRejected)
  if not genericCallbackVectorInferenceCases:
    quit(1)

  let clauseDefinitionWrapperCases = forAll(
    "clause definitions get typed wrappers from checked Pi signatures", r, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(value: int): bool =
      let expected = value == 0
      let typed = checkedNatIdentity(value)
      let typedRuntime = checkedNatIdentityRuntimeValue(value)
      let rawRuntime = checkedNatIdentityRuntimeValue(
        [natToValue(value, typedRuntime.globals)])
      typed == value and
        valueToNat(typedRuntime.value, typedRuntime.globals) == value and
        valueToNat(rawRuntime.value, rawRuntime.globals) == value,
    shrinkInt)
  if not clauseDefinitionWrapperCases:
    quit(1)

  let recursiveClauseWrapperCases = forAll(
    "recursive two-argument clause definitions get typed wrappers", r, 200,
    proc(r: var Rng): tuple[left, right: int] =
      (r.genInt(0, 20), r.genInt(0, 20)),
    proc(input: tuple[left, right: int]): bool =
      let expected = input.left + input.right
      let typed = checkedNatAdd(input.left, input.right)
      let typedRuntime = checkedNatAddRuntimeValue(input.left, input.right)
      let rawRuntime = checkedNatAddRuntimeValue(
        [natToValue(input.left, typedRuntime.globals),
         natToValue(input.right, typedRuntime.globals)])
      typed == expected and
        valueToNat(typedRuntime.value, typedRuntime.globals) == expected and
        valueToNat(rawRuntime.value, rawRuntime.globals) == expected,
    proc(input: tuple[left, right: int]): seq[tuple[left, right: int]] =
      for left in shrinkInt(input.left):
        result.add((left, input.right))
      for right in shrinkInt(input.right):
        result.add((input.left, right)))
  if not recursiveClauseWrapperCases:
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
      let runtimeHandles = generatedVectorIdentityRuntimeValue[
        ChannelHandle, 4](handles)
      let expectedHandleVectorType = callRuntimeValue(
        runtimeGlobalValue(runtimeHandles.globals, "Vec"),
        [runtimeGlobalValue(runtimeHandles.globals, "Channel"),
         natToValue(4, runtimeHandles.globals)])
      validateRuntimeValueType(runtimeHandles.value,
        expectedHandleVectorType, runtimeHandles.globals)
      let expectedIntVectorType = callRuntimeValue(
        runtimeGlobalValue(runtimeHandles.globals, "Vec"),
        [runtimeGlobalValue(runtimeHandles.globals, "Int"),
         natToValue(4, runtimeHandles.globals)])
      var mismatchedElementTypeRejected = false
      try:
        validateRuntimeValueType(runtimeHandles.value,
          expectedIntVectorType, runtimeHandles.globals)
      except ValueError:
        mismatchedElementTypeRejected = true
      generatedVectorIdentity[int, 4](values) == values and
        generatedVectorIdentity[ChannelHandle, 4](handles) == handles and
        mismatchedElementTypeRejected and
        vecValueToSeq[ChannelHandle](runtimeHandles.value, 4,
          runtimeHandles.globals, "Vec",
          proc(item: Value, _: Globals): ChannelHandle =
            valueToHost[ChannelHandle](item)) == handles,
    shrinkInt)
  if not vectorCodecCases:
    quit(1)

  let inheritedTypeWitnessCases = forAll(
    "generic host type witnesses distinguish mapped object subtypes", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(id: int): bool =
      let baseInput = BaseRuntimeHandle(id: id)
      let childInput = DerivedRuntimeHandle(id: id + 1,
        label: "derived/" & $id)
      let baseRuntime = mappedGenericIdentityRuntimeValue[
        BaseRuntimeHandle](baseInput)
      let childRuntime = mappedGenericIdentityRuntimeValue[
        DerivedRuntimeHandle](childInput)
      validateRuntimeValueType(baseRuntime.value,
        runtimeGlobalValue(baseRuntime.globals, "BaseHandle"),
        baseRuntime.globals)
      validateRuntimeValueType(childRuntime.value,
        runtimeGlobalValue(childRuntime.globals, "DerivedHandle"),
        childRuntime.globals)
      valueToHost[BaseRuntimeHandle](baseRuntime.value).id == id and
        valueToHost[DerivedRuntimeHandle](childRuntime.value).id == id + 1 and
        valueToHost[DerivedRuntimeHandle](childRuntime.value).label ==
          "derived/" & $id,
    shrinkInt)
  if not inheritedTypeWitnessCases:
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
  let dynamicGenericValueVectorCases = forAll(
    "dynamic generic Vec values cross typed wrappers", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 30), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
      let typed = generatedGenericVectorValueBinderDynamic(
        input.length, values, 0)
      let runtime = generatedGenericVectorValueBinderRuntimeValueDynamic(
        input.length, values, 0)
      let expectedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Vec"),
        [runtimeGlobalValue(runtime.globals, "Int"),
         natToValue(input.length, runtime.globals)])
      validateRuntimeValueType(runtime.value, expectedType, runtime.globals)
      typed == values and
        vecValueToSeq[int](runtime.value, input.length, runtime.globals,
          "Vec", proc(value: Value, _: Globals): int = valueToInt(value)) ==
            values)
  if not dynamicGenericValueVectorCases:
    quit(1)
  let dynamicGenericValueSigmaCases = forAll(
    "dynamic generic Sigma values use recursive runtime codecs", r, 200,
    proc(r: var Rng): tuple[marker, first, second: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000),
       r.genInt(-1000, 1000)),
    proc(input: tuple[marker, first, second: int]): bool =
      let pair = (input.marker, @[input.first, input.second])
      let typed = generatedGenericSigmaValueBinderDynamic(pair, 0)
      let runtime = generatedGenericSigmaValueBinderRuntimeValueDynamic(pair, 0)
      typed == pair and valueToInt(runtimePairFirst(runtime.value)) ==
        input.marker and
        vecValueToSeq[int](runtimePairSecond(runtime.value), 2,
          runtime.globals, "Vec",
          proc(value: Value, _: Globals): int = valueToInt(value)) ==
            pair[1])
  if not dynamicGenericValueSigmaCases:
    quit(1)
  let dynamicGenericPiCallbackCases = forAll(
    "generic Pi value binders accept checked Nim closures", r, 200,
    proc(r: var Rng): tuple[offset, value: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[offset, value: int]): bool =
      let callback: proc(value: int): int {.closure.} =
        proc(value: int): int = value + input.offset
      let typed = generatedGenericPiCallbackBinderDynamic(callback,
        input.value)
      let runtime = generatedGenericPiCallbackBinderRuntimeValueDynamic(
        callback, input.value)
      typed == input.value + input.offset and
        valueToInt(runtime.value) == input.value + input.offset)
  if not dynamicGenericPiCallbackCases:
    quit(1)
  let dynamicGenericPiBinaryCallbackCases = forAll(
    "generic multi-argument Pi values accept typed Nim closures", r, 200,
    proc(r: var Rng): tuple[offset, left, right: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000),
       r.genInt(-1000, 1000)),
    proc(input: tuple[offset, left, right: int]): bool =
      let callback: proc(left, right: int): int {.closure.} =
        proc(left, right: int): int = left + right + input.offset
      let typed = generatedGenericPiBinaryCallbackBinderDynamic(callback,
        input.left, input.right)
      let runtime = generatedGenericPiBinaryCallbackBinderRuntimeValueDynamic(
        callback, input.left, input.right)
      typed == input.left + input.right + input.offset and
        valueToInt(runtime.value) ==
          input.left + input.right + input.offset)
  if not dynamicGenericPiBinaryCallbackCases:
    quit(1)
  let mappedGenericPiCallbackCases = forAll(
    "generic Pi callbacks preserve mapped Nim object values", r, 200,
    proc(r: var Rng): tuple[id, delta: int] =
      (r.genInt(-1000, 1000), r.genInt(-100, 100)),
    proc(input: tuple[id, delta: int]): bool =
      let channel = ChannelHandle(id: input.id, label: "pi/" & $input.id)
      let callback: proc(value: ChannelHandle): ChannelHandle {.closure.} =
        proc(value: ChannelHandle): ChannelHandle =
          ChannelHandle(id: value.id + input.delta,
            label: value.label & "/callback")
      let expected = callback(channel)
      let typed = generatedMappedGenericPiCallbackBinderDynamic(callback,
        channel)
      let runtime =
        generatedMappedGenericPiCallbackBinderRuntimeValueDynamic(callback,
          channel)
      validateRuntimeValueType(runtime.value,
        runtimeGlobalValue(runtime.globals, "Channel"), runtime.globals)
      typed == expected and valueToHost[ChannelHandle](runtime.value) ==
        expected)
  if not mappedGenericPiCallbackCases:
    quit(1)
  let dynamicDependentPiCallbackCases = forAll(
    "dependent generic Pi callbacks preserve Vec indices", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 20), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
      let callback: proc(length: int, values: seq[int]): seq[int] {.closure.} =
        proc(length: int, values: seq[int]): seq[int] = values
      let typed = generatedDependentPiCallbackBinderDynamic(callback,
        input.length, values)
      let runtime = generatedDependentPiCallbackBinderRuntimeValueDynamic(
        callback, input.length, values)
      typed == values and
        vecValueToSeq[int](runtime.value, input.length, runtime.globals,
          "Vec", proc(value: Value, _: Globals): int = valueToInt(value)) ==
            values)
  if not dynamicDependentPiCallbackCases:
    quit(1)
  let computedDependentPiCallbackCases = forAll(
    "generic Pi callbacks preserve computed Vec indices", r, 200,
    proc(r: var Rng): tuple[left, right, seed: int] =
      (r.genInt(0, 10), r.genInt(0, 10), r.genInt(-1000, 1000)),
    proc(input: tuple[left, right, seed: int]): bool =
      var values = newSeq[int](input.left + input.right)
      for i in 0 ..< values.len:
        values[i] = input.seed + i
      let callback: proc(left, right: int, values: seq[int]): seq[int]
          {.closure.} =
        proc(left, right: int, values: seq[int]): seq[int] = values
      let typed = generatedComputedDependentPiCallbackBinderDynamic(
        callback, input.left, input.right, values)
      let runtime = generatedComputedDependentPiCallbackBinderRuntimeValueDynamic(
        callback, input.left, input.right, values)
      typed == values and
        vecValueToSeq[int](runtime.value, input.left + input.right,
          runtime.globals, "Vec",
          proc(value: Value, _: Globals): int = valueToInt(value)) == values)
  if not computedDependentPiCallbackCases:
    quit(1)
  let customDependentPiCallbackCases = forAll(
    "generic Pi callbacks use dependent runtimeCodec mappings", r, 200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 20), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var tree = newSeq[int](input.length)
      for i in 0 ..< tree.len:
        tree[i] = input.seed + i
      let callback: proc(length: int, tree: seq[int]): seq[int] {.closure.} =
        proc(length: int, tree: seq[int]): seq[int] = tree
      let typed = generatedDependentCustomPiCallbackBinderDynamic(callback,
        input.length, tree)
      let runtime = generatedDependentCustomPiCallbackBinderRuntimeValueDynamic(
        callback, input.length, tree)
      typed == tree and
        decodeRuntimeSizedTree(runtime.value, runtime.globals) == tree)
  if not customDependentPiCallbackCases:
    quit(1)
  var customCallbackInputMismatchRejected = false
  try:
    let callback: proc(length: int, tree: seq[int]): seq[int] {.closure.} =
      proc(length: int, tree: seq[int]): seq[int] = tree
    discard generatedDependentCustomPiCallbackBinderDynamic(callback, 3,
      @[1, 2])
  except ValueError:
    customCallbackInputMismatchRejected = true
  doAssert customCallbackInputMismatchRejected
  var customCallbackOutputMismatchRejected = false
  try:
    let callback: proc(length: int, tree: seq[int]): seq[int] {.closure.} =
      proc(length: int, tree: seq[int]): seq[int] = tree & @[999]
    discard generatedDependentCustomPiCallbackBinderDynamic(callback, 2,
      @[1, 2])
  except ValueError:
    customCallbackOutputMismatchRejected = true
  doAssert customCallbackOutputMismatchRejected
  let nestedPiCallbackCases = forAll(
    "higher-order generic Pi callbacks bridge nested closures", r, 200,
    proc(r: var Rng): tuple[base, input: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[base, input: int]): bool =
      let inner: proc(value: int): int {.closure.} =
        proc(value: int): int = value + input.base
      let callback: proc(inner: proc(value: int): int {.closure.}): int
          {.closure.} =
        proc(inner: proc(value: int): int {.closure.}): int =
          inner(input.input)
      let expected = input.input + input.base
      let typed = generatedApplyNestedPiCallbackDynamic(callback, inner)
      let runtime = generatedApplyNestedPiCallbackRuntimeValueDynamic(
        callback, inner)
      typed == expected and valueToInt(runtime.value) == expected)
  if not nestedPiCallbackCases:
    quit(1)
  let nestedPiResultCallbackCases = forAll(
    "higher-order generic Pi callbacks return nested closures", r, 200,
    proc(r: var Rng): tuple[value, seed: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[value, seed: int]): bool =
      let callback: proc(value, seed: int): int {.closure.} =
        proc(value, seed: int): int = value + seed
      let typed = generatedReturnNestedPiCallbackDynamic(callback,
        input.value)
      let runtime = generatedReturnNestedPiCallbackRuntimeValueDynamic(
        callback, input.value)
      typed(input.seed) == input.value + input.seed and
        valueToInt(callRuntimeValue(runtime.value,
          @[intToValue(input.seed)])) == input.value + input.seed)
  if not nestedPiResultCallbackCases:
    quit(1)
  let genericPiCallbackConventionCases = forAll(
    "generic Pi wrappers infer Nim callback conventions", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      generatedGenericPiCallbackBinderDynamic(hostStepNim, value) == value + 7 and
        generatedGenericPiCallbackBinderDynamic(hostCdeclStepNim, value) ==
          value + 9)
  if not genericPiCallbackConventionCases:
    quit(1)
  var computedCallbackInputMismatchRejected = false
  try:
    let callback: proc(left, right: int, values: seq[int]): seq[int]
        {.closure.} =
      proc(left, right: int, values: seq[int]): seq[int] = values
    discard generatedComputedDependentPiCallbackBinderDynamic(callback, 2, 3,
      @[1, 2, 3, 4])
  except ValueError:
    computedCallbackInputMismatchRejected = true
  doAssert computedCallbackInputMismatchRejected
  var computedCallbackOutputMismatchRejected = false
  try:
    let callback: proc(left, right: int, values: seq[int]): seq[int]
        {.closure.} =
      proc(left, right: int, values: seq[int]): seq[int] = values & @[999]
    discard generatedComputedDependentPiCallbackBinderDynamic(callback, 2, 3,
      @[1, 2, 3, 4, 5])
  except ValueError:
    computedCallbackOutputMismatchRejected = true
  doAssert computedCallbackOutputMismatchRejected
  var dependentCallbackResultMismatchRejected = false
  try:
    let malformedCallback: proc(length: int, values: seq[int]): seq[int]
        {.closure.} = proc(length: int, values: seq[int]): seq[int] =
      values & @[999]
    discard generatedDependentPiCallbackBinderDynamic(malformedCallback,
      2, @[1, 2])
  except ValueError:
    dependentCallbackResultMismatchRejected = true
  doAssert dependentCallbackResultMismatchRejected
  var dependentCallbackInputMismatchRejected = false
  try:
    let callback: proc(length: int, values: seq[int]): seq[int] {.closure.} =
      proc(length: int, values: seq[int]): seq[int] = values
    discard generatedDependentPiCallbackBinderDynamic(callback, 3, @[1, 2])
  except ValueError:
    dependentCallbackInputMismatchRejected = true
  doAssert dependentCallbackInputMismatchRejected
  let dynamicGenericDependentSigmaCases = forAll(
    "dependent Sigma generic binders retain their Vec index", r, 200,
    proc(r: var Rng): tuple[length, seed, ignored: int] =
      (r.genInt(0, 20), r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed, ignored: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
      let pair = (input.length, values)
      let typed = generatedGenericDependentSigmaValueBinderDynamic(pair,
        input.ignored)
      let runtime =
        generatedGenericDependentSigmaValueBinderRuntimeValueDynamic(pair,
          input.ignored)
      valueToNat(runtimePairFirst(runtime.value), runtime.globals) ==
        input.length and
        vecValueToSeq[int](runtimePairSecond(runtime.value), input.length,
          runtime.globals, "Vec",
          proc(value: Value, _: Globals): int = valueToInt(value)) == values and
        typed == pair)
  if not dynamicGenericDependentSigmaCases:
    quit(1)
  let validatedDependentSigmaCases = forAll(
    "dependent Sigma generic binders validate without a trusted opt-in", r,
    200,
    proc(r: var Rng): tuple[length, seed, ignored: int] =
      (r.genInt(0, 20), r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed, ignored: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
      let pair = (input.length, values)
      let runtime =
        generatedValidatedDependentSigmaValueBinderRuntimeValueDynamic(
          pair, input.ignored)
      generatedValidatedDependentSigmaValueBinderDynamic(pair,
        input.ignored) == pair and
        valueToNat(runtimePairFirst(runtime.value), runtime.globals) ==
          input.length)
  if not validatedDependentSigmaCases:
    quit(1)
  let dependentGenericSigmaValueCases = forAll(
    "trusted dependent Sigma generic binders check their Vec lengths", r,
    200,
    proc(r: var Rng): tuple[length: int, seed: int] =
      (r.genInt(0, 30), r.genInt(-1000, 1000)),
    proc(input: tuple[length: int, seed: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
      let pair = (input.length, values)
      let typed = generatedGenericDependentPairValueBinderDynamic(pair, 0)
      let runtime =
        generatedGenericDependentPairValueBinderRuntimeValueDynamic(pair, 0)
      typed == pair and
        valueToNat(runtimePairFirst(runtime.value), runtime.globals) ==
          input.length and
        vecValueToSeq[int](runtimePairSecond(runtime.value), input.length,
          runtime.globals, "Vec",
          proc(value: Value, _: Globals): int = valueToInt(value)) == values)
  if not dependentGenericSigmaValueCases:
    quit(1)
  let validatedDependentGenericSigmaCases = forAll(
    "dependent Vec Sigma binders validate without a trust opt-in", r,
    200,
    proc(r: var Rng): tuple[length: int, seed: int] =
      (r.genInt(0, 30), r.genInt(-1000, 1000)),
    proc(input: tuple[length: int, seed: int]): bool =
      var values = newSeq[seq[int]](input.length + 1)
      for i in 0 ..< values.len:
        values[i] = newSeq[int](input.length)
        for j in 0 ..< values[i].len:
          values[i][j] = input.seed + i + j
      let pair = (input.length, values)
      let typed = generatedValidatedDependentPairValueBinderDynamic(pair, 0)
      let runtime =
        generatedValidatedDependentPairValueBinderRuntimeValueDynamic(pair, 0)
      typed == pair and
        valueToNat(runtimePairFirst(runtime.value), runtime.globals) ==
          input.length and
        vecValueToSeq[seq[int]](runtimePairSecond(runtime.value),
          input.length + 1, runtime.globals, "Vec",
          proc(value: Value, globals: Globals): seq[int] =
            vecValueToSeq[int](value, input.length, globals, "Vec",
              proc(item: Value, _: Globals): int = valueToInt(item))) == values)
  if not validatedDependentGenericSigmaCases:
    quit(1)
  var validatedDependentGenericSigmaMismatchRejected = false
  try:
    discard generatedValidatedDependentPairValueBinderDynamic(
      (3, @[@[1, 2, 3], @[1, 2, 3], @[1, 2, 3]]), 0)
  except ValueError as error:
    validatedDependentGenericSigmaMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert validatedDependentGenericSigmaMismatchRejected
  var validatedNestedDependentGenericSigmaMismatchRejected = false
  try:
    discard generatedValidatedDependentPairValueBinderDynamic(
      (3, @[@[1, 2], @[1, 2, 3], @[1, 2, 3], @[1, 2, 3]]), 0)
  except ValueError as error:
    validatedNestedDependentGenericSigmaMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert validatedNestedDependentGenericSigmaMismatchRejected
  var dependentGenericSigmaMismatchRejected = false
  try:
    discard generatedGenericDependentPairValueBinderDynamic((3, @[1, 2]), 0)
  except ValueError as error:
    dependentGenericSigmaMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert dependentGenericSigmaMismatchRejected
  let conditionalGenericValueCases = forAll(
    "Bool conditional indices validate generic Vec and Sigma values", r, 200,
    proc(r: var Rng): tuple[condition: bool, yesLength, noLength, seed: int] =
      (r.genBool(), r.genInt(0, 12), r.genInt(0, 12),
       r.genInt(-1000, 1000)),
    proc(input: tuple[condition: bool, yesLength, noLength, seed: int]):
        bool =
      let length = if input.condition: input.yesLength else: input.noLength
      var values = newSeq[int](length)
      for i in 0 ..< length:
        values[i] = input.seed + i
      let pair = (7, values)
      let typedVector = generatedConditionalGenericVectorValueDynamic(
        input.condition, input.yesLength, input.noLength, values, 0)
      let runtimeVector = generatedConditionalGenericVectorValueRuntimeValueDynamic(
        input.condition, input.yesLength, input.noLength, values, 0)
      let typedSigma = generatedConditionalGenericSigmaValueDynamic(
        input.condition, input.yesLength, input.noLength, pair, 0)
      let runtimeSigma = generatedConditionalGenericSigmaValueRuntimeValueDynamic(
        input.condition, input.yesLength, input.noLength, pair, 0)
      typedVector == values and typedSigma == pair and
        vecValueToSeq[int](runtimeVector.value, length, runtimeVector.globals,
          "Vec", proc(value: Value, _: Globals): int = valueToInt(value)) ==
            values and
        valueToNat(runtimePairFirst(runtimeSigma.value), runtimeSigma.globals) ==
          7 and
        vecValueToSeq[int](runtimePairSecond(runtimeSigma.value), length,
          runtimeSigma.globals, "Vec",
          proc(value: Value, _: Globals): int = valueToInt(value)) == values)
  if not conditionalGenericValueCases:
    quit(1)
  let logicalConditionalVectorCases = forAll(
    "logical Bool expressions select dynamic generic Vec indices", r, 200,
    proc(r: var Rng): tuple[b, c: bool, yesLength, noLength, seed: int] =
      (r.genBool(), r.genBool(), r.genInt(0, 12), r.genInt(0, 12),
       r.genInt(-1000, 1000)),
    proc(input: tuple[b, c: bool, yesLength, noLength, seed: int]): bool =
      proc checkVector(expectedLength: int, typed: seq[int], value: Value,
          globals: Globals): bool =
        typed.len == expectedLength and
          vecValueToSeq[int](value, expectedLength, globals, "Vec",
            proc(value: Value, _: Globals): int = valueToInt(value)) == typed
      let andLength = if input.b and input.c:
        input.yesLength else: input.noLength
      let notLength = if not input.b:
        input.yesLength else: input.noLength
      let orLength = if input.b or input.c:
        input.yesLength else: input.noLength
      var andValues = newSeq[int](andLength)
      var notValues = newSeq[int](notLength)
      var orValues = newSeq[int](orLength)
      for i in 0 ..< andLength: andValues[i] = input.seed + i
      for i in 0 ..< notLength: notValues[i] = input.seed - i
      for i in 0 ..< orLength: orValues[i] = input.seed * (i + 1)
      let andTyped = generatedAndConditionalVectorValueDynamic(
        input.b, input.c, input.yesLength, input.noLength, andValues, 0)
      let andRuntime = generatedAndConditionalVectorValueRuntimeValueDynamic(
        input.b, input.c, input.yesLength, input.noLength, andValues, 0)
      let notTyped = generatedNotConditionalVectorValueDynamic(
        input.b, input.yesLength, input.noLength, notValues, 0)
      let notRuntime = generatedNotConditionalVectorValueRuntimeValueDynamic(
        input.b, input.yesLength, input.noLength, notValues, 0)
      let orTyped = generatedOrConditionalVectorValueDynamic(
        input.b, input.c, input.yesLength, input.noLength, orValues, 0)
      let orRuntime = generatedOrConditionalVectorValueRuntimeValueDynamic(
        input.b, input.c, input.yesLength, input.noLength, orValues, 0)
      checkVector(andLength, andTyped, andRuntime.value, andRuntime.globals) and
        checkVector(notLength, notTyped, notRuntime.value, notRuntime.globals) and
        checkVector(orLength, orTyped, orRuntime.value, orRuntime.globals))
  if not logicalConditionalVectorCases:
    quit(1)
  for b in [false, true]:
    for c in [false, true]:
      let andLength = if b and c: 2 else: 4
      let notLength = if not b: 2 else: 4
      let orLength = if b or c: 2 else: 4
      var andRejected = false
      try:
        discard generatedAndConditionalVectorValueDynamic(
          b, c, 2, 4, newSeq[int](andLength + 1), 0)
      except ValueError as error:
        andRejected = "runtime Vec length mismatch" in error.msg
      doAssert andRejected
      var notRejected = false
      try:
        discard generatedNotConditionalVectorValueDynamic(
          b, 2, 4, newSeq[int](notLength + 1), 0)
      except ValueError as error:
        notRejected = "runtime Vec length mismatch" in error.msg
      doAssert notRejected
      var orRejected = false
      try:
        discard generatedOrConditionalVectorValueDynamic(
          b, c, 2, 4, newSeq[int](orLength + 1), 0)
      except ValueError as error:
        orRejected = "runtime Vec length mismatch" in error.msg
      doAssert orRejected
  for condition in [true, false]:
    let expectedLength = if condition: 2 else: 4
    let invalidValues = newSeq[int](expectedLength + 1)
    var conditionalVectorMismatchRejected = false
    try:
      discard generatedConditionalGenericVectorValueDynamic(
        condition, 2, 4, invalidValues, 0)
    except ValueError as error:
      conditionalVectorMismatchRejected =
        "runtime Vec length mismatch" in error.msg
    doAssert conditionalVectorMismatchRejected
    var conditionalSigmaMismatchRejected = false
    try:
      discard generatedConditionalGenericSigmaValueRuntimeValueDynamic(
        condition, 2, 4, (7, invalidValues), 0)
    except ValueError as error:
      conditionalSigmaMismatchRejected =
        "runtime Vec length mismatch" in error.msg
    doAssert conditionalSigmaMismatchRejected
  var dynamicGenericValueSigmaMismatchRejected = false
  try:
    discard generatedGenericSigmaValueBinderDynamic((1, @[2, 3, 4]), 0)
  except ValueError as error:
    dynamicGenericValueSigmaMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert dynamicGenericValueSigmaMismatchRejected
  var dynamicGenericDependentSigmaMismatchRejected = false
  try:
    discard generatedGenericDependentSigmaValueBinderDynamic((3, @[1, 2]), 0)
  except ValueError as error:
    dynamicGenericDependentSigmaMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert dynamicGenericDependentSigmaMismatchRejected
  var validatedDependentSigmaMismatchRejected = false
  try:
    discard generatedValidatedDependentSigmaValueBinderDynamic((3, @[1, 2]), 0)
  except ValueError as error:
    validatedDependentSigmaMismatchRejected =
      "runtime Vec length mismatch" in error.msg or
      "runtime value does not match its expected Eponym type" in error.msg
  doAssert validatedDependentSigmaMismatchRejected
  var dynamicGenericValueVectorMismatchRejected = false
  try:
    discard generatedGenericVectorValueBinderDynamic(3, @[1, 2], 0)
  except ValueError as error:
    dynamicGenericValueVectorMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert dynamicGenericValueVectorMismatchRejected
  var runtimeGenericValueVectorMismatchRejected = false
  try:
    discard generatedGenericVectorValueBinderRuntimeValueDynamic(
      3, @[1, 2], 0)
  except ValueError as error:
    runtimeGenericValueVectorMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert runtimeGenericValueVectorMismatchRejected
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
      let expectedListType = callRuntimeValue(
        runtimeGlobalValue(intRuntime.globals, "List"),
        [runtimeGlobalValue(intRuntime.globals, "Int")])
      validateRuntimeValueType(intRuntime.value, expectedListType,
        intRuntime.globals)
      let rawIntRuntime = generatedIntListIdentityRuntimeValue([intRuntime.value])
      let runtime = generatedListIdentityRuntimeValue[int](values)
      let rawRuntime = generatedListIdentityRuntimeValue[int]([runtime.value])
      let opaqueRuntime = generatedListIdentityRuntimeValue[ChannelHandle](handles)
      generatedIntListIdentity(values) == values and
      generatedEmptyIntList() == @[] and
      generatedBoundEmptyIntList() == @[] and
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
  let dynamicGenericListCases = forAll(
    "generic List values use the registered dynamic codec", r, 200,
    proc(r: var Rng): tuple[length, seed, ignored: int] =
      (r.genInt(0, 12), r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed, ignored: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< input.length:
        values[i] = input.seed + i
      let typed = generatedGenericListValueBinderDynamic(values,
        input.ignored)
      let runtime = generatedGenericListValueBinderRuntimeValueDynamic(values,
        input.ignored)
      typed == values and decodeRuntimeIntList(runtime.value,
        runtime.globals) == values)
  if not dynamicGenericListCases:
    quit(1)

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
      let expectedOptionType = callRuntimeValue(
        runtimeGlobalValue(primitiveRuntime.globals, "Option"),
        [runtimeGlobalValue(primitiveRuntime.globals, "Int")])
      validateRuntimeValueType(primitiveRuntime.value, expectedOptionType,
        primitiveRuntime.globals)
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
  let dynamicGenericOptionCases = forAll(
    "generic Option values use the registered dynamic codec", r, 200,
    proc(r: var Rng): tuple[present: bool, seed, ignored: int] =
      (r.genBool(), r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[present: bool, seed, ignored: int]): bool =
      let value = if input.present: some(input.seed) else: none(int)
      let typed = generatedGenericOptionValueBinderDynamic(value,
        input.ignored)
      let runtime = generatedGenericOptionValueBinderRuntimeValueDynamic(value,
        input.ignored)
      let decoded = valueToOption[int](runtime.value, runtime.globals,
        "Option", proc(item: Value, _: Globals): int = valueToInt(item))
      typed == value and decoded == value)
  if not dynamicGenericOptionCases:
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
      generatedTreeIdentity(values) == values and
        generatedBoundTreeReverse(values) == reverseRuntimeTree(values) and
        decodeRuntimeTree(runtime.value, runtime.globals) == values and
        decodeRuntimeTree(rawRuntime.value, rawRuntime.globals) == values,
    )
  if not customCodecCases:
    quit(1)

  let genericCustomCodecVectorCases = forAll(
    "generic Vec callbacks use a custom element codec", r, 200,
    proc(r: var Rng): tuple[first, second, seed: int] =
      (r.genInt(-1000, 1000), r.genInt(-1000, 1000),
       r.genInt(-1000, 1000)),
    proc(input: tuple[first, second, seed: int]): bool =
      let values = @[@[input.first, input.seed], @[input.second]]
      let callback: proc(value: seq[int]): seq[int] {.closure.} =
        proc(value: seq[int]): seq[int] = reverseRuntimeTree(value)
      let expected = @[reverseRuntimeTree(values[0]),
                       reverseRuntimeTree(values[1])]
      let typed = generatedGenericTreeVectorMap[seq[int], 2](callback, values)
      let runtime = generatedGenericTreeVectorMapRuntimeValue[seq[int], 2](
        callback, values)
      let expectedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Vec"),
        [runtimeGlobalValue(runtime.globals, "Tree"),
         natToValue(2, runtime.globals)])
      validateRuntimeValueType(runtime.value, expectedType, runtime.globals)
      let decoded = vecValueToSeq[seq[int]](runtime.value, 2,
        runtime.globals, "Vec", decodeRuntimeTree)
      var wrongLengthRejected = false
      try:
        discard generatedGenericTreeVectorMap[seq[int], 2](callback,
          @[values[0]])
      except ValueError as error:
        wrongLengthRejected = "runtime Vec length mismatch" in error.msg
      typed == expected and decoded == expected and wrongLengthRejected)
  if not genericCustomCodecVectorCases:
    quit(1)
  let genericCustomCodecValueCases = forAll(
    "mapped custom values cross as dynamic generic binders", r, 200,
    proc(r: var Rng): tuple[values: seq[int], ignored: int] =
      result.values = newSeq[int](r.genInt(0, 8))
      for i in 0 ..< result.values.len:
        result.values[i] = r.genInt(-1000, 1000)
      result.ignored = r.genInt(-1000, 1000)
    ,
    proc(input: tuple[values: seq[int], ignored: int]): bool =
      let typed = generatedGenericTreeValueBinderDynamic(input.values,
        input.ignored)
      let runtime = generatedGenericTreeValueBinderRuntimeValueDynamic(
        input.values, input.ignored)
      validateRuntimeValueType(runtime.value,
        runtimeGlobalValue(runtime.globals, "Tree"), runtime.globals)
      typed == input.values and
        decodeRuntimeTree(runtime.value, runtime.globals) == input.values)
  if not genericCustomCodecValueCases:
    quit(1)
  let indexedCustomCodecValueCases = forAll(
    "indexed custom codecs validate dynamic generic values", r, 200,
    proc(r: var Rng): tuple[length, seed, ignored: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed, ignored: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< values.len:
        values[i] = input.seed + i
      let typed = generatedGenericSizedTreeBinderDynamic(input.length,
        values, input.ignored)
      let runtime = generatedGenericSizedTreeBinderRuntimeValueDynamic(
        input.length, values, input.ignored)
      let expectedType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "SizedTree"),
        [natToValue(input.length, runtime.globals)])
      validateRuntimeValueType(runtime.value, expectedType, runtime.globals)
      let decoded = decodeRuntimeSizedTree(runtime.value, runtime.globals)
      var typedMismatchRejected = false
      try:
        discard generatedGenericSizedTreeBinderDynamic(input.length,
          values & @[input.seed], input.ignored)
      except ValueError:
        typedMismatchRejected = true
      var runtimeMismatchRejected = false
      try:
        discard generatedGenericSizedTreeBinderRuntimeValueDynamic(
          input.length, values & @[input.seed], input.ignored)
      except ValueError:
        runtimeMismatchRejected = true
      typed == values and decoded == values and typedMismatchRejected and
        runtimeMismatchRejected)
  if not indexedCustomCodecValueCases:
    quit(1)
  let customDependentSigmaCases = forAll(
    "dependent Sigma generic binders validate custom codec indices", r, 200,
    proc(r: var Rng): tuple[length, seed, ignored: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed, ignored: int]): bool =
      var values = newSeq[int](input.length)
      for i in 0 ..< values.len:
        values[i] = input.seed + i
      let pair = (input.length, values)
      let typed = generatedValidatedCustomDependentSigmaBinderDynamic(
        pair, input.ignored)
      let runtime = generatedValidatedCustomDependentSigmaBinderRuntimeValueDynamic(
        pair, input.ignored)
      let expectedType = runtimeDependentSigmaType(
        runtimeGlobalValue(runtime.globals, "Nat"), runtime.globals,
        proc(length: Value): Value = callRuntimeValue(
          runtimeGlobalValue(runtime.globals, "SizedTree"), [length]))
      validateRuntimeValueAgainstType(runtime.value, expectedType,
        runtime.globals)
      var mismatchRejected = false
      try:
        discard generatedValidatedCustomDependentSigmaBinderDynamic(
          (input.length + 1, values), input.ignored)
      except ValueError:
        mismatchRejected = true
      typed == pair and mismatchRejected)
  if not customDependentSigmaCases:
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
      let innerVectorType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Vec"),
        [runtimeGlobalValue(runtime.globals, "Int"),
         natToValue(2, runtime.globals)])
      let expectedMatrixType = callRuntimeValue(
        runtimeGlobalValue(runtime.globals, "Vec"),
        [innerVectorType, natToValue(3, runtime.globals)])
      validateRuntimeValueType(runtime.value, expectedMatrixType,
        runtime.globals)
      let rawRuntime = generatedNestedVectorIdentityRuntimeValue[2, 3](
        [runtime.value])
      generatedNestedVectorIdentity[2, 3](matrix) == matrix and
        decodeRuntimeIntMatrix(runtime.value, 3, runtime.globals) == matrix and
        decodeRuntimeIntMatrix(rawRuntime.value, 3, rawRuntime.globals) == matrix,
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
      let runtimeLength = valueToNat(runtimePairFirst(runtime.value),
        runtime.globals) + valueToNat(runtimePairFirst(
          runtimePairSecond(runtime.value)), runtime.globals)
      let rawLength = valueToNat(runtimePairFirst(rawRuntime.value),
        rawRuntime.globals) + valueToNat(runtimePairFirst(
          runtimePairSecond(rawRuntime.value)), rawRuntime.globals)
      generatedSizedVecIdentity(value) == value and
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
  let genericDependentRecordCases = forAll(
    "trusted dependent record binders use dynamic runtime codecs", r, 200,
    proc(r: var Rng): tuple[prefixLength, suffixLength, seed: int] =
      (r.genInt(0, 4), r.genInt(0, 4), r.genInt(-1000, 1000)),
    proc(input: tuple[prefixLength, suffixLength, seed: int]): bool =
      let length = input.prefixLength + input.suffixLength
      var values = newSeq[int](length)
      for i in 0 ..< values.len:
        values[i] = input.seed + i
      let value = RuntimeSizedVec(prefixLength: input.prefixLength,
        suffixLength: input.suffixLength, values: values)
      let typed = generatedGenericSizedVecValueBinderDynamic(value, 0)
      let runtime = generatedGenericSizedVecValueBinderRuntimeValueDynamic(
        value, 0)
      let runtimeLength = valueToNat(runtimePairFirst(runtime.value),
        runtime.globals) + valueToNat(runtimePairFirst(
          runtimePairSecond(runtime.value)), runtime.globals)
      typed == value and runtimeLength == length and
        decodeRuntimeIntVector(runtimePairFirst(
          runtimePairSecond(runtimePairSecond(runtime.value))), runtimeLength,
          runtime.globals) == values)
  if not genericDependentRecordCases:
    quit(1)
  let validatedDependentRecordCases = forAll(
    "dependent record binders validate nested Vec indices without trust", r,
    200,
    proc(r: var Rng): tuple[length, seed: int] =
      (r.genInt(0, 8), r.genInt(-1000, 1000)),
    proc(input: tuple[length, seed: int]): bool =
      var values = newSeq[seq[int]](input.length + 1)
      for i in 0 ..< values.len:
        values[i] = newSeq[int](input.length)
        for j in 0 ..< values[i].len:
          values[i][j] = input.seed + i + j
      let host = RuntimeCheckedSizedVec(length: input.length,
        values: values)
      let typed = generatedValidatedDependentRecordValueDynamic(host, 0)
      let runtime = generatedValidatedDependentRecordValueRuntimeValueDynamic(
        host, 0)
      typed == host and
        valueToNat(runtimePairFirst(runtime.value), runtime.globals) ==
          input.length and
        vecValueToSeq[seq[int]](runtimePairFirst(
          runtimePairSecond(runtime.value)),
          input.length + 1, runtime.globals, "Vec",
          proc(value: Value, globals: Globals): seq[int] =
            vecValueToSeq[int](value, input.length, globals, "Vec",
              proc(item: Value, _: Globals): int = valueToInt(item))) == values)
  if not validatedDependentRecordCases:
    quit(1)
  var validatedDependentRecordOuterMismatchRejected = false
  try:
    discard generatedValidatedDependentRecordValueDynamic(
      RuntimeCheckedSizedVec(length: 3,
        values: @[@[1, 2, 3], @[1, 2, 3], @[1, 2, 3]]), 0)
  except ValueError as error:
    validatedDependentRecordOuterMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert validatedDependentRecordOuterMismatchRejected
  var validatedDependentRecordInnerMismatchRejected = false
  try:
    discard generatedValidatedDependentRecordValueDynamic(
      RuntimeCheckedSizedVec(length: 3,
        values: @[@[1, 2], @[1, 2, 3], @[1, 2, 3], @[1, 2, 3]]), 0)
  except ValueError as error:
    validatedDependentRecordInnerMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert validatedDependentRecordInnerMismatchRejected
  var genericDependentRecordMismatchRejected = false
  try:
    discard generatedGenericSizedVecValueBinderDynamic(
      RuntimeSizedVec(prefixLength: 1, suffixLength: 2, values: @[1, 2]), 0)
  except ValueError as error:
    genericDependentRecordMismatchRejected =
      "runtime Vec length mismatch" in error.msg
  doAssert genericDependentRecordMismatchRejected
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

  let nimcallCallbackCases = forAll(
    "Nim callbacks cross into checked function arguments", r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(value: int): bool =
      generatedApplyNimcallCallback(hostNimcallIncrement, value) == value + 1 and
        generatedApplyCdeclCallback(hostCdeclStepNim, value) == value + 9,
    shrinkInt)
  if not nimcallCallbackCases:
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
      let direct = generatedApplyTwoArgumentCallback(callback, seed, -seed)
      let runtime = generatedApplyTwoArgumentCallbackRuntimeValue(
        callback, seed, -seed)
      direct == seed and valueToInt(runtime.value) == seed and
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
