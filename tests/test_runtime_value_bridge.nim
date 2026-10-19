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
proc runtimeTreePayloads(value: Value, globals: Globals): seq[int] =
  var current = value
  while true:
    let variant = valueToRuntimeVariant(current, globals, "RuntimeTree",
      ["treeEmpty", "treeNode"])
    if variant.constructor == "treeEmpty": return
    result.add(valueToInt(variant.arguments[0]))
    current = variant.arguments[1]

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

proc encodeRuntimeHandle(value: ChannelHandle, globals: Globals): Value =
  runtimeVariantToValue(RuntimeVariant(constructor: "runtimeHandle",
    arguments: @[intToValue(value.id)]), globals, "RuntimeHandle",
    ["runtimeHandle"])

proc decodeRuntimeHandle(value: Value, globals: Globals): ChannelHandle =
  let variant = valueToRuntimeVariant(value, globals, "RuntimeHandle",
    ["runtimeHandle"])
  let id = valueToInt(variant.arguments[0])
  ChannelHandle(id: id, label: "decoded-" & $id)

proc encodeWrongRuntimeHandle(value: ChannelHandle, globals: Globals): Value =
  intToValue(value.id)

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
  proc generatedAdd(left: Int, right: Int): Int = addInt(left, right)
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
  runtimeValue(generatedAdd)

eponymBlock:
  import "fixtures/runtime_imported_value.ep"
  bindPostulate(importedStep, hostStepNim)
  runtimeValue(importedIdentity)
  runtimeValue(importedApply)

eponymBlock:
  import "fixtures/runtime_imported_vec.ep"
  runtimeVector(Vec)
  runtimeValue(importedVectorIdentity)

eponymBlock:
  import "fixtures/runtime_imported_generic.ep"
  runtimeVector(Vec)
  runtimeType(Token, ImportedToken)
  runtimeValue(importedIntIdentity)
  runtimeValue(importedGenericIdentity)
  runtimeValue(importedImplicitGenericIdentity)
  runtimeValue(importedImplicitNatVecIdentity)
  runtimeValue(importedImplicitBoolIdentity)
  runtimeValue(importedImplicitIntIdentity)
  runtimeValue(importedImplicitTokenIdentity)
  runtimeValue(importedCallbackApply)
  runtimeValue(importedCallbackApply2)
  runtimeValue(importedCallbackIdentity)
  runtimeValue(importedDependentCallbackApply)
  runtimePairTrusted(importedDependentPairIdentity)
  runtimeValue(importedDependentPairIdentity)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  runtimeCodec(RuntimeHandle, ChannelHandle, encodeRuntimeHandle,
    decodeRuntimeHandle)
  runtimeType(RuntimeOpaqueToken, ChannelHandle)
  runtimeDataVariant(RuntimeTree)
  runtimeDataVariant(SizedTree)
  runtimeDataVariant(DecisionTree)
  runtimeDataVariant(HandleEnvelope)
  runtimeValue(treeIdentity)
  runtimeValue(decisionIdentity)
  runtimeValue(handleEnvelopeIdentity)
  proc generatedSizedTreeRawIdentity(length: Nat,
      tree: SizedTree[length]): SizedTree[length] = tree
  runtimeValue(generatedSizedTreeRawIdentity)
  proc genericIndexedTreeProjection[length: Nat,
      tree: SizedTree[length]](ignored: Int): SizedTree[length] = tree
  runtimeValue(genericIndexedTreeProjection)

eponymBlock:
  import "fixtures/runtime_variant.ep"
  proc genericUnmappedSizedTreeProjection[length: Nat,
      tree: SizedTree[length]](ignored: Int): SizedTree[length] = tree
  runtimeValue(genericUnmappedSizedTreeProjection)

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
    lam(length, Nat, lam(values, Vec(Int, length), length))
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
  doAssert not compiles(generatedApplyNimCallback(
    proc(value: string): string = value, 1))
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
      let projected = genericIndexedTreeProjectionRuntimeValueDynamic(
        length, valueToRuntimeStructuredVariant(indexed, variantGlobals,
          "SizedTree", ["sizedTree"]), 0)
      let decoded = valueToRuntimeStructuredVariant(projected.value,
        variantGlobals,
        "SizedTree", ["sizedTree"])
      decoded.constructor == "sizedTree" and
      decoded.arguments.len == 2 and
        decoded.arguments[0].kind == rsvNat and
        decoded.arguments[0].natValue == length and
        decoded.arguments[1].kind == rsvVariant and
        decoded.arguments[1].variantValue.constructor == "treeEmpty",
    shrinkInt)
  if not appliedGenericTypeCases:
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
  let generatedTypedWrappersWork = generatedAdd(20, 22) == 42 and
    generatedNatId(17) == 17 and generatedArithmetic(5, 7, 3) == -27 and
    generatedSigmaId((17, -9)) == (17, -9) and
    generatedOpaqueSigmaId((17, ChannelHandle(id: 1))) ==
      (17, ChannelHandle(id: 1))
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
        rawInputMismatchRejected and adapterMismatchRejected and
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
      let input = (length, (n, values))
      let roundTrips = generatedDependentPairVecIdentity(input) == input
      let runtime = generatedDependentPairVecIdentityRuntimeValue(input)
      let rawRuntime = generatedDependentPairVecIdentityRuntimeValue(
        [runtime.value])
      let badValues = if values.len == 0: @[n] else: values[0 ..< values.len - 1]
      var mismatchRejected = false
      try:
        discard generatedDependentPairVecIdentity((length, (n, badValues)))
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
