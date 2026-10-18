## Runtime bridge checks for Eponym values that do not use the generated Int ABI.

import std/[os, tables, strutils, asyncdispatch]
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

type ChannelHandle = object
  id: int
  label: string

type NimIntCallback = proc(value: int): int {.closure.}

type RuntimePoint = object
  x: int
  channel: ChannelHandle

proc hostWrongFour(channel: ChannelHandle, message: string,
                   requestId, phase: int): int = channel.id + requestId + phase

proc hostRotateChannel(channel: ChannelHandle): ChannelHandle =
  result = channel
  inc result.id
  result.label.add("*")

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

proc hostFutureForChannel(channel: ChannelHandle): Future[int] =
  result = newFuture[int]("hostFutureForChannel")
  result.complete(channel.id)

proc hostFutureIdentity(value: Future[int]): Future[int] = value

proc hostInvokeCallback(callback: NimIntCallback, value: int): int =
  callback(value)

proc hostWrongRoute(channel: int, message: string): int = channel + message.len

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
  record(Point):
    field(x, Nat)
    field(channel, Channel)
  runtimeType(Point, RuntimePoint)
  proc generatedPointId(value: Point): Point = value
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
  proc generatedFutureRole(channel: Channel): PendingResult =
    startFuture(channel)
  proc generatedFutureInput(value: PendingResult): PendingResult =
    passFuture(value)
  proc generatedOpaqueSigmaId(value: Sig(Nat, Channel)): Sig(Nat, Channel) =
    value
  proc generatedCallbackRole(callback: Callback, value: Sample): Sample =
    invokeCallback(callback, value)

static:
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
  doAssert compiles(generatedCallbackRole(proc(value: int): int = value + 1, 1))
  doAssert not compiles(generatedCallbackRole(42, 1))

when isMainModule:
  let baseDir = currentSourcePath().parentDir.parentDir
  var r = initRng(424242'u64)

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
      generatedPointId(input) == input,
    shrinkInt)
  if not generatedRecordRoundTrips:
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
