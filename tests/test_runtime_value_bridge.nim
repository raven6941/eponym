## Runtime bridge checks for Eponym values that do not use the generated Int ABI.

import std/[os, tables, strutils]
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

proc hostRotateChannel(channel: ChannelHandle): ChannelHandle =
  result = channel
  inc result.id
  result.label.add("*")

proc hostRouteChannel(channel: ChannelHandle,
                      message: string): ChannelHandle =
  result = channel
  result.label.add(":" & message)

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

eponymBlock:
  postulate(Int, Univ)
  postulate(Nat, Univ)
  postulate(hostPlusSeven, Int -> Int)
  bindPostulate(hostPlusSeven, hostStepNim)
  proc generatedCheckedRole(value: Int): Int = hostPlusSeven(value)
  proc generatedAdd(left: Int, right: Int): Int = addInt(left, right)
  proc generatedNatId(value: Nat): Nat = value

eponymBlock:
  postulate(Int, Univ)
  postulate(hostFailure, Int -> Int)
  bindPostulate(hostFailure, hostFailureNim)
  proc generatedFailureRole(value: Int): Int = hostFailure(value)

eponymBlock:
  postulate(Channel, Univ)
  postulate(Message, Univ)
  runtimeType(Channel, ChannelHandle)
  runtimeType(Message, string)
  postulate(rotateChannel, Channel -> Channel)
  bindPostulate(rotateChannel, hostRotateChannel, Channel)
  postulate(routeChannel, Channel -> Message -> Channel)
  bindPostulate(routeChannel, hostRouteChannel, Channel, Message, Channel)
  proc generatedRotateRole(channel: Channel): Channel =
    rotateChannel(channel)
  proc generatedRouteRole(channel: Channel, message: Message): Channel =
    routeChannel(channel, message)

static:
  doAssert compiles(generatedCheckedRole(35))
  doAssert compiles(generatedAdd(20, 22))
  doAssert not compiles(generatedAdd(42))
  doAssert not compiles(generatedAdd("20", 22))
  doAssert compiles(generatedNatId(17))
  doAssert compiles(generatedRotateRole(ChannelHandle(id: 1)))
  doAssert not compiles(generatedRotateRole("not a channel"))
  doAssert compiles(generatedRouteRole(ChannelHandle(id: 1), "hello"))
  doAssert not compiles(generatedRouteRole("not a channel", "hello"))

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
    generatedNatId(17) == 17
  let generatedOpaqueWrapperWorks = generatedRouteRole(
    ChannelHandle(id: 17, label: "socket"), "generated").label ==
      "socket:generated"
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
