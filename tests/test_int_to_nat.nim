## Explicit conversion from primitive Int to Nat.

import falsify
import eponym_mac
import eponym_embed

eponymRuntimeBridgeTestBlock:
  import "../lib/int_to_nat.ep"
  bindPostulate(intToNat, intToNatHost, Int, Nat)

  proc intToNatOnly(value: Int): Nat = intToNat(value)
  proc intRoundTrip(value: Int): Int = natToInt(intToNat(value))
  proc natRoundTrip(value: Nat): Nat = intToNat(natToInt(value))

  runtimeValue(intToNatOnly)
  runtimeValue(intRoundTrip)
  runtimeValue(natRoundTrip)

eponymRuntimeBridgeTestBlock:
  requireCompiled()
  import "../lib/int_to_nat.ep"
  runtimeType(Int, int)
  runtimeType(Nat, int)
  bindPostulate(intToNat, intToNatHost, Int, Nat)

  proc compiledIntToNat(value: Int): Nat = intToNat(value)

eponymRuntimeBridgeTestBlock:
  import "../lib/nat.ep"
  runtimeType(Nat, int)
  proc entryP(n: Nat): Nat = add(n, n)

proc rejectsNegativeConversion(convert: proc(value: int): int): bool =
  try:
    discard convert(-1)
  except ValueError as error:
    return error.msg == "cannot convert negative Int to Nat"
  false

when isMainModule:
  var rng = initRng(20261022'u64)
  let valuePathAgrees = forAll("Int -> Nat Value path and round trips",
    rng, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(value: int): bool =
      let converted = intToNatOnlyRuntimeValue(value)
      let intRoundTripResult = intRoundTripRuntimeValue(value)
      let natRoundTripResult = natRoundTripRuntimeValue(value)
      intToNatOnly(value) == value and
      intRoundTrip(value) == value and
      natRoundTrip(value) == value and
      valueToNat(converted.value, converted.globals) == value and
      valueToInt(intRoundTripResult.value) == value and
      valueToNat(natRoundTripResult.value, natRoundTripResult.globals) == value,
    shrinkInt)

  let reprPathAgrees = forAll("Int -> Nat requireCompiled path agrees with Value path",
    rng, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(value: int): bool =
      let valueResult = intToNatOnlyRuntimeValue(value)
      compiledIntToNat(value) == value and
      valueToNat(valueResult.value, valueResult.globals) == value,
    shrinkInt)

  let intValueRejectsNegative = rejectsNegativeConversion(intToNatHost)
  var valuePathRejectsNegative = false
  try:
    discard intToNatOnlyRuntimeValue(-1)
  except ValueError as error:
    valuePathRejectsNegative =
      error.msg == "cannot convert negative Int to Nat"

  var typedWrapperRejectsNegative = false
  try:
    discard intToNatOnly(-1)
  except ValueError as error:
    typedWrapperRejectsNegative =
      error.msg == "cannot convert negative Int to Nat"

  var reprPathRejectsNegative = false
  try:
    discard compiledIntToNat(-1)
  except ValueError as error:
    reprPathRejectsNegative =
      error.msg == "cannot convert negative Int to Nat"

  if not valuePathAgrees or not reprPathAgrees or
      not intValueRejectsNegative or not valuePathRejectsNegative or
      not typedWrapperRejectsNegative or not reprPathRejectsNegative:
    quit(1)
  doAssert entryP(21) == 42,
    "typed runtime wrapper should accept and return Nat values"
  echo "test_int_to_nat: Value and representation properties passed"
