## Property test for the checked session roles and their opaque Nim backend.

import falsify
import ../examples/embedded/session_runtime_bindings

when isMainModule:
  var rng = initRng(20261018'u64)
  var malformedFramesRejected = true
  for frame in [newSeq[byte](), @[0x80'u8], @[0'u8, 0'u8],
                @[0x80'u8, 0x80'u8, 0x80'u8, 0x80'u8, 0x80'u8,
                  0x80'u8, 0x80'u8, 0x80'u8, 0x80'u8, 0'u8]]:
    try:
      discard decodeNatMessage(frame)
      malformedFramesRejected = false
    except ValueError:
      discard
  var negativeNatRejected = false
  try:
    discard encodeNatMessage(-1)
  except ValueError:
    negativeNatRejected = true
  let codecRoundTrips = forAll("Nat message codec round trips",
    rng, 200,
    proc(r: var Rng): int = r.genInt(0, 1000000),
    proc(value: int): bool =
      decodeNatMessage(encodeNatMessage(value)) == value,
    shrinkInt)
  let roleRoundTrips = forAll("checked session send/receive role pair",
    rng, 200,
    proc(r: var Rng): int = r.genInt(0, 10000),
    proc(message: int): bool =
      let channel = newChannelHandle()
      discard checkedSender(message, channel)
      checkedReceiver(channel) == message and channel.channelIsEmpty,
    shrinkInt)
  if not malformedFramesRejected or not negativeNatRejected or
      not codecRoundTrips or not roleRoundTrips:
    quit(1)
  echo "test_session_runtime_bindings: checked role property passed"
