## A checked session role calling opaque channel operations backed by Nim.
## Session-state indices are checked by Eponym and erase at runtime; each
## indexed Chan value maps to the same trusted Nim ChannelHandle.

import eponym_mac
import eponym_embed

type ChannelHandle* = ref object
  messages: seq[seq[byte]]

proc newChannelHandle*(): ChannelHandle =
  ChannelHandle(messages: @[])

proc channelIsEmpty*(channel: ChannelHandle): bool =
  channel.messages.len == 0

proc encodeNatMessage*(value: int): seq[byte] =
  ## A compact unsigned LEB128 payload codec used by this demo's Nim adapter.
  if value < 0:
    raise newException(ValueError, "cannot encode a negative Nat")
  var remaining = uint64(value)
  while remaining >= 0x80'u64:
    result.add(byte((remaining and 0x7f'u64) or 0x80'u64))
    remaining = remaining shr 7
  result.add(byte(remaining))

proc decodeNatMessage*(frame: openArray[byte]): int =
  ## Decode one canonical unsigned LEB128 payload; reject truncation,
  ## overlong encodings, trailing bytes, and values outside Nim's int range.
  var decoded = 0'u64
  var shift = 0
  for i, item in frame:
    if i >= 9:
      raise newException(ValueError, "Nat frame is too large")
    let payload = uint64(item and 0x7f'u8)
    decoded = decoded or (payload shl shift)
    if (item and 0x80'u8) == 0:
      if i != frame.high:
        raise newException(ValueError, "Nat frame has trailing bytes")
      if i > 0 and payload == 0:
        raise newException(ValueError, "Nat frame is not canonically encoded")
      if decoded > uint64(high(int)):
        raise newException(ValueError, "Nat frame exceeds Nim int range")
      return int(decoded)
    shift += 7
  raise newException(ValueError, "truncated Nat frame")

proc sendNatImpl(value: int, channel: ChannelHandle): ChannelHandle =
  channel.messages.add(encodeNatMessage(value))
  channel

proc recvNatImpl(channel: ChannelHandle): int =
  doAssert channel.messages.len > 0, "receive from an empty channel"
  result = decodeNatMessage(channel.messages[0])
  channel.messages.delete(0)

eponymBlock:
  import "../../lib/nat.ep"

  data(Session, Univ):
    proc sendS(A: Univ, s: Session): Session
    proc recvS(A: Univ, s: Session): Session
    proc endS(): Session

  # Chan is abstract at runtime; Eponym still checks its session index.
  postulate(Chan, Session -> Univ)
  runtimeType(Chan, ChannelHandle)

  postulate(sendNat,
    Pi(value: Nat,
       ch {.linear.}: Chan[sendS[Nat](endS())],
       Chan(endS())))
  postulate(recvNat,
    Pi(ch {.linear.}: Chan[recvS[Nat](endS())], Nat))
  bindPostulate(sendNat, sendNatImpl, Nat, Chan, Chan)
  bindPostulate(recvNat, recvNatImpl, Chan, Nat)

  proc checkedSender(value: Nat,
                     ch {.linear.}: Chan[sendS[Nat](endS())]): Chan[endS()] =
    sendNat(value, ch)

  proc checkedReceiver(ch {.linear.}: Chan[recvS[Nat](endS())]): Nat =
    recvNat(ch)

when isMainModule:
  let channel = ChannelHandle(messages: @[])
  discard checkedSender(42, channel)
  let received = checkedReceiver(channel)
  doAssert received == 42
  doAssert channel.messages.len == 0
  echo "session_runtime_bindings: checked roles sent and received 42"
