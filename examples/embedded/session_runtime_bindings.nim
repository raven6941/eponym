## A checked session role calling opaque channel operations backed by Nim.
## Session-state indices are checked by Eponym and erase at runtime; each
## indexed Chan value maps to the same trusted Nim ChannelHandle.

import eponym_mac
import eponym_embed

type ChannelHandle* = ref object
  messages: seq[int]

proc newChannelHandle*(): ChannelHandle =
  ChannelHandle(messages: @[])

proc channelIsEmpty*(channel: ChannelHandle): bool =
  channel.messages.len == 0

proc sendNatImpl(value: int, channel: ChannelHandle): ChannelHandle =
  channel.messages.add(value)
  channel

proc recvNatImpl(channel: ChannelHandle): int =
  doAssert channel.messages.len > 0, "receive from an empty channel"
  result = channel.messages[0]
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
       ch {.linear.}: Chan(sendS(Nat, endS())),
       Chan(endS())))
  postulate(recvNat,
    Pi(ch {.linear.}: Chan(recvS(Nat, endS())), Nat))
  bindPostulate(sendNat, sendNatImpl, Nat, Chan, Chan)
  bindPostulate(recvNat, recvNatImpl, Chan, Nat)

  proc checkedSender(value: Nat,
                     ch {.linear.}: Chan(sendS(Nat, endS()))): Chan(endS()) =
    sendNat(value, ch)

  proc checkedReceiver(ch {.linear.}: Chan(recvS(Nat, endS()))): Nat =
    recvNat(ch)

when isMainModule:
  let channel = ChannelHandle(messages: @[])
  discard checkedSender(42, channel)
  let received = checkedReceiver(channel)
  doAssert received == 42
  doAssert channel.messages.len == 0
  echo "session_runtime_bindings: checked roles sent and received 42"
