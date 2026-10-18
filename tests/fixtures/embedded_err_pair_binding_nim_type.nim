import eponym_mac

type ChannelHandle = object
  id: int

proc badSplitChannel(channel: ChannelHandle):
    tuple[count: string, remainder: ChannelHandle] =
  ("wrong", channel)

eponymBlock:
  import "../../lib/nat.ep"
  postulate(Channel, Univ)
  postulate(splitChannel, Channel -> Sig(Nat, Channel))
  runtimeType(Channel, ChannelHandle)
  bindPostulatePair(splitChannel, badSplitChannel, Channel, Nat, Channel)
  proc generatedSplitChannel(channel: Channel): Sig(Nat, Channel) =
    splitChannel(channel)
