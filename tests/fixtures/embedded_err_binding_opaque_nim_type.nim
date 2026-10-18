import eponym_mac

type ChannelHandle = object
  id: int

proc wrongRoute(channel: int, message: string): int = channel + message.len

eponymBlock:
  postulate(Channel, Univ)
  postulate(Message, Univ)
  runtimeType(Channel, ChannelHandle)
  runtimeType(Message, string)
  postulate(routeChannel, Channel -> Message -> Channel)
  bindPostulate(routeChannel, wrongRoute, Channel, Message, Channel)
  proc checkedRole(channel: Channel, message: Message): Channel =
    routeChannel(channel, message)
