import eponym_mac
import eponym_embed

type ChannelHandle = object
  id: int

proc wrongFive(channel: ChannelHandle, message: string, requestId,
               phase, sample: int): int = channel.id + message.len +
  requestId + phase + sample

eponymBlock:
  postulate(Channel, Univ)
  postulate(Message, Univ)
  postulate(RequestId, Univ)
  postulate(Phase, Univ)
  postulate(Sample, Univ)
  runtimeType(Channel, ChannelHandle)
  runtimeType(Message, string)
  runtimeType(RequestId, int)
  runtimeType(Phase, int)
  runtimeType(Sample, int)
  postulate(routeFive,
    Channel -> Message -> RequestId -> Phase -> Sample -> Channel)
  bindPostulate(routeFive, wrongFive,
    Channel, Message, RequestId, Phase, Sample, Channel)
  proc callFive(channel: Channel, message: Message, requestId: RequestId,
                phase: Phase, sample: Sample): Channel =
    routeFive(channel, message, requestId, phase, sample)
