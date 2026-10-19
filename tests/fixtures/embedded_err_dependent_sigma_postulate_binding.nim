import eponym_mac

type ChannelHandle = object
  id: int

proc hostDependentPair(channel: ChannelHandle): tuple[length: int,
    values: seq[int]] =
  (channel.id, newSeq[int](channel.id))

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  postulate(Channel, Univ)
  postulate(makeDependentPair,
    Channel -> Sig(length: Nat, Vec[Nat, length]))
  runtimeType(Channel, ChannelHandle)
  bindPostulatePair(makeDependentPair, hostDependentPair,
    Channel, Nat, Vec)
  proc useDependentPair(channel: Channel):
      Sig(length: Nat, Vec[Nat, length]) = makeDependentPair(channel)
