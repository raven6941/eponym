import eponym_mac
import eponym_embed
import eponym_init
import elab

type ChannelHandle = object
  id: int

eponymBlock:
  postulate(Channel, Univ)
  runtimeType(Channel, ChannelHandle)
  proc mappedCallback[A: Univ](
      callback: proc(value: A): A {.closure.}, value: A): A =
    callback(value)
  runtimeValue(mappedCallback)

discard mappedCallback(proc(value: bool): bool = not value,
  ChannelHandle(id: 1))
