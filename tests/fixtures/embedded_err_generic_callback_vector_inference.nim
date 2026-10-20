import eponym_mac
import eponym_embed
import eponym_init
import elab

type ChannelHandle = object
  id: int

eponymBlock:
  import "../../lib/vec.ep"
  runtimeVector(Vec)
  proc mappedCallback[A: Univ](
      callback: proc(value: A): A {.closure.}, values: Vec[A, 2]):
      proc(value: A): A {.closure.} = callback
  runtimeValue(mappedCallback)

discard mappedCallback(proc(value: bool): bool = not value,
  @[ChannelHandle(id: 1), ChannelHandle(id: 2)])
