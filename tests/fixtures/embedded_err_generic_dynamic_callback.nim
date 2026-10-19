import ../../src/eponym/eponym_mac
import ../../src/eponym/eponym_embed
import ../../src/eponym/eponym_init
import ../../src/eponym/elab

eponymBlock:
  postulate(Int, Univ)
  proc applyGenericCallback[callback: Int -> Int](value: Int): Int =
    callback(value)
  runtimeValue(applyGenericCallback)

proc badDynamicCall(): int =
  applyGenericCallbackDynamic(
    proc(value: bool): bool = not value, 7)
