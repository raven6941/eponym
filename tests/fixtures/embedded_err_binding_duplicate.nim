import eponym_mac
import eponym_embed

proc hostStep(value: int): int = value + 1

eponymBlock:
  postulate(Int, Univ)
  postulate(hostStepPostulate, Int -> Int)
  bindPostulate(hostStepPostulate, hostStep)
  bindPostulate(hostStepPostulate, hostStep)
  proc checkedRole(value: Int): Int = hostStepPostulate(value)
