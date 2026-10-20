import eponym_mac
import eponym_embed

proc wrongHost(value: string): string = value

eponymBlock:
  postulate(Int, Univ)
  postulate(hostStepPostulate, Int -> Int)
  bindPostulate(hostStepPostulate, wrongHost)
  proc checkedRole(value: Int): Int = hostStepPostulate(value)
