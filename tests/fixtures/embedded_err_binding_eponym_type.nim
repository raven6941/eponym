import eponym_mac
import eponym_embed

proc hostStep(value: int): int = value + 1

eponymBlock:
  postulate(Int, Univ)
  postulate(Nat, Univ)
  postulate(hostStepPostulate, Nat -> Nat)
  bindPostulate(hostStepPostulate, hostStep)
  proc checkedRole(value: Nat): Nat = hostStepPostulate(value)
