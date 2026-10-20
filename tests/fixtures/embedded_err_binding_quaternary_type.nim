import eponym_mac
import eponym_embed

proc hostFour(a, b, c, d: int): int = a + b + c + d

eponymBlock:
  postulate(A, Univ)
  postulate(B, Univ)
  postulate(C, Univ)
  postulate(D, Univ)
  postulate(E, Univ)
  postulate(F, Univ)
  postulate(hostFourPostulate, A -> B -> C -> D -> E)
  bindPostulate(hostFourPostulate, hostFour, A, B, C, F, E)
  proc checkedRole(a: A, b: B, c: C, d: D): E =
    hostFourPostulate(a, b, c, d)
