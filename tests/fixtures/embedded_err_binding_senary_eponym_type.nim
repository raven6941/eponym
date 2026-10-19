import eponym_mac
import eponym_embed

proc hostSumSix(a, b, c, d, e, f: int): int = a + b + c + d + e + f

eponymBlock:
  postulate(Int, Univ)
  postulate(Nat, Univ)
  postulate(sumSix, Int -> Int -> Int -> Int -> Int -> Int -> Int)
  bindPostulate(sumSix, hostSumSix, Int, Int, Int, Int, Nat, Int, Int)
  proc generatedSumSix(a, b, c, d, e, f: Int): Int =
    sumSix(a, b, c, d, e, f)

discard generatedSumSix(1, 2, 3, 4, 5, 6)
