import ../../src/eponym/eponym_mac

proc hostInvokeUnary(callback: proc(value: int): int {.closure.}): int =
  callback(1)

eponymBlock:
  postulate(Int, Univ)
  postulate(invokeNullary,
    Pi(callback: proc(): Int {.closure.}, Int))
  bindPostulate(invokeNullary, hostInvokeUnary,
    proc(value: Int): Int {.closure.}, Int)
  proc badRole(callback: proc(): Int {.closure.}): Int =
    invokeNullary(callback)
