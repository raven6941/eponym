import ../../src/eponym/eponym_mac

type NimBoolCallback = proc(value: bool): bool {.closure.}

proc hostWrongCallback(callback: NimBoolCallback,
                       value: int): int = value

eponymBlock:
  import "runtime_imported_callback.ep"
  import "../../lib/bool.ep"
  bindPostulate(applyCallback, hostWrongCallback,
    proc(value: Bool): Bool {.closure.}, Int, Int)
  proc badRole(callback: proc(value: Int): Int {.closure.},
               value: Int): Int = applyCallback(callback, value)
