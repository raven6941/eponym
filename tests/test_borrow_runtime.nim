## Run the exact linear borrow client through its bound Nim buffer backend.
import falsify
import ../examples/embedded/qtt_borrow as borrow

when isMainModule:
  var rng = initRng(331097'u64)
  let cases = forAll(
    "checked borrow client updates only the borrowed head cell",
    rng, 300,
    proc(r: var Rng): int = r.genInt(0, 100000),
    proc(head: int): bool =
      let initial = @[head, head mod 97, head mod 53, head mod 29]
      let outcome = borrow.runBorrowClient(initial)
      outcome.value == head + 1 and
        outcome.cells == @[head + 1, initial[1], initial[2], initial[3]],
    shrinkInt)
  if not cases:
    quit(1)
  let recoveryBuffer = borrow.Buffer(cells: @[5, 8])
  var propagated = false
  try:
    discard borrow.failingBorrowClient(recoveryBuffer)
  except IOError as error:
    propagated = error.msg == "simulated failure while borrowing"
  doAssert propagated
  doAssert borrow.borrowClient(recoveryBuffer) == 6
  doAssert recoveryBuffer.cells == @[6, 8]
  echo "test_borrow_runtime: checked borrow client uses bound postulates"
