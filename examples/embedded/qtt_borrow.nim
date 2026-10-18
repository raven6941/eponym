# QTT borrow checking, embedded (Issue #122).
#
# The residual idea from #101: "QTT borrow checking within a specific
# eponym library pathway that warrants being careful ... followed by a use
# of this pathway from normal nim; opt-in linearity etc checking".
#
# The pathway: a unique borrow of a heap buffer. `withBorrow r k` hands
# `k` the *only* borrow of the buffer `r`; `r` is consumed (linear), so the
# owner cannot touch the buffer while the borrow is live — the borrow
# checker's exclusive-access rule. The borrow is threaded through
# read/write in continuation-passing style so every borrow is a lambda
# binder, and the in-judgment quantity enforcement (Issue #66) fires at
# every step:
# - double use of a borrow: rejected (examples/ep/21a-borrow-double-use-neg.ep)
# - owner used while borrowed: rejected (21b-borrow-owner-use-neg.ep)
# - borrow dropped: rejected (21c-borrow-drop-neg.ep)
# - borrow escaping the scope: impossible by construction — `k` returns
#   `Nat`, so there is no channel by which the borrow could outlive it.
#
# Why this pathway warrants checking (Aaron's bar: enough surface area
# that a programmer could reasonably mess up without guardrails): the
# client below threads four borrows through six operations; forgetting one
# `readB` continuation, reusing a borrow after `writeB`, or touching the
# buffer from outside the scope are all easy slips in an untyped API, and
# each is a compile-time error here.
#
# The operations are postulates implemented by a Nim buffer backend. The
# backend uses the explicit raw-Value adapter because it must invoke the
# checked Eponym continuations. Eponym checks the client and linear uses;
# Nim remains responsible for exclusivity, alias discipline, and lifetime.

import std/sequtils
import eponym_mac
import eponym_embed
import eponym_init
import elab

type
  Buffer* = ref object
    cells*: seq[int]
    borrowed: bool

  BorrowHandle = ref object
    buffer: Buffer
    active: bool

proc hostWithBorrow(args: seq[Value], globals: Globals): Value
proc hostReadB(args: seq[Value], globals: Globals): Value
proc hostWriteB(args: seq[Value], globals: Globals): Value
proc hostEndB(args: seq[Value], globals: Globals): Value
proc hostFailBorrow(args: seq[Value], globals: Globals): Value

eponymBlock:
  # Prelude import (issue #131): Nat, zero, suc, add, mul from lib/nat.ep
  # (was a per-file data(Nat, ...) redefinition before #131).
  import "../../lib/nat.ep"

  postulate(Res, Univ)
  postulate(Borrow, Univ)
  runtimeType(Res, Buffer)

  postulate(allocRes, Pi(n: Nat, Res))

  # Scoped unique borrow (bracket): k gets the borrow and computes a Nat;
  # when k finishes, the backend releases the resource. The linear `r` is
  # fully consumed, so a well-typed client cannot leak it.
  postulate(withBorrow,
    Pi(r {.linear.}: Res,
       k: Pi(b {.linear.}: Borrow, Nat),
       Nat))

  # readB b k: read the head cell, continue with value + re-bound borrow.
  # writeB b v k: write v, continue with the re-bound borrow.
  # endB b v: finish the borrow, yielding v.
  # CPS keeps every borrow a lambda binder, so linearity is checked at
  # every step (unannotated lam binders inherit the quantity from the
  # expected Pi — the Idris 2 behaviour).
  postulate(readB,
    Pi(b {.linear.}: Borrow,
       k: Pi(v: Nat, b2 {.linear.}: Borrow, Nat),
       Nat))
  postulate(writeB,
    Pi(b {.linear.}: Borrow,
       v: Nat,
       k: Pi(b2 {.linear.}: Borrow, Nat),
       Nat))
  postulate(endB,
    Pi(b {.linear.}: Borrow, v: Nat, Nat))
  postulate(failBorrow, Borrow -> Nat)

  bindPostulateValue(withBorrow, hostWithBorrow)
  bindPostulateValue(readB, hostReadB)
  bindPostulateValue(writeB, hostWriteB)
  bindPostulateValue(endB, hostEndB)
  bindPostulateValue(failBorrow, hostFailBorrow)

  # Client: read the head cell, write back its successor, read again,
  # finish the borrow with the new value. `r` appears in term position
  # exactly once (as withBorrow's argument); every borrow exactly once.
  proc borrowClient(r {.linear.}: Res): Nat =
    withBorrow(r, lam(b, Borrow,
      readB(b, lam(v, Nat, lam(b2, Borrow,
        writeB(b2, suc(v), lam(b3, Borrow,
          readB(b3, lam(v2, Nat, lam(b4, Borrow,
            endB(b4, v2)))))))))))

  proc failingBorrowClient(r {.linear.}: Res): Nat =
    withBorrow(r, lam(b, Borrow, failBorrow(b)))

proc requireArgs(args: seq[Value], expected: int, operation: string) =
  if args.len != expected:
    raise newException(ValueError, operation & " expects " & $expected &
      " runtime arguments")

proc getBorrow(value: Value, operation: string): BorrowHandle =
  result = valueToHost[BorrowHandle](value)
  if result.isNil or not result.active or not result.buffer.borrowed:
    raise newException(ValueError, operation & " used an inactive borrow")

proc hostWithBorrow(args: seq[Value], globals: Globals): Value =
  requireArgs(args, 2, "withBorrow")
  let buffer = valueToHost[Buffer](args[0])
  if buffer.isNil or buffer.cells.len == 0 or buffer.cells.anyIt(it < 0):
    raise newException(ValueError,
      "withBorrow requires a nonempty buffer containing only Nat cells")
  if buffer.borrowed:
    raise newException(ValueError, "buffer already has an active borrow")
  buffer.borrowed = true
  let borrow = BorrowHandle(buffer: buffer, active: true)
  try:
    let callbackResult = callRuntimeValue(args[1], [toHostValue(borrow)])
    if borrow.active:
      raise newException(IOError,
        "withBorrow callback returned without ending the borrow")
    result = callbackResult
  finally:
    borrow.active = false
    buffer.borrowed = false

proc hostReadB(args: seq[Value], globals: Globals): Value =
  requireArgs(args, 2, "readB")
  let borrow = getBorrow(args[0], "readB")
  result = callRuntimeValue(args[1], [natToValue(borrow.buffer.cells[0]),
                                     toHostValue(borrow)])

proc hostWriteB(args: seq[Value], globals: Globals): Value =
  requireArgs(args, 3, "writeB")
  let borrow = getBorrow(args[0], "writeB")
  borrow.buffer.cells[0] = valueToNat(args[1], globals)
  result = callRuntimeValue(args[2], [toHostValue(borrow)])

proc hostEndB(args: seq[Value], globals: Globals): Value =
  requireArgs(args, 2, "endB")
  let borrow = getBorrow(args[0], "endB")
  borrow.active = false
  natToValue(valueToNat(args[1], globals))

proc hostFailBorrow(args: seq[Value], globals: Globals): Value =
  requireArgs(args, 1, "failBorrow")
  discard getBorrow(args[0], "failBorrow")
  raise newException(IOError, "simulated failure while borrowing")

proc runBorrowClient*(cells: seq[int]): tuple[value: int, cells: seq[int]] =
  if cells.len == 0 or cells.anyIt(it < 0):
    raise newException(ValueError, "borrowClient requires nonempty Nat cells")
  let buffer = Buffer(cells: cells)
  result.value = borrowClient(buffer)
  result.cells = buffer.cells

proc main() =
  echo "qtt_borrow: QTT borrow checking, embedded (Issue #122)."
  echo "  borrowClient threads 4 linear borrows through read/write/end;"
  echo "  double-use, owner-use-while-borrowed, and dropped borrows are"
  echo "  compile-time errors (examples/ep/21a,21b,21c-*-neg.ep)."
  let outcome = runBorrowClient(@[0, 7, 12, 99])
  echo "  checked client on a 4-cell buffer: ", outcome.cells,
    " -> result ", outcome.value
  assert outcome.value == 1 and outcome.cells == @[1, 7, 12, 99],
    "borrow protocol violated on the backend"

when isMainModule:
  main()
