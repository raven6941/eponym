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
# The operations are postulates (mock backend), exactly as in
# paxos_session.nim: the types enforce the borrow discipline, and the
# normal-Nim driver below binds the same op sequence to a real buffer —
# the Wu & Xi "typed API over untrusted backend" architecture. The
# Eponym-checked client is the spec; the driver is the trusted backend
# that upholds it (in particular: it never creates a second borrow).

import ett_mac
import ett_embed

ettBlock:
  # Prelude import (issue #131): Nat, zero, suc, add, mul from lib/nat.ep
  # (was a per-file data(Nat, ...) redefinition before #131).
  import "../../lib/nat.ep"

  postulate(Res, Univ)
  postulate(Borrow, Univ)

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

  # Client: read the head cell, write back its successor, read again,
  # finish the borrow with the new value. `r` appears in term position
  # exactly once (as withBorrow's argument); every borrow exactly once.
  proc borrowClient(r {.linear.}: Res): Nat =
    withBorrow(r, lam(b, Borrow,
      readB(b, lam(v, Nat, lam(b2, Borrow,
        writeB(b2, suc(v), lam(b3, Borrow,
          readB(b3, lam(v2, Nat, lam(b4, Borrow,
            endB(b4, v2)))))))))))

# --- Normal Nim program: real buffer backend + driver ----------------------
# Mirrors borrowClient op-for-op against a real buffer:
#   allocRes -> withBorrow -> readB -> writeB(suc) -> readB -> endB.
# The backend upholds the contract the types assume: exactly one borrow
# exists at a time, and the scope brackets its lifetime.

type Buffer = object
  cells: seq[int]

proc allocBuffer(n: int): Buffer =
  Buffer(cells: newSeq[int](n))

proc runBorrowDemo(): int =
  var buf = allocBuffer(4)        # allocRes 4
  # withBorrow buf: exclusive scope begins — no other handle to buf exists.
  var cell = buf.cells[0]         # readB b -> v
  cell += 1                       # suc v
  buf.cells[0] = cell             # writeB b v
  let v2 = buf.cells[0]           # readB b -> v2
  # endB b v2 -> v2; scope ends, the single borrow is gone (linear).
  v2

proc main() =
  echo "qtt_borrow: QTT borrow checking, embedded (Issue #122)."
  echo "  borrowClient threads 4 linear borrows through read/write/end;"
  echo "  double-use, owner-use-while-borrowed, and dropped borrows are"
  echo "  compile-time errors (examples/ep/21a,21b,21c-*-neg.ep)."
  let v = runBorrowDemo()
  echo "  backend run on a 4-cell buffer (head 0 -> bump -> read): ", v
  assert v == 1, "borrow protocol violated on the backend"

when isMainModule:
  main()
