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
# The operations are postulates. Their callback-based clients are checked
# at compile time and marked `compileTimeOnly`: the previous Nim buffer
# backend invoked Eponym continuations through the Value interpreter, which
# strict `eponymBlock` runtime code now forbids. A representation-compiled
# closure adapter is needed before those clients can run against Nim again.

import eponym_mac

eponymBlock:
  # Prelude import (issue #131): Nat, zero, suc, add, mul from lib/nat.ep
  # (was a per-file data(Nat, ...) redefinition before #131).
  import "../../lib/nat.ep"

  postulate(Res, Univ)
  postulate(Borrow, Univ)
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


  # Client: read the head cell, write back its successor, read again,
  # finish the borrow with the new value. `r` appears in term position
  # exactly once (as withBorrow's argument); every borrow exactly once.
  proc borrowClient(r {.linear.}: Res): Nat =
    withBorrow(r, lam(b: Borrow) => readB(b, lam(v: Nat) => lam(b2: Borrow) => writeB(b2, suc(v), lam(b3: Borrow) => readB(b3, lam(v2: Nat) => lam(b4: Borrow) => endB(b4, v2)))))

  proc failingBorrowClient(r {.linear.}: Res): Nat =
    withBorrow(r, lam(b: Borrow) => failBorrow(b))

  # The clients are checked at compile time. Their raw callback adapters
  # previously invoked the Value interpreter and therefore are excluded
  # from the strict runtime closure until compiled closure adapters exist.
  compileTimeOnly(borrowClient)
  compileTimeOnly(failingBorrowClient)

proc main() =
  echo "qtt_borrow: QTT borrow checking, embedded (Issue #122)."
  echo "  borrowClient threads 4 linear borrows through read/write/end;"
  echo "  double-use, owner-use-while-borrowed, and dropped borrows are"
  echo "  compile-time errors (examples/ep/21a,21b,21c-*-neg.ep)."
  echo "  runtime callback adapter is compile-time-only until it can use"
  echo "  representation-compiled closures without Value interpretation."

when isMainModule:
  main()
