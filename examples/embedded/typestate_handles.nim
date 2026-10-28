# Phase-indexed handles / typestate, embedded (Issue #481).
#
# A socket's phase (unconnected -> connected -> closed) is carried in its
# type: `Sock[unconnP()]`, `Sock[connP()]`, `Sock[closedP()]`. Every
# operation's type states the phase it requires and the phase it delivers,
# so misuse is a compile-time error: the block is elaborated when this
# module compiles. The reusable library lives in lib/typestate.ep; this
# file is the example-specific use: clients over that library.
#
# The operations are postulates (mock socket ops); a real library would
# bind them to socket code. Linearity is enforced at use sites (clients):
# each handle binder is `{.linear.}`, so a handle is used exactly once
# along a path — no silent drops, no double use.
#
# Honest boundary (must be stated, not overclaimed): Eponym checks phase
# ordering inside checked terms. It cannot see Nim-side aliasing: two Nim
# references to the same socket are invisible to it (see
# docs/known-limitations.md, "Static checks do not manage Nim resources").
# This example demonstrates checking at the eponym API boundary; it does
# not claim end-to-end resource management.
#
# Misuse cases are negative tests under examples/ep/, run by
# tests/run_examples.nim:
#   - send before connect: 28a-typestate-send-before-connect-neg.ep
#   - use after close:     28b-typestate-use-after-close-neg.ep
#   - double close:        28c-typestate-double-close-neg.ep
#   - dropped handle:      28d-typestate-drop-neg.ep
#
# Watchlist (part of the deliverable; observations from building this):
#   - No new language friction: the phase-indexed pattern fell directly
#     out of the session-types machinery (indexed data + linear binders).
#     The embedded example compiled first try once lib/typestate.ep was
#     written, and it imports that lib file rather than redefining the
#     types (session_types.nim, by contrast, redefines its own).
#   - Error quality is good: phase mismatches name the distinct
#     constructors (e.g. unconnP vs connP), so the programmer sees which
#     transition was wrong, not just "type mismatch".
#   - Structural split, same as session types: misuse cases cannot live
#     in the embedded file itself (they would fail compilation), so the
#     example necessarily splits into embedded positives + .ep negatives.
#     A newcomer may find that split surprising; it is documented here.
#   - Mock-postulate limit, same as session_types: the happy path has no
#     runtime behaviour to assert. A runnable socket backend is a separate
#     step and is not claimed here.
#   - Repo nit, not language friction: session_types.nim imports
#     eponym_embed unused and warns; this file imports only eponym_mac
#     and is warning-clean. Left untouched to keep this change focused.

import eponym_mac

eponymBlock:
  import "../../lib/typestate.ep"

  # Happy path: connect, send a Nat, receive one, close. Each step's
  # result feeds the next; the index on Sock advances with the lifecycle.
  proc socketSession(s {.linear.}: Sock[unconnP()]): Sock[closedP()] =
    let c = connectH(s)
    let c2 = sendH(zero(), c)
    let p = recvH(c2)
    closeH(snd(p))

  # Round trip: receive a value, send it back, close. Exercises both
  # projections of the Sig pair returned by recvH.
  proc echoRoundTrip(s {.linear.}: Sock[unconnP()]): Sock[closedP()] =
    let c = connectH(s)
    let p = recvH(c)
    let c2 = sendH(fst(p), snd(p))
    closeH(c2)

  # Chained sends: the connected handle threads through two sends
  # before closing, with no intermediate let-bindings.
  proc sendTwice(s {.linear.}: Sock[unconnP()]): Sock[closedP()] =
    closeH(sendH(suc(zero()), sendH(zero(), connectH(s))))

# --- Normal Nim program ------------------------------------------------
# Plain Nim from here: the clients above were checked at compile time.
# The operations are mock postulates, so there is no socket to run
# against; like examples/embedded/session_types.nim, this module's runtime
# behaviour is just a description of what elaborated.

proc main() =
  echo "typestate_handles: phase-indexed sockets, embedded (Issue #481)."
  echo "  socketSession : Sock unconnP -> Sock closedP (connect/send/recv/close)"
  echo "  echoRoundTrip : Sock unconnP -> Sock closedP (connect/recv/send/close)"
  echo "  sendTwice     : Sock unconnP -> Sock closedP (connect/send/send/close)"
  echo "  misuse (send-before-connect, use-after-close, double-close,"
  echo "  dropped handle) is rejected at elaboration; see examples/ep/28*.ep."

when isMainModule:
  main()
