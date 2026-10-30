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
#   - Runtime checking stays at the eponym API boundary: the Nim backend
#     asserts each phase transition as defence in depth, but cannot detect
#     Nim-side aliasing of a handle (see the limitation above).
#   - Repo nit, not language friction: session_types.nim imports
#     eponym_embed unused and warns; this example imports eponym_embed
#     and eponym_init for runtime bindings and remains warning-clean.

import eponym_mac
import eponym_embed
import eponym_init

type
  SockPhaseB = enum unconnB, connB, closedB

  SockHandle = ref object
    phase: SockPhaseB
    incoming: int
    lastReceived: int
    lastSent: int
    connects: int
    sends: int
    receives: int
    closes: int

proc newSockHandle(incoming = 41): SockHandle =
  SockHandle(phase: unconnB, incoming: incoming)

proc hostConnectH(sock: SockHandle): SockHandle =
  doAssert sock.phase == unconnB, "connectH requires an unconnected socket"
  sock.phase = connB
  inc sock.connects
  sock

proc hostSendH(payload: int, sock: SockHandle): SockHandle =
  doAssert sock.phase == connB, "sendH requires a connected socket"
  sock.lastSent = payload
  inc sock.sends
  sock

proc hostRecvH(sock: SockHandle): tuple[value: int, sock: SockHandle] =
  doAssert sock.phase == connB, "recvH requires a connected socket"
  sock.lastReceived = sock.incoming
  inc sock.receives
  (sock.incoming, sock)

proc hostCloseH(sock: SockHandle): SockHandle =
  doAssert sock.phase == connB, "closeH requires a connected socket"
  sock.phase = closedB
  inc sock.closes
  sock

eponymBlock:
  import "../../lib/typestate.ep"

  runtimeType(Sock, SockHandle)
  bindPostulate(connectH, hostConnectH, Sock, Sock)
  bindPostulate(sendH, hostSendH, Nat, Sock, Sock)
  bindPostulatePair(recvH, hostRecvH, Sock, Nat, Sock)
  bindPostulate(closeH, hostCloseH, Sock, Sock)

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
# Plain Nim from here: the clients above were checked at compile time and
# bound to a phase-checking mock backend for executable happy paths.

proc main() =
  echo "typestate_handles: phase-indexed sockets, embedded (Issue #481)."
  let session = newSockHandle()
  discard socketSession(session)
  doAssert session.phase == closedB
  doAssert (session.connects, session.sends, session.receives,
    session.closes) == (1, 1, 1, 1)
  doAssert session.lastReceived == 41, "socketSession must receive its payload"
  doAssert session.lastSent == 0
  echo "  socketSession trace connect/send/recv/close: ", session.connects,
    "/", session.sends, "/", session.receives, "/", session.closes

  let echoSock = newSockHandle(incoming = 73)
  discard echoRoundTrip(echoSock)
  doAssert echoSock.phase == closedB
  doAssert (echoSock.connects, echoSock.sends, echoSock.receives,
    echoSock.closes) == (1, 1, 1, 1)
  doAssert echoSock.lastReceived == 73
  doAssert echoSock.lastSent == 73, "echoRoundTrip must send the received value"
  echo "  echoRoundTrip echoed: ", echoSock.lastSent

  let twice = newSockHandle()
  discard sendTwice(twice)
  doAssert twice.phase == closedB
  doAssert (twice.connects, twice.sends, twice.receives,
    twice.closes) == (1, 2, 0, 1)
  doAssert twice.lastSent == 1, "sendTwice must finish with suc(zero())"
  echo "  sendTwice trace connect/send/recv/close: ", twice.connects,
    "/", twice.sends, "/", twice.receives, "/", twice.closes
  echo "  misuse (send-before-connect, use-after-close, double-close,"
  echo "  dropped handle) is rejected at elaboration; see examples/ep/28*.ep."

when isMainModule:
  main()
