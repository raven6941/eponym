# Session-typed channels, embedded (Issue #28).
#
# The protocol is stated once as indexed Eponym types inside an eponymBlock;
# the client is written in ordinary-looking Nim. Protocol violations are
# compile-time errors: the block is elaborated when this module compiles.
#
# New eponymBlock surface used here (Issue #28 / #64):
# - `ch {.linear.}` params become `(1 ch : ...)` binders; the elaborator
#   rejects using a linear variable zero or 2+ times.
# - `Pi(x: A, y {.linear.}: B, C)` call syntax for dependent Pi types
#   (Nim parses this as nnkObjConstr; eponym_mac handles both shapes).
# - `Sig(x: A, B)` / `Sig(A, B)` for dependent pairs.
#
# The operations are postulates (mock socket ops); a real library would
# bind them to socket code. Linearity is enforced at use sites (clients).

import eponym_mac
import eponym_embed

eponymBlock:
  # Prelude import (issue #131): Nat, zero, suc, add, mul from lib/nat.ep
  # (was a per-file data(Nat, ...) redefinition before #131).
  import "../../lib/nat.ep"

  # Session protocol descriptions: what comes next on the channel.
  data(Session, Univ):
    proc sendS(A: Univ, s: Session): Session
    proc recvS(A: Univ, s: Session): Session
    proc endS(): Session

  # Channel indexed by current session state.
  data(Chan, Session -> Univ):
    proc mkChan(s: Session): Chan[s]

  # Operations as postulates (mock implementations). The types enforce
  # the protocol; the linear binders enforce single use of the channel.
  postulate(sendNat, Pi(x: Nat, ch {.linear.}: Chan[sendS[Nat](endS())], Chan[endS()]))
  postulate(recvNat, Pi(ch {.linear.}: Chan[recvS[Nat](endS())], Sig(x: Nat, Chan[endS()])))
  postulate(closeOp, Pi(ch {.linear.}: Chan[endS()], Nat))

  # The protocol, stated once as a type: send a Nat, then done.
  proc proto(): Session =
    sendS[Nat](endS())

  # Correct client: ordinary-looking Nim. The elaborator checks that `ch`
  # starts as `Chan[sendS[Nat](endS())]` and that the body delivers the
  # declared `Chan[endS()]`.
  proc client(ch {.linear.}: Chan[sendS[Nat](endS())]): Chan[endS()] =
    sendNat(zero(), ch)

  # Server side of the dual protocol: receive a Nat, then close.
  # `recvNat` returns a pair; `snd(p)` is the continued channel.
  proc server(ch {.linear.}: Chan[recvS[Nat](endS())]): Nat =
    let p = recvNat(ch)
    closeOp(snd(p))

# --- Normal Nim program ------------------------------------------------
# Plain Nim from here: IO, config, orchestration. The session-typed
# `client`/`server` above were checked at compile time; violations do not
# compile (each is a negative test under examples/ep/, run by
# tests/run_examples.nim):
#   - recv before send: 15c-session-types-neg.ep
#   - send on closed channel: 15d-session-types-neg.ep
#   - double use of the channel: 15b-session-types-neg.ep
#     ("linear variable 'ch' used 2 times (expected exactly once)")
#   - dropped (unused) channel: "linear variable 'ch' not used"

proc main() =
  echo "session_types: protocol + client elaborated at compile time."
  echo "client : Pi(1 ch: Chan (sendS Nat endS), Chan endS)  -- checks out."

when isMainModule:
  main()
