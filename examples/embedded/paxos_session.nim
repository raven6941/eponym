# Paxos, embedded (Issue #101).
#
# The Paxos prepare/promise/accept/accepted exchange as session types.
# The value discipline -- the proposer must accept *the value the acceptor
# promised*, not substitute its own -- is enforced by unforgeable promise
# tickets: `AcceptMsg` is postulated with *no constructors*, so the only
# `AcceptMsg v` a proposer can ever hold is the ticket returned by the
# acceptor's promise. `sendAccept` demands the ticket and requires the
# accept message to have type `AcceptMsg (fst pr)`; the only inhabitant
# available is `snd pr` itself. Substituting another value is not a
# runtime consensus violation here -- it is a compile-time type error.
#
# Why this protocol is worth checking (Aaron's bar: enough surface area that
# a programmer could reasonably mess up without guardrails):
# - two roles, four messages each, in a fixed interleaved order
#   (wrong order: 16a-paxos-wrong-order-neg.ep);
# - the accept message must carry exactly the promised value
#   (wrong value: 16b-paxos-wrong-value-neg.ep);
# - every channel is linear (quantity 1): dropping or double-using a
#   channel is rejected (Issue #64).
#
# Design note: the session datatype stays first-order (sendS/recvS/endS).
# A fancier formulation would use *dependent* session continuations
# (`sendD (A : ?) (k : A -> Session)`), but the elaborator rejects
# non-strictly-positive data -- the eliminator generator assumes every
# family-mentioning constructor argument is a direct `F ...` application
# (elab.nim `genElimTy` calls `extractIndices` on it). So the dependency
# lives in the *operation types* (tickets + indexed messages) instead of
# in the session datatype. Same guarantee, first-order sessions.
#
# The channel operations are postulates (mock transport ops), exactly as in
# session_types.nim: the types enforce the protocol, linearity is enforced
# at use sites. The normal-Nim driver below binds the same message sequence
# to a real (in-memory) transport, mirroring the checked roles step by
# step -- the Wu & Xi "typed API over untrusted backend" architecture.

import std/deques
import ett_mac
import ett_embed

ettBlock:
  data(Nat, Univ):
    proc zero(): Nat
    proc suc(n: Nat): Nat

  # Session protocol descriptions: what comes next on the channel.
  data(Session, Univ):
    proc sendS(A: Univ, s: Session): Session
    proc recvS(A: Univ, s: Session): Session
    proc endS(): Session

  # Channel indexed by current session state.
  data(Chan, Session -> Univ):
    proc mkChan(s: Session): Chan(s)

  # Promise ticket, indexed by the promised value. Postulated with NO
  # constructors: tickets are unforgeable. The acceptor's `sendPromise`
  # is the only source of `AcceptMsg v` inhabitants.
  postulate(AcceptMsg, Nat -> Univ)

  # Named session states: the full protocol is a 4-message exchange per
  # role, and spelling the nested sendS/recvS inline in every operation
  # type is unreadable (and paren-counting hell). accS2 needs the promised
  # value, so it takes it as a parameter.
  proc propS0(): Session =
    sendS(Nat, recvS(Nat, sendS(Nat, recvS(Nat, endS()))))
  proc propS1(): Session =
    recvS(Nat, sendS(Nat, recvS(Nat, endS())))
  proc propS2(): Session =
    sendS(Nat, recvS(Nat, endS()))
  proc propS3(): Session =
    recvS(Nat, endS())
  proc accS0(): Session =
    recvS(Nat, sendS(Nat, recvS(Nat, sendS(Nat, endS()))))
  proc accS1(): Session =
    sendS(Nat, recvS(Nat, sendS(Nat, endS())))
  proc accS2(v: Nat): Session =
    recvS(AcceptMsg(v), sendS(Nat, endS()))
  proc accS3(): Session =
    sendS(Nat, endS())

  # --- Proposer-side operations (postulates: mock transport) ---
  postulate(sendPrepare,
    Pi(ch {.linear.}: Chan(propS0()),
       n: Nat,
       Chan(propS1())))
  postulate(recvPromise,
    Pi(ch {.linear.}: Chan(propS1()),
       Sig(pr: Sig(v: Nat, AcceptMsg(v)), Chan(propS2()))))
  postulate(sendAccept,
    Pi(pr: Sig(v: Nat, AcceptMsg(v)),
       ch {.linear.}: Chan(propS2()),
       m: AcceptMsg(fst(pr)),
       Chan(propS3())))
  postulate(recvAccepted,
    Pi(ch {.linear.}: Chan(propS3()),
       Sig(x: Nat, Chan(endS()))))

  # --- Acceptor-side operations (postulates: mock transport) ---
  postulate(recvPrepare,
    Pi(ch {.linear.}: Chan(accS0()),
       Sig(n: Nat, Chan(accS1()))))
  postulate(sendPromise,
    Pi(v: Nat,
       ch {.linear.}: Chan(accS1()),
       Sig(t: AcceptMsg(v), Chan(accS2(v)))))
  postulate(recvAccept,
    Pi(v: Nat,
       ch {.linear.}: Chan(accS2(v)),
       Sig(m: AcceptMsg(v), Chan(accS3()))))
  postulate(sendAccepted,
    Pi(v: Nat,
       ch {.linear.}: Chan(accS3()),
       Chan(endS())))

  # Proposer role: prepare(1) -> promise(pr) -> accept(snd pr) -> accepted.
  # `pr : Sig(v : Nat). AcceptMsg v` is the promise (value + unforgeable
  # ticket): the only term the proposer can supply for m is `snd pr`
  # itself, so the accept provably carries the promised value. (pr is
  # omega: reusing it is harmless -- every use consumes the linear
  # channel, so the protocol still advances exactly once.)
  proc proposer(ch {.linear.}: Chan(propS0())): Chan(endS()) =
    let ch1 = sendPrepare(ch, 1)
    let pv = recvPromise(ch1)
    let pr = fst(pv)
    let ch2 = snd(pv)
    let ch3 = sendAccept(pr, ch2, snd(pr))
    let ac = recvAccepted(ch3)
    snd(ac)

  # Acceptor role: prepare(n) -> promise(stored) -> accept(_) -> accepted.
  # The mock promises `zero()` for any ballot; a real binding would compare
  # n against the promised ballot first. `recvAccept(stored, ch2)` demands
  # the accept message for exactly the promised value.
  proc acceptor(ch {.linear.}: Chan(accS0())): Chan(endS()) =
    let pn = recvPrepare(ch)
    let n = fst(pn)
    let ch1 = snd(pn)
    let stored = zero()
    let pt = sendPromise(stored, ch1)
    let ch2 = snd(pt)
    let am = recvAccept(stored, ch2)
    let ch3 = snd(am)
    sendAccepted(stored, ch3)

# --- Normal Nim program: transport binding + driver -----------------------
# The postulates above are the typed API. Here is the (untrusted) backend
# they would bind to, in the style of Wu & Xi's typed API over an untrusted
# implementation. We run a full proposer/acceptor exchange over in-memory
# mailboxes, mirroring the checked roles step by step; the runtime asserts
# are the dynamic shadow of the `AcceptMsg v` ticket discipline.

type Mailbox = object
  queue: Deque[int]

proc sendMsg(mb: var Mailbox, x: int) = mb.queue.addLast(x)
proc recvMsg(mb: var Mailbox): int = mb.queue.popFirst()

proc runPaxosRound(ballot: int, acceptorStored: int): int =
  ## One Paxos round over in-memory mailboxes. Returns the agreed value.
  var propBox, accBox: Mailbox
  # prepare(ballot): proposer -> acceptor
  sendMsg(accBox, ballot)
  # acceptor: recv prepare; promise(stored)
  let n = recvMsg(accBox)
  assert n == ballot, "ballot mismatch on the wire"
  sendMsg(propBox, acceptorStored)
  # proposer: recv promise(v); the accept must carry exactly v --
  # the runtime analog of the unforgeable-ticket discipline.
  let promised = recvMsg(propBox)
  sendMsg(accBox, promised)
  # acceptor: recv accept; it must equal the promised value.
  let accepted = recvMsg(accBox)
  assert accepted == acceptorStored,
    "acceptor got accept for a value it never promised"
  sendMsg(propBox, accepted)
  # proposer: recv accepted
  let decided = recvMsg(propBox)
  assert decided == promised, "proposer decided a value it was not promised"
  decided

proc main() =
  echo "paxos_session: two-role Paxos protocol elaborated at compile time."
  echo "  Promise tickets (AcceptMsg v) are unforgeable: the proposer can only"
  echo "  accept the value the acceptor promised. Wrong order / wrong value /"
  echo "  double use are compile-time errors (examples/ep/16a,16b-*-neg.ep)."
  let decided = runPaxosRound(ballot = 1, acceptorStored = 42)
  echo "  mock transport round: ballot 1, acceptor stored 42 -> decided ", decided

when isMainModule:
  main()
