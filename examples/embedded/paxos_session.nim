# Paxos, embedded (Issues #101, #120).
#
# The Paxos prepare/promise/accept/accepted exchange as dependent session
# types (Issue #113). The session datatype has higher-order continuations:
#   sendD (A : ?) (k : A -> Session)
#   recvD (A : ?) (k : A -> Session)
# so the continuation can depend on the value communicated.
#
# The value discipline -- the proposer must accept *the value the acceptor
# promised*, not substitute its own -- is enforced by unforgeable promise
# tickets: `AcceptMsg` is postulated with *no constructors*, so the only
# `AcceptMsg v` a proposer can ever hold is the ticket returned by the
# acceptor's promise. The dependent session binds the received promise `pr`
# and the accept step demands `AcceptMsg (fst (fst pv))`; the only inhabitant
# available is `snd (fst pv)` itself. Substituting another value is not a
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
# Design note: the session datatype is higher-order (sendD/recvD). The value
# dependency lives in the session term itself: after `recvD (Sig (v : Nat).
# AcceptMsg v) propAfterPromise`, the continuation `propAfterPromise` is a
# function of the received promise, and its body mentions `(fst pr)`. No
# indexed session-state families (cf. the first-order encoding in #101,
# which needed `accS2(v : Nat) : Session` as an external family).
#
# The channel operations are postulates (mock transport ops), exactly as in
# session_types.nim: the types enforce the protocol, linearity is enforced
# at use sites. The normal-Nim driver below binds the same message sequence
# to a real (in-memory) transport, mirroring the checked roles step by
# step -- the Wu & Xi "typed API over untrusted backend" architecture.

import std/deques
import eponym_mac
import eponym_embed

eponymBlock:
  # Prelude import (issue #131): Nat, zero, suc, add, mul from lib/nat.ep
  # (was a per-file data(Nat, ...) redefinition before #131).
  import "../../lib/nat.ep"

  # Dependent session datatype (Issue #113): continuations are functions
  # of the communicated value.
  data(Session, Univ):
    proc sendD(A: Univ, k: A -> Session): Session
    proc recvD(A: Univ, k: A -> Session): Session
    proc endS(): Session

  data(Chan, Session -> Univ):
    proc mkChan(s: Session): Chan(s)

  # Promise ticket, indexed by the promised value. Postulated with NO
  # constructors: tickets are unforgeable. The acceptor's promise is the
  # only source of AcceptMsg(v) inhabitants.
  postulate(AcceptMsg, Nat -> Univ)

  # Proposer protocol: send prepare(n); receive promise pr : Sig(v, AcceptMsg v);
  # send accept carrying AcceptMsg(fst pr) -- the ticket for the promised value;
  # receive accepted. The continuation after the promise mentions (fst pr).
  # Continuations are named procs (functions A -> Session); the binder pr is
  # bound by recvD itself, not passed as an external family parameter.
  proc propAfterAccept(a: Nat): Session =
    endS()
  proc propAfterPromise(pr: Sig(v: Nat, AcceptMsg(v))): Session =
    sendD(AcceptMsg(fst(pr)), lam(t, AcceptMsg(fst(pr)),
      recvD(Nat, propAfterAccept)))
  proc propAfterPrepare(n: Nat): Session =
    recvD(Sig(v: Nat, AcceptMsg(v)), propAfterPromise)
  proc propProto(): Session =
    sendD(Nat, propAfterPrepare)

  # Acceptor protocol: receive prepare(n); send promise (v, ticket);
  # receive accept carrying AcceptMsg(fst pr); send accepted.
  proc accAfterAccept(v2: Nat): Session =
    endS()
  proc accAfterPromise(pr: Sig(v: Nat, AcceptMsg(v))): Session =
    recvD(AcceptMsg(fst(pr)), lam(t, AcceptMsg(fst(pr)),
      sendD(Nat, accAfterAccept)))
  proc accAfterPrepare(n: Nat): Session =
    sendD(Sig(v: Nat, AcceptMsg(v)), accAfterPromise)
  proc accProto(): Session =
    recvD(Nat, accAfterPrepare)

  # --- Proposer operations (postulates: mock transport) ---
  # Each step's channel type is the dependent session term; the value
  # dependency (fst pr) is inside the session, not in an external family.
  postulate(sendPrepare,
    Pi(ch {.linear.}: Chan(propProto()),
       n: Nat,
       Chan(propAfterPrepare(n))))
  postulate(recvPromise,
    Pi(n: Nat,
       ch {.linear.}: Chan(propAfterPrepare(n)),
       Sig(pr: Sig(v: Nat, AcceptMsg(v)),
         Chan(propAfterPromise(pr)))))
  postulate(sendAccept,
    Pi(pv: Sig(pr: Sig(v: Nat, AcceptMsg(v)),
           Chan(propAfterPromise(pr))),
       t: AcceptMsg(fst(fst(pv))),
       Chan(recvD(Nat, propAfterAccept))))
  postulate(recvAccepted,
    Pi(pv: Sig(pr: Sig(v: Nat, AcceptMsg(v)),
           Chan(propAfterPromise(pr))),
       t: AcceptMsg(fst(fst(pv))),
       ch {.linear.}: Chan(recvD(Nat, propAfterAccept)),
       Sig(a: Nat, Chan(endS()))))

  # --- Acceptor operations (postulates: mock transport) ---
  postulate(recvPrepare,
    Pi(ch {.linear.}: Chan(accProto()),
       Sig(n: Nat, Chan(accAfterPrepare(n)))))
  postulate(sendPromise,
    Pi(n: Nat,
       v: Nat,
       ch {.linear.}: Chan(accAfterPrepare(n)),
       Sig(pr: Sig(v0: Nat, AcceptMsg(v0)),
         Chan(accAfterPromise(pr)))))
  postulate(recvAccept,
    Pi(pt: Sig(pr: Sig(v: Nat, AcceptMsg(v)),
           Chan(accAfterPromise(pr))),
       Sig(t: AcceptMsg(fst(fst(pt))),
         Chan(sendD(Nat, accAfterAccept)))))
  postulate(sendAccepted,
    Pi(pt: Sig(pr: Sig(v: Nat, AcceptMsg(v)),
           Chan(accAfterPromise(pr))),
       t: AcceptMsg(fst(fst(pt))),
       am: Sig(t0: AcceptMsg(fst(fst(pt))),
         Chan(sendD(Nat, accAfterAccept))),
       v2: Nat,
       ch {.linear.}: Chan(sendD(Nat, accAfterAccept)),
       Chan(endS())))

  # Proposer role: prepare(1) -> promise(pr) -> accept(snd pr) -> accepted.
  # The ticket discipline (snd(fst(pv)) : AcceptMsg(fst(fst(pv)))) enforces
  # the value match: the accept carries the ticket for the promised value.
  proc proposer(ch {.linear.}: Chan(propProto())): Chan(endS()) =
    let ch1 = sendPrepare(ch, 1)
    let pv = recvPromise(1, ch1)
    let ch3 = sendAccept(pv, snd(fst(pv)))
    let ac = recvAccepted(pv, snd(fst(pv)), ch3)
    snd(ac)

  # Acceptor role: prepare(n) -> promise(stored) -> accept(_) -> accepted.
  proc acceptor(ch {.linear.}: Chan(accProto())): Chan(endS()) =
    let pn = recvPrepare(ch)
    let n = fst(pn)
    let ch1 = snd(pn)
    let stored = zero()
    let pt = sendPromise(n, stored, ch1)
    let am = recvAccept(pt)
    let t = fst(am)
    let ch3 = snd(am)
    sendAccepted(pt, t, am, stored, ch3)

# --- Normal Nim program: transport binding + driver -----------------------
type Mailbox = object
  queue: Deque[int]

proc sendMsg(mb: var Mailbox, x: int) = mb.queue.addLast(x)
proc recvMsg(mb: var Mailbox): int = mb.queue.popFirst()

proc runPaxosRound(ballot: int, acceptorStored: int): int =
  var propBox, accBox: Mailbox
  sendMsg(accBox, ballot)
  let n = recvMsg(accBox)
  assert n == ballot, "ballot mismatch on the wire"
  sendMsg(propBox, acceptorStored)
  let promised = recvMsg(propBox)
  sendMsg(accBox, promised)
  let accepted = recvMsg(accBox)
  assert accepted == acceptorStored,
    "acceptor got accept for a value it never promised"
  sendMsg(propBox, accepted)
  let decided = recvMsg(propBox)
  assert decided == promised, "proposer decided a value it was not promised"
  decided

proc main() =
  echo "paxos_session: Paxos with dependent session continuations (Issue #120)."
  echo "  The protocol is a dependent session term; continuations are functions"
  echo "  of the communicated value (Issue #113). Tickets (AcceptMsg v) remain"
  echo "  the unforgeability mechanism. Wrong order / wrong value are"
  echo "  compile-time errors (examples/ep/16a,16b-*-neg.ep)."
  let decided = runPaxosRound(ballot = 1, acceptorStored = 42)
  echo "  mock transport round: ballot 1, acceptor stored 42 -> decided ", decided

when isMainModule:
  main()
