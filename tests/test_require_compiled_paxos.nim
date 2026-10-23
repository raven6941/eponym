# Paxos under requireCompiled() (issue #401).
#
# The same dependent session protocol as examples/embedded/paxos_session.nim,
# but the block demands representation-compiled definitions with direct typed
# wrappers: opaque host types (PaxosChannel/PaxosPromise/PaxosTicket) for the
# Chan/Promise/AcceptMsg families, host tuples for the dependent Sigmas, and
# the Session-valued protocol constructors classified compile-time-only.
# The test runs real TCP rounds through the compiled wrappers (differential
# coverage against the interpreter-backed example) and checks the artifact
# links no interpreter symbols, like tests/test_require_compiled.nim.

import std/[net, os, osproc, strutils]
import eponym_mac
import ../examples/embedded/session_runtime_bindings as codec

type
  PaxosChannel = ref object
    socket: Socket
    lastAccepted: int

  PaxosTicket = object
    value: int
    nonce: int

  PaxosPromise = object
    value: int
    ticket: PaxosTicket

proc writeNat(channel: PaxosChannel, value: int) =
  var frame = codec.encodeNatMessage(value)
  var bytes = newStringOfCap(frame.len)
  for item in frame:
    bytes.add(char(item))
  channel.socket.send(bytes)

proc readNat(channel: PaxosChannel): int =
  var frame: seq[byte] = @[]
  for _ in 0 ..< 9:
    let item = channel.socket.recv(1, timeout = 5000)
    if item.len != 1:
      raise newException(IOError, "Paxos peer closed during a Nat frame")
    frame.add(byte(ord(item[0])))
    if (frame[^1] and 0x80'u8) == 0:
      return codec.decodeNatMessage(frame)
  raise newException(IOError, "Paxos Nat frame is too long")

proc ticketMatches(promise: PaxosPromise, ticket: PaxosTicket): bool =
  ticket == promise.ticket and ticket.value == promise.value

proc hostSendPrepare(ballot: int, channel: PaxosChannel): PaxosChannel =
  channel.writeNat(ballot)
  channel

proc hostRecvPromise(ballot: int, channel: PaxosChannel):
    tuple[promise: PaxosPromise, channel: PaxosChannel] =
  let receivedBallot = channel.readNat()
  if receivedBallot != ballot:
    raise newException(IOError, "promise belongs to a different ballot")
  let value = channel.readNat()
  let nonce = channel.readNat()
  (PaxosPromise(value: value,
    ticket: PaxosTicket(value: value, nonce: nonce)), channel)

proc hostPromiseValue(promise: PaxosPromise): int = promise.value

proc hostPromiseTicket(promise: PaxosPromise): PaxosTicket = promise.ticket

proc hostSendAccept(promise: PaxosPromise, ticket: PaxosTicket,
                    channel: PaxosChannel): PaxosChannel =
  if not ticketMatches(promise, ticket):
    raise newException(IOError, "proposer sent a ticket for another value")
  channel.writeNat(ticket.value)
  channel.writeNat(ticket.nonce)
  channel

proc hostRecvAccepted(promise: PaxosPromise, ticket: PaxosTicket,
                      channel: PaxosChannel):
    tuple[accepted: int, channel: PaxosChannel] =
  if not ticketMatches(promise, ticket):
    raise newException(IOError, "proposer received acceptance for another value")
  let accepted = channel.readNat()
  if accepted != promise.value:
    raise newException(IOError, "acceptor acknowledged a different value")
  channel.lastAccepted = accepted
  (accepted, channel)

proc hostRecvPrepare(channel: PaxosChannel):
    tuple[ballot: int, channel: PaxosChannel] =
  (channel.readNat(), channel)

proc hostSendPromise(ballot, stored: int, channel: PaxosChannel):
    tuple[promise: PaxosPromise, channel: PaxosChannel] =
  let nonce = ballot xor stored
  let ticket = PaxosTicket(value: stored, nonce: nonce)
  channel.writeNat(ballot)
  channel.writeNat(stored)
  channel.writeNat(nonce)
  (PaxosPromise(value: stored, ticket: ticket), channel)

proc hostRecvAccept(promise: PaxosPromise, channel: PaxosChannel):
    tuple[ticket: PaxosTicket, channel: PaxosChannel] =
  let value = channel.readNat()
  let nonce = channel.readNat()
  let ticket = PaxosTicket(value: value, nonce: nonce)
  if not ticketMatches(promise, ticket):
    raise newException(IOError, "acceptor received a ticket for another value")
  (ticket, channel)

proc hostSendAccepted(promise: PaxosPromise, ticket: PaxosTicket,
                      channel: PaxosChannel): PaxosChannel =
  if not ticketMatches(promise, ticket):
    raise newException(IOError, "acceptor rejected a ticket for another value")
  channel.writeNat(promise.value)
  channel

eponymBlock:
  requireCompiled()
  import "../lib/nat.ep"

  data(Session, Univ):
    proc sendD(A: Univ, k: A -> Session): Session
    proc recvD(A: Univ, k: A -> Session): Session
    proc endS(): Session

  postulate(Chan, Session -> Univ)
  postulate(Promise, Univ)
  postulate(AcceptMsg, Nat -> Univ)
  runtimeType(Chan, PaxosChannel)
  runtimeType(Promise, PaxosPromise)
  runtimeType(AcceptMsg, PaxosTicket)
  runtimeType(Nat, int)

  postulate(promiseValue, Promise -> Nat)
  bindPostulate(promiseValue, hostPromiseValue, Promise, Nat)
  postulate(promiseTicket,
    Pi(promise: Promise, AcceptMsg(promiseValue(promise))))
  bindPostulate(promiseTicket, hostPromiseTicket, Promise, AcceptMsg)

  proc propAfterAccept(accepted: Nat): Session = endS()
  proc propAfterPromise(promise: Promise): Session =
    sendD(AcceptMsg(promiseValue(promise)),
      lam(ticket, AcceptMsg(promiseValue(promise)),
        recvD(Nat, propAfterAccept)))
  proc propAfterPrepare(ballot: Nat): Session =
    recvD(Promise, propAfterPromise)
  proc propProto(): Session = sendD(Nat, propAfterPrepare)

  proc accAfterAccept(accepted: Nat): Session = endS()
  proc accAfterPromise(promise: Promise): Session =
    recvD(AcceptMsg(promiseValue(promise)),
      lam(ticket, AcceptMsg(promiseValue(promise)),
        sendD(Nat, accAfterAccept)))
  proc accAfterPrepare(ballot: Nat): Session =
    sendD(Promise, accAfterPromise)
  proc accProto(): Session = recvD(Nat, accAfterPrepare)

  postulate(sendPrepare,
    Pi(ballot: Nat,
       ch {.linear.}: Chan(propProto()),
       Chan(propAfterPrepare(ballot))))
  bindPostulate(sendPrepare, hostSendPrepare, Nat, Chan, Chan)

  postulate(recvPromise,
    Pi(ballot: Nat,
       ch {.linear.}: Chan(propAfterPrepare(ballot)),
       Sig(promise: Promise, Chan(propAfterPromise(promise)))))
  bindPostulatePairTrusted(recvPromise, hostRecvPromise,
    Nat, Chan, Promise, Chan)

  postulate(sendAccept,
    Pi(promise: Promise,
       ticket: AcceptMsg(promiseValue(promise)),
       ch {.linear.}: Chan(propAfterPromise(promise)),
       Chan(recvD(Nat, propAfterAccept))))
  bindPostulate(sendAccept, hostSendAccept,
    Promise, AcceptMsg, Chan, Chan)

  postulate(recvAccepted,
    Pi(promise: Promise,
       ticket: AcceptMsg(promiseValue(promise)),
       ch {.linear.}: Chan(recvD(Nat, propAfterAccept)),
       Sig(accepted: Nat, Chan(endS()))))
  bindPostulatePair(recvAccepted, hostRecvAccepted,
    Promise, AcceptMsg, Chan, Nat, Chan)

  postulate(recvPrepare,
    Pi(ch {.linear.}: Chan(accProto()),
       Sig(ballot: Nat, Chan(accAfterPrepare(ballot)))))
  bindPostulatePairTrusted(recvPrepare, hostRecvPrepare,
    Chan, Nat, Chan)

  postulate(sendPromise,
    Pi(ballot: Nat,
       stored: Nat,
       ch {.linear.}: Chan(accAfterPrepare(ballot)),
       Sig(promise: Promise, Chan(accAfterPromise(promise)))))
  bindPostulatePairTrusted(sendPromise, hostSendPromise,
    Nat, Nat, Chan, Promise, Chan)

  postulate(recvAccept,
    Pi(promise: Promise,
       ch {.linear.}: Chan(accAfterPromise(promise)),
       Sig(ticket: AcceptMsg(promiseValue(promise)),
         Chan(sendD(Nat, accAfterAccept)))))
  bindPostulatePair(recvAccept, hostRecvAccept,
    Promise, Chan, AcceptMsg, Chan)

  postulate(sendAccepted,
    Pi(promise: Promise,
       ticket: AcceptMsg(promiseValue(promise)),
       ch {.linear.}: Chan(sendD(Nat, accAfterAccept)),
       Chan(endS())))
  bindPostulate(sendAccepted, hostSendAccepted,
    Promise, AcceptMsg, Chan, Chan)

  proc proposer(ballot: Nat, ch {.linear.}: Chan(propProto())):
      Sig(accepted: Nat, Chan(endS())) =
    let ch1 = sendPrepare(ballot, ch)
    let promiseAndChannel = recvPromise(ballot, ch1)
    let ch3 = sendAccept(fst(promiseAndChannel),
      promiseTicket(fst(promiseAndChannel)), snd(promiseAndChannel))
    recvAccepted(fst(promiseAndChannel),
      promiseTicket(fst(promiseAndChannel)), ch3)

  proc acceptor(stored: Nat, ch {.linear.}: Chan(accProto())): Chan(endS()) =
    let ballotAndChannel = recvPrepare(ch)
    let promiseAndChannel = sendPromise(fst(ballotAndChannel), stored,
      snd(ballotAndChannel))
    let ticketAndChannel = recvAccept(fst(promiseAndChannel),
      snd(promiseAndChannel))
    sendAccepted(fst(promiseAndChannel), fst(ticketAndChannel),
      snd(ticketAndChannel))


proc runPaxosAcceptor*(port, stored: int) =
  var socket = newSocket()
  defer: socket.close()
  socket.connect("127.0.0.1", Port(port))
  let channel = PaxosChannel(socket: socket)
  discard acceptor(stored, channel)

proc runPaxosRound*(ballot, acceptorStored: int): int =
  if ballot < 0 or acceptorStored < 0:
    raise newException(ValueError, "Paxos ballot and stored value must be Nats")
  var listener = newSocket()
  defer: listener.close()
  listener.setSockOpt(OptReuseAddr, true)
  listener.bindAddr(Port(0), "127.0.0.1")
  listener.listen()
  let (_, port) = listener.getLocalAddr()

  let child = startProcess(getAppFilename(),
    args = @["--paxos-acceptor", $port, $acceptorStored],
    options = {poParentStreams})
  var childWaited = false
  defer:
    if not childWaited:
      discard child.waitForExit()
    child.close()
  var peer: owned(Socket)
  # This demo accepts only the acceptor subprocess started above, which
  # connects immediately to the ephemeral loopback port. The blocking accept
  # intentionally waits for that controlled child rather than an external peer.
  listener.accept(peer)
  let channel = PaxosChannel(socket: peer)
  defer: channel.socket.close()
  let acceptedAndChannel = proposer(ballot, channel)
  if acceptedAndChannel[0] != acceptorStored:
    raise newException(IOError, "checked proposer received the wrong accepted value")
  let childStatus = child.waitForExit()
  childWaited = true
  if childStatus != 0:
    raise newException(IOError, "checked acceptor process failed")
  acceptedAndChannel[0]

when isMainModule:
  if paramCount() == 3 and paramStr(1) == "--paxos-acceptor":
    runPaxosAcceptor(parseInt(paramStr(2)), parseInt(paramStr(3)))
  else:
    for (ballot, stored) in [(1, 42), (2, 7), (5, 1000)]:
      let accepted = runPaxosRound(ballot, stored)
      doAssert accepted == stored,
        "requireCompiled Paxos round lost the promised value"
      echo "test_require_compiled_paxos: round ballot=", ballot,
        " stored=", stored, " accepted=", accepted
    let (symbols, nmStatus) = execCmdEx("nm " & quoteShell(getAppFilename()))
    doAssert nmStatus == 0, "could not inspect compiled test artifact with nm"
    for interpreterSymbol in ["evalWhnf", "evalWithBindings", "callValueFuncDir",
        "getGlobalsDir", "elabCheckDirStateAll"]:
      doAssert interpreterSymbol notin symbols,
        "representation-compiled Paxos artifact linked " & interpreterSymbol
    echo "test_require_compiled_paxos: strict Paxos block passed"
