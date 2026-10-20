## A TCP adapter for indexed session roles. Eponym checks the sender and
## receiver state transitions; std/net and the Nat framing codec are trusted.

import std/net
when isMainModule:
  import std/os
import eponym_mac
import eponym_embed
import session_runtime_bindings as codec

type TcpChannelHandle = ref object
  socket: Socket

type TransportError = enum
  transportFailure, codecFailure

type TransportResult[T] = object
  case isOk*: bool
  of true:
    value*: T
  of false:
    error*: TransportError

proc success[T](value: T): TransportResult[T] =
  TransportResult[T](isOk: true, value: value)

proc failure[T](error: TransportError): TransportResult[T] =
  TransportResult[T](isOk: false, error: error)

proc sendNatTcp(value: int, channel: TcpChannelHandle):
    TransportResult[TcpChannelHandle] =
  var frame: seq[byte]
  try:
    frame = codec.encodeNatMessage(value)
  except CatchableError:
    return failure[TcpChannelHandle](codecFailure)
  var bytes = newStringOfCap(frame.len)
  for item in frame:
    bytes.add(char(item))
  try:
    channel.socket.send(bytes)
    success(channel)
  except CatchableError:
    failure[TcpChannelHandle](transportFailure)

proc recvNatTcp(channel: TcpChannelHandle): TransportResult[int] =
  var frame: seq[byte]
  for _ in 0 ..< 9:
    var item: string
    try:
      item = channel.socket.recv(1, timeout = 5000)
    except CatchableError:
      return failure[int](transportFailure)
    if item.len != 1:
      return failure[int](transportFailure)
    frame.add(byte(ord(item[0])))
    if (frame[^1] and 0x80'u8) == 0:
      try:
        return success(codec.decodeNatMessage(frame))
      except CatchableError:
        return failure[int](codecFailure)
  failure[int](codecFailure)

eponymBlock:
  import "../../lib/nat.ep"

  data(Session, Univ):
    proc sendS(A: Univ, s: Session): Session
    proc recvS(A: Univ, s: Session): Session
    proc endS(): Session

  postulate(Chan, Session -> Univ)
  postulate(SendOutcome, Univ)
  postulate(ReceiveOutcome, Univ)
  runtimeType(Chan, TcpChannelHandle)
  runtimeType(SendOutcome, TransportResult[TcpChannelHandle])
  runtimeType(ReceiveOutcome, TransportResult[int])
  postulate(sendNatTcpOp,
    Pi(value: Nat,
       ch {.linear.}: Chan(sendS(Nat, endS())),
       SendOutcome))
  postulate(recvNatTcpOp,
    Pi(ch {.linear.}: Chan(recvS(Nat, endS())), ReceiveOutcome))
  bindPostulate(sendNatTcpOp, sendNatTcp, Nat, Chan, SendOutcome)
  bindPostulate(recvNatTcpOp, recvNatTcp, Chan, ReceiveOutcome)
  proc checkedTcpSender(value: Nat,
      ch {.linear.}: Chan(sendS(Nat, endS()))): SendOutcome =
    sendNatTcpOp(value, ch)
  proc checkedTcpReceiver(ch {.linear.}: Chan(recvS(Nat, endS()))): ReceiveOutcome =
    recvNatTcpOp(ch)

proc runTcpDemo*() =
  var listener = newSocket()
  defer: listener.close()
  listener.setSockOpt(OptReuseAddr, true)
  listener.bindAddr(Port(0), "127.0.0.1")
  listener.listen()
  let (_, port) = listener.getLocalAddr()

  let clientSocket = newSocket()
  defer: clientSocket.close()
  clientSocket.connect("127.0.0.1", port)
  var serverSocket: owned(Socket)
  listener.accept(serverSocket)
  defer: serverSocket.close()

  let client = TcpChannelHandle(socket: clientSocket)
  let server = TcpChannelHandle(socket: serverSocket)
  let sent = checkedTcpSender(2026, client)
  doAssert sent.isOk, "TCP send failed: " & $sent.error
  let received = checkedTcpReceiver(server)
  doAssert received.isOk, "TCP receive failed: " & $received.error
  doAssert received.value == 2026
  echo "session_tcp_bindings: checked TCP roles transferred 2026"

proc runTcpFailureDemo*() =
  proc checkFailure(malformedFrame: bool, expected: TransportError) =
    var listener = newSocket()
    defer: listener.close()
    listener.setSockOpt(OptReuseAddr, true)
    listener.bindAddr(Port(0), "127.0.0.1")
    listener.listen()
    let (_, port) = listener.getLocalAddr()

    let clientSocket = newSocket()
    clientSocket.connect("127.0.0.1", port)
    var serverSocket: owned(Socket)
    listener.accept(serverSocket)
    if malformedFrame:
      clientSocket.send("\x80\x80\x80\x80\x80\x80\x80\x80\x80\x00")
      clientSocket.close()
    else:
      clientSocket.close()
    defer: serverSocket.close()

    let received = checkedTcpReceiver(
      TcpChannelHandle(socket: serverSocket))
    doAssert not received.isOk
    doAssert received.error == expected

  checkFailure(false, transportFailure)
  checkFailure(true, codecFailure)
  echo "session_tcp_bindings: transport and codec failures returned explicitly"

when isMainModule:
  if getEnv("EPONYM_RUN_LOOPBACK_TCP") == "1":
    runTcpDemo()
  else:
    echo "session_tcp_bindings: set EPONYM_RUN_LOOPBACK_TCP=1 to run loopback TCP"
