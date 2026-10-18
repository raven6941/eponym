## A TCP adapter for indexed session roles. Eponym checks the sender and
## receiver state transitions; std/net and the Nat framing codec are trusted.

import std/[net, os]
import eponym_mac
import eponym_embed
import session_runtime_bindings as codec

type TcpChannelHandle = ref object
  socket: Socket

proc sendNatTcp(value: int, channel: TcpChannelHandle): TcpChannelHandle =
  let frame = codec.encodeNatMessage(value)
  var bytes = newStringOfCap(frame.len)
  for item in frame:
    bytes.add(char(item))
  channel.socket.send(bytes)
  channel

proc recvNatTcp(channel: TcpChannelHandle): int =
  var frame: seq[byte]
  for _ in 0 ..< 9:
    let item = channel.socket.recv(1, timeout = 5000)
    if item.len != 1:
      raise newException(IOError, "TCP peer closed before completing a Nat frame")
    frame.add(byte(ord(item[0])))
    if (frame[^1] and 0x80'u8) == 0:
      return codec.decodeNatMessage(frame)
  raise newException(ValueError, "TCP Nat frame exceeds the supported length")

eponymBlock:
  import "../../lib/nat.ep"

  data(Session, Univ):
    proc sendS(A: Univ, s: Session): Session
    proc recvS(A: Univ, s: Session): Session
    proc endS(): Session

  postulate(Chan, Session -> Univ)
  runtimeType(Chan, TcpChannelHandle)
  postulate(sendNatTcpOp,
    Pi(value: Nat,
       ch {.linear.}: Chan(sendS(Nat, endS())),
       Chan(endS())))
  postulate(recvNatTcpOp,
    Pi(ch {.linear.}: Chan(recvS(Nat, endS())), Nat))
  bindPostulate(sendNatTcpOp, sendNatTcp, Nat, Chan, Chan)
  bindPostulate(recvNatTcpOp, recvNatTcp, Chan, Nat)
  proc checkedTcpSender(value: Nat,
      ch {.linear.}: Chan(sendS(Nat, endS()))): Chan(endS()) =
    sendNatTcpOp(value, ch)
  proc checkedTcpReceiver(ch {.linear.}: Chan(recvS(Nat, endS()))): Nat =
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
  discard checkedTcpSender(2026, client)
  let received = checkedTcpReceiver(server)
  doAssert received == 2026
  echo "session_tcp_bindings: checked TCP roles transferred 2026"

when isMainModule:
  if getEnv("EPONYM_RUN_LOOPBACK_TCP") == "1":
    runTcpDemo()
  else:
    echo "session_tcp_bindings: set EPONYM_RUN_LOOPBACK_TCP=1 to run loopback TCP"
