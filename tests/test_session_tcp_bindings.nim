## Loopback integration test for the checked session roles over std/net.

import ../examples/embedded/session_tcp_bindings

when isMainModule:
  runTcpDemo()
  runTcpFailureDemo()
