## Property test for the checked session roles and their opaque Nim backend.

import falsify
import ../examples/embedded/session_runtime_bindings

when isMainModule:
  var rng = initRng(20261018'u64)
  let roleRoundTrips = forAll("checked session send/receive role pair",
    rng, 200,
    proc(r: var Rng): int = r.genInt(0, 10000),
    proc(message: int): bool =
      let channel = newChannelHandle()
      discard checkedSender(message, channel)
      checkedReceiver(channel) == message and channel.channelIsEmpty,
    shrinkInt)
  if not roleRoundTrips:
    quit(1)
  echo "test_session_runtime_bindings: checked role property passed"
