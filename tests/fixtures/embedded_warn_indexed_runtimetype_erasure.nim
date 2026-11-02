## Fixture for tests/test_embedded_error_path.nim (issue #517).
## An indexed family's opaque runtime mapping erases its index from the Nim
## representation. The warning must explain that the checked distinction is
## compile-time only, so host code must not expect the value to remember it.
import eponym_mac

type ChannelHandle = object

eponymBlock:
  postulate(Nat, Univ)
  runtimeType(Nat, int)
  postulate(Channel, Nat -> Univ)
  runtimeType(Channel, ChannelHandle)
