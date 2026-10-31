import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  proc unsupported: Univ {.runtimeType.} = Sig(Nat, Nat)
