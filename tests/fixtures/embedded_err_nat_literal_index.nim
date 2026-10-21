import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  proc badLiteralVector(x, y: Nat): Vec[Nat, 1] =
    cons[Nat, 1](x, cons[Nat, 0](y, vecnil[Nat]()))
