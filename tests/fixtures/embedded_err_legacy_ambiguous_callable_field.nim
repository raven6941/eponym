import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  record(PolymorphicHandler):
    field(apply, Pi(n: Nat, value: Vec[Nat, n], Vec[Nat, n]))

  record(NumericHandler):
    field(apply, Nat -> Nat)

  proc oldPositionalFieldType(
      handler: PolymorphicHandler, value: Vec[Nat, 0]): Vec[Nat, 0] =
    handler.apply(zero(), value)
