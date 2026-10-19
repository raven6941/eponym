import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  record(PolymorphicHandler):
    field(apply, Pi(n: Nat, value: Vec[Nat, n], Vec[Nat, n]))

  record(NumericHandler):
    field(apply, Nat -> Nat)

  record(HandlerBundle):
    field(inner, PolymorphicHandler)

  proc oldNestedPositionalFieldType(
      bundle: HandlerBundle, value: Vec[Nat, 0]): Vec[Nat, 0] =
    bundle.inner.apply(zero(), value)
