import eponym_mac

eponymBlock:
  data(Nat, Univ):
    proc zero(): Nat
  record(Handler):
    field(apply, Pi({n: Nat}, Nat -> Nat))

  proc legacyField(handler: Handler, value: Nat): Nat =
    handler.apply(zero(), value)
