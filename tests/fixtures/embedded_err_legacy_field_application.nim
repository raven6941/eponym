import eponym_mac

eponymBlock:
  import "callable_record_field.ep"

  proc legacyField(handler: Handler, value: Nat): Nat =
    (handler.apply)(zero(), value)
