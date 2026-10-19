import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"
  import "ambiguous_callable_records.ep"

  proc oldNestedImportedFieldType(
      bundle: HandlerBundle, value: Vec[Nat, 0]): Vec[Nat, 0] =
    bundle.inner.apply(zero(), value)
