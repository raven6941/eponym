import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"
  import "ambiguous_callable_records.ep"

  proc oldTypedAliasImportedFieldType(
      bundle: HandlerBundle, value: Vec[Nat, 0]): Vec[Nat, 0] =
    let nested: PolymorphicHandler = bundle.inner
    nested.apply(zero(), value)
