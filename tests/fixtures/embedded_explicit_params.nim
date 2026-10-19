import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"
  import "../../lib/bool.ep"
  import "legacy_postulate_index.ep"
  import "callable_record_field.ep"
  import "callable_record_field_value.ep"
  import "returned_identity_factory.ep"

  data(Protocol, Univ):
    proc protocolSend(A: Univ, payload: Nat): Protocol

  record(LocalCallableField):
    field(apply, Nat -> Nat -> Nat)

  record(OrdinaryIdentityField):
    field(identity, Nat -> Nat)


  proc localLegacyConstructor(): Protocol = protocolSend[Nat](zero())
  proc localBracketConstructor(): Protocol = protocolSend[Nat](zero())

  proc legacySingleton(value: Nat): Vec[Nat, suc(zero)] =
    let empty = vecnil[Nat]()
    cons[Nat, zero()](value, empty)

  proc bracketVectorType(value: Vec[Nat, suc(zero())]):
      Vec[Nat, suc(zero())] = value

  proc bracketInferredEqualityIndex(): Eq[Nat, zero(), zero()] =
    refl[Nat](zero())

  proc bracketIndexedHead(values: Vec[Nat, 0]): Vec[Nat, 0] =
    indexedHead[zero()](values)

  proc inferredIndexedHead(values: Vec[Nat, 0]): Vec[Nat, 0] =
    indexedHead(values)

  proc identityFactory(): Pi(A: Univ, value: A, A) =
    lam(A, Univ, lam(value, A, value))

  proc bracketHigherOrderResult(value: Nat): Nat =
    identityFactory()[Nat](value)

  proc bracketHigherOrderAlias(value: Nat): Nat =
    let callback = identityFactory()
    callback[Nat](value)

  proc bracketImportedHigherOrderResult(value: Nat): Nat =
    importedIdentityFactory(unitv)[Nat](value)

  proc bracketCallbackParameter(
      callback: Pi(A: Univ, value: A, A), value: Nat): Nat =
    callback[Nat](value)

  proc bracketAscribedCallback(
      callback: Pi(A: Univ, value: A, A), value: Nat): Nat =
    (callback : Pi(A: Univ, value: A, A))[Nat](value)

  proc plainNatIdentity(value: Nat): Nat = value

  proc ordinaryCallAfterShadowing(
      callback: Pi(A: Univ, value: A, A), value: Nat): Nat =
    let callback = plainNatIdentity
    callback(value)

  proc bracketCallableRecordField(handler: CallableField,
                                  value: Nat): Nat =
    handler.apply[zero()](value)

  proc bracketImplicitCallableRecordField(handler: Handler,
                                          value: Nat): Nat =
    handler.apply[zero()](value)

  proc bracketLocalCallableRecordField(handler: LocalCallableField,
                                       value: Nat): Nat =
    handler.apply[zero()](value)

  proc ordinaryCallThroughNameCollidingField(
      handler: OrdinaryIdentityField, value: Nat): Nat =
    handler.identity(value)

  proc bracketCallbackAfterTerm(
      callback: Nat -> Pi(A: Univ, value: A, A), argument, value: Nat): Nat =
    callback(argument)[Nat](value)

  proc legacyAppend(left, right: Vec[Nat, suc(zero())]):
      Vec[Nat, add(suc(zero()), suc(zero()))] =
    vappend[Nat, suc(zero()), suc(zero())](left, right)

  # Partial applications are still distinguishable when a known data type
  # appears first: this is the legacy explicit A argument to cons, even though
  # the call supplies fewer arguments than cons has term binders.
  proc bracketPartial(value: Nat): Vec[Nat, 0] -> Vec[Nat, 1] =
    cons[Nat, zero()](value)

  # The generic binder is known to be a type only within this proc's scope.
  proc bracketPartialGeneric[A: Univ](value: A): Vec[A, 0] -> Vec[A, 1] =
    cons[A, zero()](value)

  proc indexHead[n: Nat](xs, ys: Vec[Nat, n]): Vec[Nat, n] = xs

  proc bracketPartialIndex[n: Nat](xs: Vec[Nat, n]):
      Vec[Nat, n] -> Vec[Nat, n] -> Vec[Nat, n] = indexHead[n]

  proc bracketPartialIndexExpr():
      Vec[Nat, 0] -> Vec[Nat, 0] -> Vec[Nat, 0] = indexHead[zero()]

  proc bracketNatIf(enabled: Bool): Nat =
    let index = if enabled: zero() else: suc(zero())
    index

  # Ordinary Nim-shaped Eponym value calls remain parenthesized.
  proc ordinaryNat(): Nat = suc(zero())
  proc ordinaryNatArg(value: Nat): Nat = value
  proc ordinaryNatCall(): Nat = ordinaryNatArg(zero())
