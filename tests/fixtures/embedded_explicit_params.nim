import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"
  import "../../lib/bool.ep"

  data(Protocol, Univ):
    proc protocolSend(A: Univ, payload: Nat): Protocol

  compileTimeOnly(localLegacyConstructor)
  proc localLegacyConstructor(): Protocol = protocolSend[Nat](zero())
  compileTimeOnly(localBracketConstructor)
  proc localBracketConstructor(): Protocol = protocolSend[Nat](zero())

  compileTimeOnly(legacySingleton)
  proc legacySingleton(value: Nat): Vec[Nat, suc(zero)] =
    let empty = vecnil[Nat]()
    cons[Nat, zero()](value, empty)

  compileTimeOnly(bracketVectorType)
  proc bracketVectorType(value: Vec[Nat, suc(zero())]):
      Vec[Nat, suc(zero())] = value

  compileTimeOnly(legacyAppend)
  proc legacyAppend(left, right: Vec[Nat, suc(zero())]):
      Vec[Nat, add(suc(zero()), suc(zero()))] =
    vappend[Nat, suc(zero()), suc(zero())](left, right)

  # Partial applications are still distinguishable when a known data type
  # appears first: this is the legacy explicit A argument to cons, even though
  # the call supplies fewer arguments than cons has term binders.
  compileTimeOnly(bracketPartial)
  proc bracketPartial(value: Nat): Vec[Nat, 0] -> Vec[Nat, 1] =
    cons[Nat, zero()](value)

  # The generic binder is known to be a type only within this proc's scope.
  compileTimeOnly(bracketPartialGeneric)
  proc bracketPartialGeneric[A: Univ](value: A): Vec[A, 0] -> Vec[A, 1] =
    cons[A, zero()](value)

  compileTimeOnly(indexHead)
  proc indexHead[n: Nat](xs, ys: Vec[Nat, n]): Vec[Nat, n] = xs

  compileTimeOnly(bracketPartialIndex)
  proc bracketPartialIndex[n: Nat](xs: Vec[Nat, n]):
      Vec[Nat, n] -> Vec[Nat, n] -> Vec[Nat, n] = indexHead[n]

  compileTimeOnly(bracketPartialIndexExpr)
  proc bracketPartialIndexExpr():
      Vec[Nat, 0] -> Vec[Nat, 0] -> Vec[Nat, 0] = indexHead[zero()]

  compileTimeOnly(bracketNatIf)
  proc bracketNatIf(enabled: Bool): Nat =
    let index = if enabled: zero() else: suc(zero())
    index

  # Ordinary Nim-shaped Eponym value calls remain parenthesized.
  compileTimeOnly(ordinaryNat)
  proc ordinaryNat(): Nat = suc(zero())
  compileTimeOnly(ordinaryNatArg)
  proc ordinaryNatArg(value: Nat): Nat = value
  compileTimeOnly(ordinaryNatCall)
  proc ordinaryNatCall(): Nat = ordinaryNatArg(zero())

eponymBlock:
  postulate(Nat, Univ)
  compileTimeOnly(callbackInferredType)
  proc callbackInferredType(
      callback: Pi(A: Univ, value: A, A), value: Nat): Nat =
    callback[Nat](value)
