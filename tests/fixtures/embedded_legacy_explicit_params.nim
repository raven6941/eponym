import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  data(Protocol, Univ):
    proc protocolSend(A: Univ, payload: Nat): Protocol

  proc localLegacyConstructor(): Protocol = protocolSend[Nat](zero())
  proc localBracketConstructor(): Protocol = protocolSend[Nat](zero())

  proc legacySingleton(value: Nat): Vec[Nat, suc(zero)] =
    let empty = vecnil[Nat]()
    cons[Nat, zero()](value, empty)

  proc bracketVectorType(value: Vec[Nat, suc(zero())]):
      Vec[Nat, suc(zero())] = value

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

  # Ordinary Nim-shaped Eponym value calls remain parenthesized.
  proc ordinaryNat(): Nat = suc(zero())
  proc ordinaryNatArg(value: Nat): Nat = value
  proc ordinaryNatCall(): Nat = ordinaryNatArg(zero())
