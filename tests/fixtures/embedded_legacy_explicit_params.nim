import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"

  proc legacySingleton(value: Nat): Vec[Nat, suc(zero)] =
    let empty = vecnil(Nat)
    cons(Nat, zero(), value, empty)

  proc legacyVectorType(value: Vec(Nat, suc(zero()))):
      Vec(Nat, suc(zero())) = value

  proc legacyAppend(left, right: Vec[Nat, suc(zero())]):
      Vec[Nat, add(suc(zero()), suc(zero()))] =
    vappend(Nat, suc(zero()), suc(zero()), left, right)

  # Partial applications are still distinguishable when a known data type
  # appears first: this is the legacy explicit A argument to cons, even though
  # the call supplies fewer arguments than cons has term binders.
  proc legacyPartial(value: Nat): Vec[Nat, 0] -> Vec[Nat, 1] =
    cons(Nat, zero(), value)

  # The generic binder is known to be a type only within this proc's scope.
  proc legacyPartialGeneric[A: Univ](value: A): Vec[A, 0] -> Vec[A, 1] =
    cons(A, zero(), value)

  # A normal Nim-shaped Eponym value call must not trigger the migration
  # diagnostic because its first argument is a value expression.
  proc ordinaryNat(): Nat = suc(zero())
