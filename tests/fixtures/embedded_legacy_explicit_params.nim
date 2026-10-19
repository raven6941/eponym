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

  # A normal Nim-shaped Eponym value call must not trigger the migration
  # diagnostic because its first argument is a value expression.
  proc ordinaryNat(): Nat = suc(zero())
