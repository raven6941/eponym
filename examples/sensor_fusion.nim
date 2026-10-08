# Sensor fusion with verified core (ettBlock version)
#
# A Nim program that fuses 3 sensor readings with a weighted sum.
# The core math is in an ettBlock where dependent types check the
# implementation — no """ string delimiter needed!
#
# - `mkVec3` builds a `Vec Int three`; the elaborator CHECKS the body
#   constructs exactly 3 elements.
# - `dot3` builds two `Vec Int three`s, proving arity matches.
#
# Nim-friendly forms used here (with Eponym equivalents):
# - `ettBlock:` — block macro, no """ string (vs ettEmbed"""...""")
# - `proc` — Nim keyword (Eponym string syntax also uses `proc` now, was `def`)
# - `=` — Nim definition (was `:=` in old Eponym syntax)
# - `postulate(Int, Univ)` — call syntax; `Univ` stands for `?` (`?` isn't valid Nim)
# - `data(Nat, Univ):` — block syntax for datatypes (vs `data Nat : ? where`)
# - `Vec(A, zero())` — call syntax for type application (vs `Vec A zero`)
# - `vecnil` — Nim keyword workaround; maps to Eponym `nil` constructor
# - `Nat -> Univ` — infix `->` for Pi types (valid Nim, right-associative)
#
# The surrounding Nim program handles IO and orchestration.

import ett_mac
import ett_embed

# ettBlock: takes a Nim AST block (not a string). No """ delimiter.
# Each proc/data/postulate is converted to Eponym source at compile time,
# elaborated, and wrapped as a callable Nim proc.
ettBlock:
  # postulate(Int, Univ): declares primitive Int type.
  # Call syntax because `postulate Int : ?` isn't valid Nim (`?` doesn't parse).
  # `Univ` is the Nim-friendly spelling of Eponym's `?` (the universe).
  postulate(Int, Univ)

  # data(Nat, Univ): defines inductive Nat.
  # Block syntax: `data Name:` + indented constructors (vs `data Nat : ? where`).
  # Each constructor is a `proc` (valid Nim), converted to `| ctor : Ty`.
  data(Nat, Univ):
    proc zero(): Nat
    proc suc(n: Nat): Nat

  # Parameterized data: [A: Univ] is the telescope (vs `(A : ?)` in Eponym).
  # `Nat -> Univ` is the kind (vs `Nat -> ?`); `->` is valid Nim infix.
  data(Vec, [A: Univ], Nat -> Univ):
    # `vecnil` because `nil` is a Nim keyword; maps to Eponym `nil`.
    # Backticks (`` `nil` ``) also work but `vecnil` is clearer.
    proc vecnil(): Vec(A, zero())
    # `Vec(A, n)` is call syntax for type application (vs `Vec A n`).
    proc cons(n: Nat, x: A, xs: Vec(A, n)): Vec(A, suc(n))

  # `proc` not `def`; `=` not `:=` — matches Nim.
  # `suc(suc(suc(zero())))` is call syntax; Eponym elaborates to unary Nat.
  proc three(): Nat = suc(suc(suc(zero())))
  proc two(): Nat = suc(suc(zero()))
  proc one(): Nat = suc(zero())

  # Build a 3-element vector. Return type `Vec(Int, three())` is checked:
  # the body must construct exactly 3 `cons` cells ending in `vecnil`.
  # `cons(Int, two(), a, ...)` — first arg is the type parameter (Eponym: `cons Int ...`).
  proc mkVec3(a: Int, b: Int, c: Int): Vec(Int, three()) =
    cons(Int, two(), a, cons(Int, one(), b, cons(Int, zero(), c, vecnil(Int))))

  # 3-element dot product. The `let` bindings build `Vec Int 3` values,
  # proving at the type level that arity matches (3 weights, 3 inputs).
  # Nim `let` in proc body becomes Eponym `let ... in ...` (expression).
  proc dot3(w1: Int, w2: Int, w3: Int, x1: Int, x2: Int, x3: Int): Int =
    let ws = mkVec3(w1, w2, w3)
    let xs = mkVec3(x1, x2, x3)
    # `addInt(a, b)` call syntax; Eponym: `addInt a b`. Nested calls get parens.
    addInt(addInt(mulInt(w1, x1), mulInt(w2, x2)), mulInt(w3, x3))

# --- Normal Nim program ----------------------------------------------
# Plain Nim from here: IO, config, orchestration. No dependent types needed.
# The verified `dot3` above is called like any Nim proc.

proc readSensor(id: int): int =
  case id
  of 1: 100
  of 2: 150
  of 3: 200
  else: 0

proc main() =
  let w1 = 2; let w2 = 3; let w3 = 5
  let x1 = readSensor(1); let x2 = readSensor(2); let x3 = readSensor(3)

  echo "Sensor readings: ", x1, ", ", x2, ", ", x3
  echo "Weights: ", w1, ", ", w2, ", ", w3

  # Verified: dot3's ettBlock was elaborated at compile time.
  # The `Vec(Int, three())` types ensure the implementation builds
  # 3-element vectors; a 2-element bug would be a type error.
  let fused = dot3(w1, w2, w3, x1, x2, x3)
  echo "Fused result: ", fused  # 1650

  if fused > 1000: echo "Threshold exceeded!"
  else: echo "Within normal range."

when isMainModule:
  main()
