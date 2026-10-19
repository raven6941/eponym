# Sensor fusion with verified core (eponymBlock version)
#
# A Nim program that fuses 3 sensor readings with a weighted sum.
# The core math is in an eponymBlock where dependent types check the
# implementation — no """ string delimiter needed!
#
# - `mkVec3` builds a `Vec Int three`; the elaborator CHECKS the body
#   constructs exactly 3 elements.
# - `dot3` builds two `Vec Int three`s, proving arity matches.
#
# Nim-friendly forms used here (with Eponym equivalents):
# - `eponymBlock:` — block macro, no """ string: the single embedding form
#   (the old ettEmbed"""...""" string form was dropped in Issue #115)
# - `proc` — Nim keyword (Eponym string syntax also uses `proc` now, was `def`)
# - `=` — Nim definition (was `:=` in old Eponym syntax)
# - `postulate(Int, Univ)` — call syntax; `Univ` stands for `Type 0` (`Type 0` isn't valid Nim)
# - `import "../../lib/nat.ep"` — Eponym-module import (issue #131), resolved
#   relative to this file's directory; pulls in Nat/Vec/etc. from the prelude
#   instead of redefining them per file (`data(Nat, Univ):` block syntax still
#   works for local datatypes)
# - `Vec(A, zero())` — call syntax for type application (vs `Vec A zero`)
# - `vecnil` — Nim keyword workaround; maps to Eponym `nil` constructor
# - `Nat -> Univ` — infix `->` for Pi types (valid Nim, right-associative)
#
# The surrounding Nim program handles IO and orchestration.

import eponym_mac
import eponym_embed

# eponymBlock: takes a Nim AST block (not a string). No """ delimiter.
# Each proc/data/postulate is converted to Eponym source at compile time,
# elaborated, and wrapped as a callable Nim proc.
eponymBlock:
  # Prelude import (issue #131): Nat/Vec (+ zero, suc, nil, cons, add, vappend,
  # ...) from lib/vec.ep (which pulls in lib/nat.ep and lib/eq.ep). This
  # replaces the per-file data(Nat, ...)/data(Vec, ...) redefinitions.
  import "../../lib/vec.ep"

  # postulate(Int, Univ): declares primitive Int type.
  # Call syntax because `postulate Int : Type 0` isn't valid Nim (`Type 0` doesn't parse).
  # `Univ` is the Nim-friendly spelling of Eponym's `Type 0` (the universe).
  postulate(Int, Univ)

  # `proc` not `def`; `=` not `:=` — matches Nim.
  # Integer literals for Nat: write `3`, not `suc(suc(suc(zero())))`.
  # Literals overload against the expected type (Issue #115): `3` in a
  # Nat position elaborates as a Nat literal, in an Int position (e.g.
  # `addInt(mulInt(2, x), 3)`) as a primitive Int literal — the same
  # semantics as string syntax. (Exception: `1` is the unit type in
  # surface syntax, so the Nat literal one is written `suc(zero())`.)

  # Build a 3-element vector. Return type `Vec(Int, 3)` uses Nat literal.
  # The body constructs 3 `cons` cells with Nat literal indices.
  proc mkVec3(a: Int, b: Int, c: Int): Vec[Int, 3] =
    cons[Int, 2](a, cons[Int, 1](b, cons[Int, 0](c, vecnil[Int]())))

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

  # Verified: dot3's eponymBlock was elaborated at compile time.
  # The `Vec(Int, three())` types ensure the implementation builds
  # 3-element vectors; a 2-element bug would be a type error.
  let fused = dot3(w1, w2, w3, x1, x2, x3)
  echo "Fused result: ", fused  # 1650

  if fused > 1000: echo "Threshold exceeded!"
  else: echo "Within normal range."

when isMainModule:
  main()
