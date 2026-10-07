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
# The ettBlock uses Nim-block syntax (valid Nim AST):
#   proc add42(n: Int): Int = addInt(n, 42)
#   postulate(Int, Univ)
#   data(Nat, Univ):
#     proc zero(): Nat
#
# The surrounding Nim program handles IO and orchestration.

import ett_mac
import ett_embed

ettBlock:
  postulate(Int, Univ)

  data(Nat, Univ):
    proc zero(): Nat
    proc suc(n: Nat): Nat

  data(Vec, [A: Univ], Nat -> Univ):
    proc vecnil(): Vec(A, zero())
    proc cons(n: Nat, x: A, xs: Vec(A, n)): Vec(A, suc(n))

  proc three(): Nat = suc(suc(suc(zero())))
  proc two(): Nat = suc(suc(zero()))
  proc one(): Nat = suc(zero())

  # Build a 3-element vector. The return TYPE is Vec(Int, three()).
  # The elaborator verifies the body: three cons cells, ending in nil.
  proc mkVec3(a: Int, b: Int, c: Int): Vec(Int, three()) =
    cons(Int, two(), a, cons(Int, one(), b, cons(Int, zero(), c, vecnil(Int))))

  # 3-element dot product. We build Vec Int 3 for weights and inputs,
  # proving the arity matches, then compute.
  proc dot3(w1: Int, w2: Int, w3: Int, x1: Int, x2: Int, x3: Int): Int =
    let ws = mkVec3(w1, w2, w3)
    let xs = mkVec3(x1, x2, x3)
    addInt(addInt(mulInt(w1, x1), mulInt(w2, x2)), mulInt(w3, x3))

# --- Normal Nim program ----------------------------------------------

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

  # Verified: dot3 builds Vec Int 3 twice (checked), then computes.
  let fused = dot3(w1, w2, w3, x1, x2, x3)
  echo "Fused result: ", fused  # 1650

  if fused > 1000: echo "Threshold exceeded!"
  else: echo "Within normal range."

when isMainModule:
  main()
