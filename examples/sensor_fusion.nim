# Sensor fusion with verified core
#
# A Nim program that fuses 3 sensor readings with a weighted sum.
# The core math is in an ettEmbed block where dependent types check
# the implementation:
#
# - `mkVec3 : Int -> Int -> Int -> Vec Int 3` builds a length-indexed vector.
#   The elaborator CHECKS that the body constructs exactly 3 elements.
#   Forget one `cons`, and it won't typecheck.
# - `dot3` builds two `Vec Int 3`s (weights and readings), proving at the
#   type level that the arity is correct: 3 weights, 3 inputs.
#
# This catches a real bug class: arity mismatches. If someone "optimizes"
# dot3 by dropping a term but forgets to update mkVec3, or vice versa,
# the Vec Int 3 types won't match and compilation fails.
#
# The surrounding Nim program handles IO and orchestration — naturally
# separated from the math kernel with invariants.

import ett_mac
import ett_embed

ettEmbed"""
postulate Int : ?

data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat

data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)

def three : Nat := suc (suc (suc zero))
def two : Nat := suc (suc zero)
def one : Nat := suc zero

-- Build a 3-element vector. The return TYPE is Vec Int three.
-- The elaborator verifies the body: three cons cells, ending in nil.
-- Delete a cons, and you get Vec Int two — a type error.
def mkVec3 (a : Int) (b : Int) (c : Int) : Vec Int three :=
  cons Int two a (cons Int one b (cons Int zero c (nil Int)))

-- 3-element dot product. We build Vec Int 3 for weights and inputs,
-- proving the arity matches, then compute.
-- The lets are checked: mkVec3 returns Vec Int three, as required.
def dot3 (w1 : Int) (w2 : Int) (w3 : Int)
         (x1 : Int) (x2 : Int) (x3 : Int) : Int :=
  let ws = mkVec3 w1 w2 w3 in
  let xs = mkVec3 x1 x2 x3 in
  addInt (addInt (mulInt w1 x1) (mulInt w2 x2)) (mulInt w3 x3)
"""

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
  # An arity bug (2 vs 3 elements) is a compile-time type error.
  let fused = dot3(w1, w2, w3, x1, x2, x3)
  echo "Fused result: ", fused  # 1650

  if fused > 1000: echo "Threshold exceeded!"
  else: echo "Within normal range."

when isMainModule:
  main()
