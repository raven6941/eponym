## Explicit Nat-to-Int conversion across the checked runtime boundary.

import falsify
import eponym_mac
import eponym_embed

proc hostPlusSeven(value: int): int = value + 7

eponymRuntimeBridgeTestBlock:
  import "../lib/nat_to_int.ep"
  postulate(addHostOffset, Int -> Int)
  bindPostulate(addHostOffset, hostPlusSeven)
  proc convertNatThenCallHost(value: Nat): Int =
    addHostOffset(natToInt(value))

when isMainModule:
  var rng = initRng(20261021'u64)
  var negativeNatRejected = false
  try:
    discard convertNatThenCallHost(-1)
  except ValueError:
    negativeNatRejected = true
  let conversionFeedsAnIntPostulate = forAll("Nat to Int postulate bridge",
    rng, 200,
    proc(r: var Rng): int = r.genInt(0, 100),
    proc(value: int): bool = convertNatThenCallHost(value) == value + 7,
    shrinkInt)
  if not negativeNatRejected or not conversionFeedsAnIntPostulate:
    quit(1)
  echo "test_nat_to_int: postulate bridge property passed"
