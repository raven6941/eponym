## Chained pure if/elif/else branches lower to nested checked ifThenElse terms.

import eponym_mac

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/bool.ep"

  proc chooseThree(first: Bool, second: Bool): Nat =
    if first:
      zero()
    elif second:
      suc(zero())
    else:
      suc(suc(zero()))

when isMainModule:
  echo "test_embedded_chained_if: chained pure branches elaborated"
