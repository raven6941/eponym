## Fixture for tests/test_embedded_error_path.nim (#569).
## The middle terms of this calc2 chain do not match.
import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/calc.ep"

  proc badCalc(): Eq Nat zero (suc(zero())) =
    calc2[Nat](zero(), zero(), suc(zero()),
      refl[Nat](zero()), refl[Nat](zero()))
