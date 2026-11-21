## Focused coverage for flat equality chains (#569, phase 2).

import eponym_mac

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/bool.ep"
  import "../lib/calc.ep"

  proc natCong(x: Nat): Eq Nat (suc(x)) (suc(x)) =
    cong[Nat, Nat](lam(n: Nat) => suc(n), x, x, refl[Nat](x))

  proc natSym(x: Nat): Eq Nat (suc(x)) (suc(x)) =
    sym[Nat](suc(x), suc(x), refl[Nat](suc(x)))

  proc checkCalc2(): Eq Nat (suc(zero())) (suc(zero())) =
    calc2[Nat](suc(zero()), suc(zero()), suc(zero()),
      natCong(zero()), natSym(zero()))

  proc checkCalc3(): Eq Nat (suc(zero())) (suc(zero())) =
    calc3[Nat](suc(zero()), suc(zero()), suc(zero()), suc(zero()),
      natSym(zero()), natCong(zero()), natSym(zero()))

  proc boolCong(b: Bool): Eq Bool b b =
    cong[Bool, Bool](lam(x: Bool) => x, b, b, refl[Bool](b))

  proc checkCalc4(): Eq Bool true true =
    calc4[Bool](true, true, true, true, true,
      boolCong(true), sym[Bool](true, true, refl[Bool](true)),
      boolCong(true), sym[Bool](true, true, refl[Bool](true)))

  compileTimeOnly(natCong)
  compileTimeOnly(natSym)
  compileTimeOnly(checkCalc2)
  compileTimeOnly(checkCalc3)
  compileTimeOnly(boolCong)
  compileTimeOnly(checkCalc4)
