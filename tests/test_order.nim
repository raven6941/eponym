## Focused coverage for the shared abstract order rules (#569).

import eponym_mac

eponymBlock:
  import "../lib/order.ep"

  proc reflRule(A: Univ, x: A): Le[A, x, x] =
    leRefl[A](x)
  proc transRule(A: Univ, x: A, y: A, z: A,
      p: Le[A, x, y], q: Le[A, y, z]): Le[A, x, z] =
    leTrans[A](x, y, z, p, q)
  proc antisymRule(A: Univ, x: A, y: A,
      p: Le[A, x, y], q: Le[A, y, x]): Eq[A, x, y] =
    leAntisym[A](x, y, p, q)
  proc ofEqRule(A: Univ, x: A, y: A, p: Eq[A, x, y]): Le[A, x, y] =
    leOfEq[A](x, y, p)

  compileTimeOnly(reflRule)
  compileTimeOnly(transRule)
  compileTimeOnly(antisymRule)
  compileTimeOnly(ofEqRule)
