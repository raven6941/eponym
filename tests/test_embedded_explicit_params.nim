## Nim square-bracket syntax for explicit Eponym binders and applications.

import eponym_mac

eponymBlock:
  import "../lib/vec.ep"

  proc myAppend[A: Univ, n: Nat](x: A, xs: Vec[A, n]): Vec[A, suc(n)] =
    cons[A, n](x, xs)

  proc useAppend(x: Nat, xs: Vec[Nat, 0]): Vec[Nat, 1] =
    myAppend[Nat, 0](x, xs)

  proc appendTwo(xs: Vec[Nat, suc(zero())],
                 ys: Vec[Nat, suc(zero())]):
      Vec[Nat, add(suc(zero()), suc(zero()))] =
    vappend[Nat, suc(zero()), suc(zero())](xs, ys)

when isMainModule:
  echo "test_embedded_explicit_params: square-bracket Eponym binders passed"
