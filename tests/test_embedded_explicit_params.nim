## Nim square-bracket syntax for explicit Eponym binders and applications.

import eponym_mac

eponymBlock:
  import "../lib/vec.ep"
  postulate(Int, Univ)

  data(NatBox, [n: Nat], Univ):
    proc natBox(): NatBox[n]

  proc myAppend[A: Univ, n: Nat](x: A, xs: Vec[A, n]): Vec[A, suc(n)] =
    cons[A, n](x, xs)

  proc useAppend(x: Nat, xs: Vec[Nat, 0]): Vec[Nat, 1] =
    myAppend[Nat, 0](x, xs)

  proc useAppendOne(x: Nat, xs: Vec[Nat, 1]): Vec[Nat, 2] =
    myAppend[Nat, 1](x, xs)

  proc appendTwo(xs: Vec[Nat, suc(zero())],
                 ys: Vec[Nat, suc(zero())]):
      Vec[Nat, add(suc(zero()), suc(zero()))] =
    vappend[Nat, suc(zero()), suc(zero())](xs, ys)

  proc twoLiteralVector(x, y: Nat): Vec[Nat, 2] =
    cons[Nat, 1](x, cons[Nat, 0](y, vecnil[Nat]()))

  proc appendLiteralVectors(xs, ys: Vec[Nat, 1]): Vec[Nat, add(1, 1)] =
    vappend[Nat, 1, 1](xs, ys)

  proc useNatBoxLiteral(): NatBox[1] = natBox[1]()

  proc intIndexed[index: Int](ignored: Int): Int = index
  proc useIntBracketOne(): Int = intIndexed[1](0)

when isMainModule:
  echo "test_embedded_explicit_params: square-bracket Eponym binders passed"
