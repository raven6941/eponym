# Dependent index telescopes, embedded (Issue #112 / #144).
#
# A later index's type may mention an earlier index binder:
# `data(All, [A: Univ, P: A -> Univ], Pi(n: Nat, Vec A n -> Univ))`.
# The generated eliminator renames index binders to i0, i1, ... and must
# substitute the old names into later index domains; without the #112 fix
# the motive C is ill-scoped (unbound `n`).
#
# Vec comes from the prelude (lib/vec.ep) via real import; only `All` is
# declared locally, since its dependent index telescope is the point of
# the demo.
#
# Two-layer shape: the proof layer (the eponymBlock below) is checked at
# compile time by the elaborator; the running layer is plain Nim.

import eponym_mac
import eponym_embed

eponymBlock:
  # Prelude import (issue #131): Nat, Vec (+ zero, suc, nil, cons, ...)
  # from lib/vec.ep.
  import "../../lib/vec.ep"

  # The motivating case: index telescope `Pi(n: Nat, Vec A n -> Univ)` —
  # the second index's type mentions the first index binder `n`.
  data(All, [A: Univ, P: A -> Univ], Pi(n: Nat, Vec[A, n] -> Univ)):
    proc allNil(): All[A, P, zero(), vecnil[A]()]
    proc allCons(n: Nat, x: A, xs: Vec[A, n], px: P(x),
                 pxs: All[A, P, n, xs]): All[A, P, suc(n), cons[A, n](x, xs)]

  # A witness: every element of [1, 1] satisfies P (P = fun x => Nat).
  proc witness(): All[Nat, lam(x: Nat) => Nat, suc(suc(zero())),
                      cons[Nat, suc(zero())](suc(zero()),
                           cons[Nat, zero()](zero(), vecnil[Nat]()))] =
    allCons[Nat, lam(x: Nat) => Nat](suc(zero()), suc(zero()),
            cons[Nat, zero()](zero(), vecnil[Nat]()), suc(zero()),
            allCons[Nat, lam(x: Nat) => Nat](zero(), zero(), vecnil[Nat](),
                    zero(), allNil[Nat, lam(x: Nat) => Nat]()))

  # Eliminate the witness to compute the vector's length. The motive is
  # `lam (i : Nat). lam (w : Vec Nat i). lam (u : All Nat P i w). Nat`,
  # which is well-scoped only because the #112 fix substitutes the
  # renamed index binders into later index domains.
  proc allLen(n: Nat, v: Vec[Nat, n],
              a: All[Nat, lam(x: Nat) => Nat, n, v]): Nat =
    allElim[Nat, lam(x: Nat) => Nat](
            lam(i: Nat) => lam(w: Vec[Nat, i]) => lam(u: All[Nat, lam(x: Nat) => Nat, i, w]) => Nat,
            zero(),
            lam(i: Nat) => lam(x: Nat) => lam(xs: Vec[Nat, i]) => lam(px: Nat) => lam(pxs: All[Nat, lam(x: Nat) => Nat, i, xs]) => lam(ih: Nat) => suc(ih),
            n, v, a)

  # Sanity: the length of the 2-vector is 2.
  proc lenIsTwo(): Nat =
    allLen(suc(suc(zero())),
           cons[Nat, suc(zero())](suc(zero()),
                cons[Nat, zero()](zero(), vecnil[Nat]())),
           witness())

# --- Normal Nim program ------------------------------------------------
# Plain Nim from here. The dependent-index machinery above was checked at
# compile time; `allLen` computes through the generated eliminator.

proc main() =
  echo "dependent_indices: dependent index telescopes elaborated at compile time."
  echo "allLen : Pi(n: Nat, Pi(v: Vec Nat n, Pi(a: All Nat P n v, Nat)))  -- checks out."

when isMainModule:
  main()
