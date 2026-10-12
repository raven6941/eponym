## Embedded equivalents of smoke tests 07/08/14, plus def-clauses,
## quantity-variable binders, and the unit value (issue #151).
##
## eponymBlock can now emit every canonical surface form: elim/red
## declarations, `by` tactic terms, def clause-style definitions,
## quantity-variable binders `(q x : A)`, and the unit value/type. This file
## elaborates the embedded forms of examples/ep/07-bool-postulate.ep,
## examples/ep/08-nat-postulate.ep, and examples/ep/14-tactics.ep at
## compile time — the eponymBlock macro typechecks the generated source, so
## successful compilation IS the test.

import eponym_mac
import eponym_embed

eponymBlock:
  # --- smoke 07 embedded: Bool via postulate/elim/red ---
  postulate(Bool, Univ)
  postulate(true, Bool)
  postulate(false, Bool)
  elim(boolElim, Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b))))
  red(boolElim(C, t, f, true), t)
  red(boolElim(C, t, f, false), f)
  proc notFn(b: Bool): Bool =
    boolElim(lam(u, Bool, Bool), false, true, b)

  # --- smoke 08 embedded: Nat via postulate/elim/red ---
  postulate(Nat, Univ)
  postulate(zero, Nat)
  postulate(suc, Nat -> Nat)
  elim(natElim, Pi(C: Nat -> Univ,
                   C(zero) -> (Pi(n: Nat, C(n) -> C(suc(n)))) -> Pi(m: Nat, C(m))))
  red(natElim(C, z, s, zero), z)
  red(natElim(C, z, s, suc(n)), s(n, natElim(C, z, s, n)))
  proc two(): Nat = suc(suc(zero))
  proc addN(m: Nat, n: Nat): Nat =
    natElim(lam(u, Nat, Nat), m, lam(p, Nat, lam(ih, Nat, suc(ih))), n)

  # --- smoke 14 embedded: tactics ---
  postulate(Int, Univ)
  data(Eq, [A: Univ, x: A], A -> Univ):
    proc refl(): Eq(A, x, x)
  proc pf1(): Eq(Int, 42, 42) = byTac(refl)
  proc pf2(): Eq(Int, addInt(20, 22), 42) = byTac(refl)
  proc idInt(x: Int): Int = byTac(assumption)

eponymBlock:
  # --- def clause-style definitions need a `data` scrutinee (issue #32) ---
  data(NatD, Univ):
    proc zeroD(): NatD
    proc sucD(n: NatD): NatD
  def(isZeroD, NatD -> NatD):
    clause([zeroD], zeroD)
    clause([sucD(n)], zeroD)

  # --- quantity-variable binder (issue #66 / #151) ---
  proc qid(x {.qvar(q).}: Univ): Univ = x

  # --- unit value / unit type / empty type (issue #151) ---
  proc unitVal(): unitTy = unitv
  proc absurd(x: emptyTy): emptyTy = x

when isMainModule:
  echo "test_embedded_macro_forms: embedded 07/08/14 + def/qvar/unit elaborated at compile time"
