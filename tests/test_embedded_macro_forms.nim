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
import elab
import macros
import strutils

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

eponymBlock:
  # --- PHOAS surface (issue #40): host lambdas as binders ---
  # The lambda closes over the enclosing proc scope (host scoping); the
  # parenthesized emission keeps immediate application outside the body.
  postulate(NatP, Univ)
  postulate(zeroP, NatP)
  postulate(sucP, NatP -> NatP)
  proc twiceP(f: NatP -> NatP, x: NatP): NatP =
    phoasLam(proc (g: NatP -> NatP): NatP = g (g x))(f)
  proc shadowP(x: NatP): (NatP -> NatP) -> NatP -> NatP =
    phoasLam(proc (x: NatP -> NatP): NatP -> NatP =
      phoasLam(proc (y: NatP): NatP = x y))

  # --- erased binder on phoasLam (issue #40): round-trips as (0e : NatP) ---
  proc erasedConst(): NatP =
    phoasLam(proc (e {.erased.}: NatP): NatP = zeroP)(zeroP)

eponymBlock:
  # --- PHOAS breakdown cases (issue #40): all benign ---
  # (each eponymBlock is scope-independent, hence the local postulates)
  postulate(BoolB, Univ)
  postulate(trueB, BoolB)
  postulate(falseB, BoolB)
  elim(boolElimB, Pi(C: BoolB -> Univ, C(trueB) -> C(falseB) -> Pi(b: BoolB, C(b))))
  red(boolElimB(C, t, f, trueB), t)
  red(boolElimB(C, t, f, falseB), f)
  # 1. Pattern analysis under a host binder: the bound variable is
  #    scrutinized by an eliminator (patterns-as-elim under lam).
  proc notPH(b: BoolB): BoolB =
    phoasLam(proc (x: BoolB): BoolB =
      boolElimB(lam(u, BoolB, BoolB), falseB, trueB, x))(b)
  # 2. phoasLam in a clause RHS, capturing the pattern variable: the
  #    pattern binder is textually in scope in the emitted source.
  data(NatQ, Univ):
    proc zeroQ(): NatQ
    proc sucQ(n: NatQ): NatQ
  def(capQ, NatQ -> NatQ):
    clause([zeroQ], zeroQ)
    clause([sucQ(n)], phoasLam(proc (f: NatQ -> NatQ): NatQ = f n)(sucQ))
  # 3. A hole `_` in a phoasLam body is a real elaborator hole: it fails
  #    with the standard located "unsolved metavariable" error (verified
  #    in scratch; same message class as the string surface), so it
  #    cannot live in this compile-time test. Recorded in decisions.org.

when isMainModule:
  echo "test_embedded_macro_forms: embedded 07/08/14 + def/qvar/unit elaborated at compile time"

  # --- PHOAS error parity (issue #40, acceptance criterion 3) -----------------
  # An ill-typed phoasLam term must fail with the same *located* error as its
  # string-surface twin: the macro attaches elaboration errors to the host
  # block (error(msg, body) in eponymBlock), and the message itself carries a
  # "line L, col C" location in the elaborator's standard format — not an
  # unlocated crash and not a message class the string surface never emits.
  # Run at compile time (static:) so `quote do:` can build the host AST.
  static:
    # parseStmt (not `quote do:`): quote hygienically gensyms the binder and
    # the Eponym lexer rejects backticks; the real macro path never sees
    # gensyms, so build the AST the way the compiler does.
    let node = parseStmt("phoasLam(proc (x: Nat): Bool = x)")
    let gen = phoasLamToEponym(node[0][1])  # parseStmt wraps in nnkStmtList
    # Pin the generator output exactly, plus binder consistency.
    doAssert gen == "(lam (x : Nat). (x : Bool))",
      "phoasLam generator output changed: " & gen
    let prog = "postulate Nat : ?\npostulate Bool : ?\nproc bad : Nat = " &
      gen & "\n"
    var msg1 = ""
    try:
      discard elabCheckDir(prog, ".")
    except ElabError as e:
      msg1 = e.msg
    doAssert msg1.len > 0, "expected ElabError from ill-typed PHOAS program"
    doAssert "line " in msg1,
      "PHOAS elaboration error lacks a source location: " & msg1
    # Hand-written string-surface twin: byte-identical elaboration input
    # must give a byte-identical error.
    let twin = "postulate Nat : ?\npostulate Bool : ?\n" &
      "proc bad : Nat = (lam (x : Nat). (x : Bool))\n"
    var msg2 = ""
    try:
      discard elabCheckDir(twin, ".")
    except ElabError as e:
      msg2 = e.msg
    doAssert msg1 == msg2, "PHOAS error differs from string-surface twin:\n" &
      msg1 & "\nvs\n" & msg2
  echo "ok: phoasLam error parity — located error identical to string twin"
