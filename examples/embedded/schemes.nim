# Recursion schemes deforestation demo, embedded (Issue #48 / #144).
#
# The library is lib/schemes.ep: `cata`/`ana` combinators over the generated
# eliminators, with fusion laws as checked propositions. This file
# demonstrates deforestation end to end, in embedded Eponym.
#
# Unfused: build an intermediate list with the anamorphism `replicate`,
# then consume it with the fold `length`.
# Fused: a single pass over the fuel, no intermediate list.
# The lemma `deforestDemo` connects them — and it is discharged by `refl`,
# which typechecks only because the elaborator normalizes *both* sides to
# `suc (suc zero)`: both programs genuinely evaluate to the same result.
# The general law is `deforestLenRep` in lib/schemes.ep.
#
# Two-layer shape: the proof layer (the eponymBlock below) is checked at
# compile time by the elaborator; the running layer is plain Nim.

import eponym_mac
import eponym_embed

eponymBlock:
  import "../../lib/schemes.ep"

  proc two(): Nat =
    suc(suc(zero()))

  # Unfused: ana then cata, via the intermediate 2-list
  #   cons[Nat, 1](suc zero, cons[Nat, 1](suc zero, nil[Nat]())).
  proc unfused(): Nat =
    length[Nat](replicate[Nat](two(), suc(zero())))

  # Fused: one pass, no intermediate list.
  proc fused(): Nat =
    fusedLenRep(two())

  # Both evaluate to suc (suc zero); `refl` proves it.
  proc deforestDemo(): Eq[Nat, unfused(), fused()] =
    refl[Nat](unfused())

  # The same story for map fusion: two passes become one, by the checked
  # law `cataMapFusion` (lib/schemes.ep). Here the algebra is `length`'s,
  # so mapping then measuring is measuring directly.
  proc mapThenLength(xs: List[Nat]): Eq[Nat, length[Nat](map[Nat, Nat](suc, xs)),
      length[Nat](xs)] =
    cataMapFusion[Nat, Nat](lam(u: List[Nat]) => Nat, zero(), lam(x: Nat) => lam(tl: List[
        Nat]) => lam(ih: Nat) => suc(ih), suc, xs)

# --- Normal Nim program ------------------------------------------------
# Plain Nim from here: IO, config, orchestration. The deforestation
# lemmas above were checked at compile time; `deforestDemo` typechecks
# only because the elaborator evaluates both `unfused` and `fused` to
# `suc (suc zero)`.

proc main() =
  echo "schemes: deforestation demo elaborated at compile time."
  echo "deforestDemo : Eq Nat unfused fused  -- checks out (both sides normalize)."
  echo "mapThenLength  -- checked by the cataMapFusion law from lib/schemes.ep."

when isMainModule:
  main()
