# Printf via large elimination (Issue #52 experiment).
#
# The canonical large-elimination demo from the Idris literature: a type
# computed by recursion on a VALUE. `PrintfType fmt` is the type of the
# printf function for the format `fmt` -- `Nat -> String -> String` for
# `Number (Str End)`, etc. This requires `Univ : Univ` (Type-in-Type),
# enabled per-block by `eponymBlock(stratified = false):`.
#
# What this demonstrates:
# - `PrintfType : Format -> Univ` defined by large elimination (recursion
#   on a Format value computing a type). This FAILS without the flag
#   (universe level mismatch: the motive `Format -> Univ` is `Type 1`).
# - Terms at computed types check definitionally: `exampleComputed` is
#   declared at the computed type `PrintfType (Number (End ()))`, which
#   IS `Nat -> String`, so the body checks. It is `compileTimeOnly` --
#   a family-typed definition has no runtime wrapper -- while `example`
#   at the concrete type `String` runs.
#
# Current limitation: a `printf` skeleton whose RESULT TYPE is computed
# by large elimination (`Pi(f: Format, PrintfType(f))`) elaborates fine
# but has no runtime representation mapping, so #490's strict default
# rejects it loudly at compile time ("no representation-compiled body")
# instead of falling back to an interpreter. See
# tests/fixtures/embedded_err_stratified_strict.nim for that negative
# case, and tests/fixtures/embedded_err_stratified_off.nim for the
# without-the-flag negative case.
#
# Requires the `univ-stratified-flag` branch.

import eponym_mac
import eponym_embed
import eponym_init

# Host backend for the opaque String type.
proc hostEmpty(n: int): string = ""

eponymBlock(stratified = false):
  import "../../lib/nat.ep"
  import "../../lib/text.ep"

  runtimeType(String, string)
  runtimeType(Nat, int)
  postulate(emptyString, Pi(u: Nat, String))
  bindPostulate(emptyString, hostEmpty, Nat, String)

  # A tiny format language.
  data(Format, Univ):
    proc Number(f: Format): Format
    proc Str(f: Format): Format
    proc End(): Format

  # LARGE ELIMINATION: compute a TYPE by recursion on a format value.
  # PrintfType (Number f) = Nat -> PrintfType f
  # PrintfType (Str f)    = String -> PrintfType f
  # PrintfType End        = String
  #
  # A type family has no runtime representation, so under #490's strict
  # default it is marked compileTimeOnly: checked at compile time, no
  # runtime API emitted (#401's compile-time-only classification).
  compileTimeOnly(PrintfType)
  proc PrintfType(f: Format): Univ =
    formatElim(lam(u: Format) => Univ,
               lam(f: Format) => lam(ih: Univ) => Pi(n: Nat, ih),
               lam(f: Format) => lam(ih: Univ) => Pi(s: String, ih),
               String,
               f)

  # A term at a computed type. PrintfType (Number End) reduces
  # definitionally to Nat -> String, so this checks.
  proc example(n: Nat): String =
    (lam(n: Nat) => emptyString(zero()))(n)

  # A term whose DECLARED type is computed by large elimination:
  # PrintfType (Number (End ())) is definitionally Nat -> String, so the
  # lambda body checks against it. Family-typed definitions have no
  # runtime wrapper, hence compileTimeOnly; the elaboration -- the
  # actual large elimination -- is the check.
  compileTimeOnly(exampleComputed)
  proc exampleComputed(n: Nat): PrintfType(Number(End())) =
    lam(m: Nat) => emptyString(m)

when isMainModule:
  # The runnable part: a term at a computed type.
  echo "example(5) = '", example(5), "'"
  echo "PrintfType elaborated by large elimination (see block above)."
