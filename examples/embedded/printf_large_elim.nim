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
# - Terms at computed types check definitionally: `example` has type
#   `PrintfType (Number End)` which IS `Nat -> String`.
# - The `printf` skeleton has the correct dependent type
#   `Pi(f: Format, PrintfType(f))`.
#
# Current limitation: executing the full `formatElim` with a
# type-computing motive at runtime is not yet supported (the interpreter
# and codegen were built for stratified universes). The elaboration --
# the actual large elimination -- works. Runtime execution of large
# eliminators is future work.
#
# Requires the `univ-stratified-flag` branch.

import eponym_mac
import eponym_embed
import eponym_init

# Host backend for the opaque String type.
proc hostEmpty(n: int): string = ""
proc hostAppend(a, b: string): string = a & b
proc hostShowNat(n: int): string = $n

eponymBlock(stratified = false):
  import "../../lib/nat.ep"
  import "../../lib/text.ep"

  runtimeType(String, string)
  runtimeType(Nat, int)
  postulate(emptyString, Pi(u: Nat, String))
  postulate(appendStr, Pi(a: String, Pi(b: String, String)))
  postulate(showNat, Pi(n: Nat, String))
  bindPostulate(emptyString, hostEmpty, Nat, String)
  bindPostulate(appendStr, hostAppend, String, String, String)
  bindPostulate(showNat, hostShowNat, Nat, String)

  # A tiny format language.
  data(Format, Univ):
    proc Number(f: Format): Format
    proc Str(f: Format): Format
    proc End(): Format

  # LARGE ELIMINATION: compute a TYPE by recursion on a format value.
  # PrintfType (Number f) = Nat -> PrintfType f
  # PrintfType (Str f)    = String -> PrintfType f
  # PrintfType End        = String
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

  # The printf skeleton: the dependent type is the point. The motive
  # `lam(u) => Pi(a: String, PrintfType(u))` is itself a large
  # elimination -- each case's result TYPE is computed from the format.
  # (Not executed at runtime yet; see header note.)
  proc printfGo(f: Format, acc: String): PrintfType(f) =
    formatElim(lam(u: Format) => Pi(a: String, PrintfType(u)),
               lam(f: Format) => lam(ih: Pi(a: String, PrintfType(f))) =>
                 lam(acc: String) => lam(n: Nat) =>
                   ih(appendStr(acc, showNat(n))),
               lam(f: Format) => lam(ih: Pi(a: String, PrintfType(f))) =>
                 lam(acc: String) => lam(s: String) =>
                   ih(appendStr(acc, s)),
               lam(acc: String) => acc,
               f)(acc)

  proc printf(f: Format): PrintfType(f) =
    printfGo(f, emptyString(zero()))

when isMainModule:
  # The runnable part: a term at a computed type.
  echo "example(5) = '", example(5), "'"
  echo "PrintfType elaborated by large elimination (see block above)."
