## Fixture for tests/test_embedded_error_path.nim (issue #500).
## A `stratified = false` block whose definitions have no runtime
## representation must FAIL LOUDLY under #490's strict default -- no
## silent interpreter fallback, no skipped emission. The `printf`
## skeleton's type `Pi(f: Format, PrintfType(f))` is computed by large
## elimination, so Phase 2 codegen has no representation mapping for it.
## Expected: "eponymBlock requireCompiled: definition 'printf' has no
## representation-compiled body".
import eponym_mac
import eponym_embed
import eponym_init

eponymBlock(stratified = false):
  import "../../lib/nat.ep"
  import "../../lib/text.ep"

  runtimeType(String, string)
  runtimeType(Nat, int)
  postulate(emptyString, Pi(u: Nat, String))
  postulate(appendStr, Pi(a: String, Pi(b: String, String)))
  postulate(showNat, Pi(n: Nat, String))

  data(Format, Univ):
    proc Number(f: Format): Format
    proc Str(f: Format): Format
    proc End(): Format

  proc PrintfType(f: Format): Univ =
    formatElim(lam(u: Format) => Univ,
               lam(f: Format) => lam(ih: Univ) => Pi(n: Nat, ih),
               lam(f: Format) => lam(ih: Univ) => Pi(s: String, ih),
               String,
               f)

  # The printf skeleton: the dependent type is the point, and it
  # elaborates fine (large elimination works). But the computed result
  # type has no runtime representation mapping, so the strict default
  # rejects it here instead of falling back.
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
