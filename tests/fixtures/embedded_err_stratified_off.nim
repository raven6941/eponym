## Fixture for tests/test_embedded_error_path.nim (issue #500).
## Large elimination WITHOUT the `stratified = false` flag. Compiling this
## file must FAIL: the motive `Format -> Univ` is `Type 1`, which does not
## fit the stratified `Univ` (`Type 0`). This is the negative half of the
## opt-in Type-in-Type flag: the default universe discipline rejects the
## program the flag accepts (see
## examples/embedded/printf_large_elim.nim for the positive case).
import eponym_mac
import eponym_embed
import eponym_init

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/text.ep"

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
