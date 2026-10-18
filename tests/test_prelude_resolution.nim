## Installed package prelude fallback with nested source-relative imports.

import eponym_mac
import eponym_embed

eponymBlock:
  import "schemes.ep"
  proc installedPreludeZero(): Nat = 0

when isMainModule:
  doAssert installedPreludeZero() == 0
  echo "test_prelude_resolution: package prelude fallback passed"
