## The legacy call-style explicit-parameter spelling gets a migration warning,
## while ordinary value calls keep working without a warning.

import os
import osproc
import strutils

const fixture = "tests/fixtures/embedded_legacy_explicit_params.nim"
let outputPath = getTempDir() / "eponym-legacy-explicit-params"
let cachePath = getTempDir() / "eponym-legacy-explicit-params-cache"
let command = "nim c --hints:off --path:src --path:src/eponym --nimcache:" &
  quoteShell(cachePath) & " --out:" & quoteShell(outputPath) & " " &
  quoteShell(fixture)
let (output, exitCode) = execCmdEx(command)
if exitCode != 0:
  quit("legacy syntax fixture failed to compile:\n" & output, 1)
let termDiagnostic = "call-style explicit parameters are deprecated"
let typeDiagnostic = "call-style explicit type/index arguments are deprecated"
if output.count(termDiagnostic) != 5 or output.count(typeDiagnostic) != 2:
  quit("expected five term and two type-application warnings, with no " &
    "warning for ordinary value calls:\n" & output, 1)
echo "test_embedded_legacy_syntax: explicit-parameter migration warning passed"
