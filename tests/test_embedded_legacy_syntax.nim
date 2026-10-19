## Bracket applications compile, while removed call-style explicit-parameter
## applications fail and ordinary value calls remain available.

import os
import osproc
import strutils

proc compileFixture(fixture, suffix: string):
    tuple[output: string, exitCode: int] =
  let outputPath = getTempDir() / ("eponym-explicit-params-" & suffix)
  let cachePath = getTempDir() / ("eponym-explicit-params-cache-" & suffix)
  let command = "nim c --hints:off --path:src --path:src/eponym --nimcache:" &
    quoteShell(cachePath) & " --out:" & quoteShell(outputPath) & " " &
    quoteShell(fixture)
  execCmdEx(command)

let (positiveOutput, positiveCode) = compileFixture(
  "tests/fixtures/embedded_explicit_params.nim", "positive")
if positiveCode != 0:
  quit("bracket syntax fixture failed to compile:\n" & positiveOutput, 1)

for fixture in [
    "tests/fixtures/embedded_err_legacy_explicit_params.nim",
    "tests/fixtures/embedded_err_legacy_type_application.nim",
    "tests/fixtures/embedded_err_legacy_nat_let.nim",
    "tests/fixtures/embedded_err_legacy_nat_if.nim",
    "tests/fixtures/embedded_err_legacy_postulate_index.nim",
    "tests/fixtures/embedded_err_legacy_local_postulate.nim",
    "tests/fixtures/embedded_err_legacy_field_application.nim",
    "tests/fixtures/embedded_err_legacy_command_application.nim"]:
  let (legacyOutput, legacyCode) = compileFixture(fixture, fixture.splitFile.name)
  if legacyCode == 0 or "call-style explicit" notin legacyOutput or
      "have been removed" notin legacyOutput:
    quit("legacy explicit-parameter syntax was not rejected:\n" &
      legacyOutput, 1)

echo "test_embedded_legacy_syntax: bracket syntax accepted; legacy term and type syntax rejected"
