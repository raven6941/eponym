## Issue #133: sheds — hole-tolerant elaboration with imports + sidecar IO.
##
## Headless tests (no editor): elabCheckHolesDir (the #58 hole-tolerant
## semantics combined with #131 import resolution, as used by the
## shedsBlock macro) and the sidecar JSON round-trip the LSP server
## (issues #134/#135) will read. The macro itself is exercised by
## examples/embedded/sheds_demo.nim (compile + run).
import os
import strutils
import elab
import sheds

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

# --- elabCheckHolesDir: holes + imports ---------------------------------
# A source with a hole and a prelude import elaborates hole-tolerantly;
# imports resolve relative to baseDir.
let srcHoles = """import "../../lib/nat.ep"
postulate Int : ?
proc double (x : Int) : Int = x
proc quad (n : Int) : Int = _
"""
block:
  let (defs, ms, errLoc, errMsg) =
    elabCheckHolesDir(srcHoles, "examples/embedded")
  check(errMsg == "", "holes+import: no error, got: " & errMsg)
  check(ms.holes.len == 1, "holes+import: one hole recorded")
  check(ms.holes[0].holeLoc.line == 4, "holes+import: hole on line 4")
  check(defs.len == 2, "holes+import: both proc defs returned " &
    "(postulates register in globals, no ElabDef)")

# --- elabCheckHolesDir: stops at the first non-hole failure -------------
# The hole before the failure stays queryable (the #58 prefix property).
let srcBad = """postulate Int : ?
proc quad (n : Int) : Int = _
proc broken (x : Int) : Nat = x
"""
block:
  let (defs, ms, errLoc, errMsg) = elabCheckHolesDir(srcBad, ".")
  check(errMsg != "", "non-hole failure: error reported")
  check(ms.holes.len == 1, "non-hole failure: earlier hole kept")
  check(defs.len == 1, "non-hole failure: only the good prefix returned")

# --- elabCheckHolesDir: missing import is still an error ------------------
block:
  let (_, _, _, errMsg) =
    elabCheckHolesDir("import \"nope.ep\"\n", ".")
  check(errMsg.contains("file not found"), "missing import: error, got: " & errMsg)

# --- sidecar round-trip ---------------------------------------------------
block:
  let dir = getTempDir() / "sheds_test"
  createDir(dir)
  let nimFile = dir / "demo.nim"
  writeFile(nimFile, "-- placeholder")
  let shedsIn = @[ShedInfo(name: "quadBody", draft: "n ++++ n",
                           nimLine: 35, nimCol: 27,
                           holeLine: 5, holeIdx: 0,
                           goal: "R134", ctx: @["n : R134"])]
  writeShedSidecar(nimFile, shedsIn)
  let path = sidecarPath(nimFile)
  check(fileExists(path), "sidecar written to " & path)
  let shedsOut = readShedSidecar(path)
  check(shedsOut.len == 1 and shedsOut[0].name == "quadBody",
    "sidecar round-trip: name")
  check(shedsOut[0].draft == "n ++++ n" and shedsOut[0].holeIdx == 0 and
        shedsOut[0].ctx == @["n : R134"],
    "sidecar round-trip: draft/holeIdx/ctx")
  # Name-keyed merge: recompiling the same shed updates, not duplicates.
  var shedsIn2 = shedsIn
  shedsIn2[0].nimLine = 40  # edit shifted the shed down
  writeShedSidecar(nimFile, shedsIn2)
  let shedsOut2 = readShedSidecar(path)
  check(shedsOut2.len == 1 and shedsOut2[0].nimLine == 40,
    "sidecar merge: recompile updates the named entry")
  removeDir(dir)

if failures > 0:
  echo failures, " failure(s)"
  quit(1)
echo "--- all sheds tests passed ---"
