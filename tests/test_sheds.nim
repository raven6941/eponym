## Issue #133: sheds — hole-tolerant elaboration with imports + sidecar IO.
##
## Headless tests (no editor): elabCheckHolesDir (the #58 hole-tolerant
## semantics combined with #131 import resolution, as used by the
## eponymBlock macro, issue #478) and the sidecar JSON round-trip the LSP server
## (issues #134/#135) will read. The macro itself is exercised by
## examples/embedded/sheds_demo.nim (compile + run).
import os
import strutils
import json  # JsonNode indexing in status assertions
import tables  # initTable (issue #134: LSP server in tests)
import elab
import sheds
import eponym_init  # issue #191: Term/tR for the R<n>-fallback test
import preterm  # q0/q1 quantity constructors (issue #377)
import lsp  # issue #134: shed diagnostics via handleMessage

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
postulate(Int, Univ)
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

# --- Issue #377: semantic hole state, not rendered text ----------------
block:
  let semanticSrc = """postulate(Int, Univ)
proc semanticHole (n : Int) : Pi(1 x: Int, Int) = _
"""
  let (_, ms, _, errMsg) = elabCheckHoles(semanticSrc)
  check(errMsg == "" and ms.holes.len == 1,
    "semantic shed: elaborates one typed hole, got: " & errMsg)
  if ms.holes.len == 1:
    let state = semanticShedState(ms, ms.holes[0])
    check(state.hole != nil and state.hole.kind == tMeta and
          state.goal.kind == tPi,
      "semantic shed: retains typed meta and zonked Pi goal terms")
    check(state.context.len == 1 and state.context[0].name == "n" and
          state.context[0].qty.isVar and
          state.context[0].qty.vname.len > 0,
      "semantic shed: context binder retains its unresolved quantity variable")
    check(state.goalPi.len == 1 and state.goalPi[0].name == "x" and
          state.goalPi[0].qty == q1 and state.residualGoal.kind == tR,
      "semantic shed: Pi spine is structured and preserves quantity")
    let hover = renderShedHover(ms, state)
    check(hover.contains("goal : Pi(Int, x. Int)") and
          hover.contains("n : Int"),
      "semantic shed: LSP hover is rendered from structured state, got: " &
        hover)

# --- elabCheckHolesDir: stops at the first non-hole failure -------------
# The hole before the failure stays queryable (the #58 prefix property).
let srcBad = """postulate(Int, Univ)
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

# --- Issue #134: shed status tracking --------------------------------------
# Status serializes in the sidecar; a missing key (pre-#134 sidecar)
# defaults to yellow (stuck), the safe "not known-good" state.
block:
  let s = ShedInfo(name: "q", draft: "", nimLine: 1, nimCol: 1,
                   holeLine: 2, holeIdx: 0, goal: "Int", ctx: @[],
                   status: ssBrown)
  check(shedFromJson(shedToJson(s)).status == ssBrown,
    "status round-trip: brown")
  check(shedToJson(s)["status"].getStr() == "brown",
    "status serializes as \"brown\"")
  let j = shedToJson(s)
  j.delete("status")
  check(shedFromJson(j).status == ssYellow,
    "status missing: defaults to yellow")
  check(shedStatusFromStr("white") == ssWhite and
        shedStatusFromStr("bogus") == ssYellow,
    "status parse: white ok, unknown -> yellow")

# refreshShedStatuses: the #137 editor loop, headless. A shed with an open
# hole is yellow; filling the hole (as the #58 refine action would) and
# re-elaborating turns it white; breaking the shed's own declaration so no
# goal is established turns it brown.
let srcOneHole = """postulate(Int, Univ)
proc quad (n : Int) : Int = _
"""
block:
  var sheds = @[ShedInfo(name: "quadBody", draft: "", nimLine: 7, nimCol: 25,
                         holeLine: 2, holeIdx: -1, goal: "", ctx: @[],
                         status: ssYellow)]
  refreshShedStatuses(sheds, srcOneHole, ".")
  check(sheds[0].status == ssYellow and sheds[0].holeIdx == 0,
    "open hole: yellow, matched to hole 0")
  let filled = srcOneHole.replace("= _", "= n")
  refreshShedStatuses(sheds, filled, ".")
  check(sheds[0].status == ssWhite and sheds[0].holeIdx == -1,
    "hole filled, clean elaboration: white")
  let broken = srcOneHole.replace("(n : Int)", "(n : Nope)")
  refreshShedStatuses(sheds, broken, ".")
  check(sheds[0].status == ssBrown,
    "shed decl fails before a goal is established: brown")
  let unparseable = srcOneHole.replace("proc", "proc proc")
  refreshShedStatuses(sheds, unparseable, ".")
  check(sheds[0].status == ssBrown,
    "unparseable document: brown")

# LSP: `.nim` documents get shed-status diagnostics from the sidecar --
# yellow -> Warning, brown -> Error (carrying the elaboration message),
# white -> no diagnostic. Re-read on every didOpen/didChange.
block:
  let dir = getTempDir() / "sheds_lsp_test"
  createDir(dir)
  let nimFile = dir / "demo.nim"
  writeFile(nimFile, "-- placeholder")
  let shedsIn = @[
    ShedInfo(name: "stuck", draft: "", nimLine: 10, nimCol: 5,
             holeLine: 3, holeIdx: 0, goal: "Int", ctx: @["n : Int"],
             status: ssYellow),
    ShedInfo(name: "bad", draft: "", nimLine: 20, nimCol: 5,
             holeLine: 0, holeIdx: -1, goal: "", ctx: @[],
             status: ssBrown),
    ShedInfo(name: "done", draft: "", nimLine: 30, nimCol: 5,
             holeLine: 0, holeIdx: -1, goal: "Int", ctx: @[],
             status: ssWhite)]
  writeShedSidecar(nimFile, shedsIn, "kaboom")
  var server = LspServer(documents: initTable[string, string]())
  let uri = "file://" & nimFile
  let resp = handleMessage(server, %*{
    "jsonrpc": "2.0", "method": "textDocument/didOpen",
    "params": {"textDocument": {"uri": uri, "text": "-- nim source"}}})
  check(resp["method"].getStr() == "textDocument/publishDiagnostics",
    "shed diagnostics: notification published on didOpen")
  let diags = resp["params"]["diagnostics"]
  check(diags.len == 2, "shed diagnostics: yellow+brown only, got " &
    $diags.len)
  check(diags[0]["severity"].getInt() == 2 and
        diags[0]["range"]["start"]["line"].getInt() == 9 and
        diags[0]["range"]["start"]["character"].getInt() == 4 and
        diags[0]["message"].getStr().contains("stuck (yellow)") and
        diags[0]["message"].getStr().contains("goal: Int"),
    "shed diagnostics: yellow warning at 10:5 with goal")
  check(diags[1]["severity"].getInt() == 1 and
        diags[1]["range"]["start"]["line"].getInt() == 19 and
        diags[1]["message"].getStr().contains("kaboom"),
    "shed diagnostics: brown error at 20:5 carrying the failure message")
  # didChange re-reads the sidecar: rewrite it all-white, expect silence.
  var shedsIn2 = shedsIn
  for i in 0 ..< shedsIn2.len: shedsIn2[i].status = ssWhite
  writeShedSidecar(nimFile, shedsIn2)
  let resp2 = handleMessage(server, %*{
    "jsonrpc": "2.0", "method": "textDocument/didChange",
    "params": {"textDocument": {"uri": uri},
               "contentChanges": [{"text": "-- nim source v2"}]}})
  check(resp2["params"]["diagnostics"].len == 0,
    "shed diagnostics: all white -> no diagnostics on didChange")
  removeDir(dir)

# --- Issue #191: shed goal/context use the name-resolving pretty-printer --
block:
  let src191 = """postulate(Int, Univ)
proc quad (n : Int) : Int = _
"""
  let (_, ms191, _, errMsg191) = elabCheckHolesDir(src191, ".")
  check(errMsg191 == "", "name-aware shed goal: no error, got: " & errMsg191)
  check(ms191.holes.len == 1, "name-aware shed goal: one hole recorded")
  let (g191, c191, pi191) = shedGoalAndCtx(ms191, ms191.holes[0])
  check(g191 == "Int",
    "name-aware shed goal: goal shows 'Int', got: " & g191)
  check(c191 == @["n : Int"],
    "name-aware shed goal: ctx shows 'n : Int', got: " & $c191)
  check(pi191.len == 0,
    "goalPi: non-Pi goal yields an empty spine, got: " & $pi191)
  # Unnamed rigid keeps the R<n> fallback (no crash, no empty name).
  let unreg = Term(kind: tR, refId: 424242)
  check(prettyTerm(unreg, @[], initTable[int, string]()) == "R424242",
    "name-aware shed goal: unregistered rigid falls back to R<n>")

if failures > 0:
  echo failures, " failure(s)"
  quit(1)
echo "--- all sheds tests passed ---"
