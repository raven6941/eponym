## Issue #137: `eponym/refineShed` -- the server-owned refine round-trip.
##
## The #137 gap: for real `.nim` shed documents the server could not run
## the #58 refine action, because that path elaborates document text as
## Eponym source, which a `.nim` file is not. `eponym/refineShed` closes
## it: the client sends only (shedName, term); the server fills the hole
## in the macro-recorded generated source, refreshes statuses, rewrites
## the sidecar, and returns the term plus the `.nim` splice position.
##
## The test drives the method through `handleMessage` exactly as the #136
## webview would: didOpen -> refineShed -> client splices the returned
## term over the `![...]` node -> didChange re-reads the sidecar ->
## shedLayout shows the done box. Macro time is simulated with the real
## `resolveShedPlaceholders` (hole line/col) plus the `genSrc` recording
## `sheds_mac.shedsBlock` performs.
import json
import os
import strutils
import tables
import elab
import lsp
import sheds

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

proc didOpen(server: var LspServer, uri, text: string): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didOpen",
    "params": {"textDocument": {"uri": uri, "text": text}}})

proc didChange(server: var LspServer, uri, text: string): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didChange",
    "params": {"textDocument": {"uri": uri},
               "contentChanges": [{"text": text}]}})

proc refineShedReq(server: var LspServer, uri, shedName, term: string,
                   id: int): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "eponym/refineShed",
    "params": {"textDocument": {"uri": uri}, "shedName": shedName,
               "term": term}})

proc shedNamesReq(server: var LspServer, uri: string, id: int): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "eponym/shedNames",
    "params": {"textDocument": {"uri": uri}}})

proc spliceShed(nimText: string, line1, col1: int, term: string): string =
  ## The client-side splice: replace the single-line `![...]` node
  ## starting at 1-based (line1, col1) with the refined term.
  let lines = nimText.splitLines()
  let ln = lines[line1 - 1]
  doAssert ln[col1 - 1] == '!' and ln[col1] == '[',
    "splice: no shed node at " & $line1 & ":" & $col1
  var depth = 0
  var e = -1
  for i in (col1 - 1) ..< ln.len:
    if ln[i] == '[': inc depth
    elif ln[i] == ']':
      dec depth
      if depth == 0: e = i + 1; break
  doAssert e >= 0, "splice: unbalanced shed node"
  var res = lines
  res[line1 - 1] = ln[0 ..< (col1 - 1)] & term & ln[e .. ^1]
  res.join("\n")

proc macroTime(nimFile: string, names: seq[string],
               nimLines, nimCols: seq[int]): seq[ShedInfo] =
  ## Simulate what `shedsBlock` records: placeholders resolved by the
  ## real `resolveShedPlaceholders` (hole line AND column), `genSrc`
  ## stored per shed (the `sheds_mac` #137 addition).
  var src = "postulate Int : ?\n"
  for i, nm in names:
    src &= "proc p" & $i & " (n : Int) : Int = " & shedPlaceholder(i) & "\n"
  result = @[]
  for i, nm in names:
    result.add(ShedInfo(name: nm, draft: "", nimLine: nimLines[i],
                        nimCol: nimCols[i], status: ssYellow))
  resolveShedPlaceholders(src, result)
  for i in 0 ..< result.len:
    result[i].genSrc = src

# --- the loop, as the webview performs it --------------------------------

let dir = getTempDir() / "shed_refine_method_test"
createDir(dir)
let nimFile = dir / "demo.nim"
let nimV0 = """import sheds_mac
shedsBlock:
  postulate(Int, Univ)
  proc doubleIt(n: Int): Int = ![ shedA ]
  proc tripleIt(n: Int): Int = ![ shedB ]
"""
writeFile(nimFile, nimV0)
let nimUri = "file://" & nimFile
let shedALine = 4
let shedACol = nimV0.splitLines()[3].find("![") + 1  # 1-based
let shedBLine = 5
let shedBCol = nimV0.splitLines()[4].find("![") + 1

var shedInfos = macroTime(nimFile, @["shedA", "shedB"],
                          @[shedALine, shedBLine], @[shedACol, shedBCol])
check(shedInfos[0].holeLine == 2 and shedInfos[0].holeCol > 0,
  "macro-time: hole line/col recorded, got " &
  $shedInfos[0].holeLine & ":" & $shedInfos[0].holeCol)
writeShedSidecar(nimFile, shedInfos)

var server = LspServer(documents: initTable[string, string]())

# shedNames: the client picker source.
let namesResp = shedNamesReq(server, nimUri, 1)
check("error" notin namesResp and namesResp["result"].len == 2 and
      namesResp["result"][0].getStr() == "shedA",
  "shedNames lists both sheds")

# didOpen -> two yellow diagnostics from the sidecar.
let openResp = didOpen(server, nimUri, nimV0)
check(openResp["params"]["diagnostics"].len == 2,
  "didOpen: two yellow warnings")

# Refine shedA through the server-owned method (no client-held source).
let refA = refineShedReq(server, nimUri, "shedA", "addInt n n", 10)
check("error" notin refA, "refineShed(shedA): accepted, got: " & $refA)
let resA = refA["result"]
check(resA["term"].getStr() == "addInt n n" and
      resA["status"].getStr() == "white" and
      resA["nimLine"].getInt() == shedALine and
      resA["nimCol"].getInt() == shedACol and
      resA["yellowCount"].getInt() == 1,
  "refineShed(shedA): white, splice pos 4:" & $shedACol & ", 1 yellow left")

# The sidecar on disk is rewritten: A white with the filled source, B
# still yellow (same block: genSrc updated for both).
let sheds1 = readShedSidecar(sidecarPath(nimFile))
check(sheds1[0].status == ssWhite and sheds1[0].genSrc.contains("addInt n n"),
  "sidecar: shedA white, filled source recorded")
check(sheds1[1].status == ssYellow and sheds1[1].holeLine == 3 and
      sheds1[1].genSrc == sheds1[0].genSrc,
  "sidecar: shedB still yellow on line 3, block source shared")

# didChange re-reads the sidecar -> only shedB warns.
let chResp = didChange(server, nimUri, nimV0)
let diags1 = chResp["params"]["diagnostics"]
check(diags1.len == 1 and diags1[0]["message"].getStr().contains("shedB"),
  "didChange: only shedB warns after first refine")

# The client splice: the returned term over the `![ shedA ]` node.
let nimV1 = spliceShed(nimV0, resA["nimLine"].getInt(),
                       resA["nimCol"].getInt(), resA["term"].getStr())
check(nimV1.splitLines()[3] == "  proc doubleIt(n: Int): Int = addInt n n",
  "client splice: shed node replaced by the term")

# Refine shedB -> both white, diagnostics silent.
let refB = refineShedReq(server, nimUri, "shedB", "addInt (addInt n n) n", 20)
check("error" notin refB and refB["result"]["status"].getStr() == "white" and
      refB["result"]["yellowCount"].getInt() == 0,
  "refineShed(shedB): white, none yellow left")
let chResp2 = didChange(server, nimUri, nimV1)
check(chResp2["params"]["diagnostics"].len == 0,
  "didChange: silent when all white")

# The completed program (both fills in the recorded source) elaborates
# strictly: the loop produced real code.
let sheds2 = readShedSidecar(sidecarPath(nimFile))
try:
  discard elabCheck(sheds2[1].genSrc)
  check(true, "completed source passes strict elabCheck")
except ElabError as e:
  check(false, "completed source passes strict elabCheck: " & e.msg)

# --- error cases ----------------------------------------------------------

let dir2 = getTempDir() / "shed_refine_method_errs"
createDir(dir2)
let nimFile2 = dir2 / "demo.nim"
writeFile(nimFile2, "-- placeholder")
var shedInfos2 = macroTime(nimFile2, @["only"], @[2], @[10])
writeShedSidecar(nimFile2, shedInfos2)
let uri2 = "file://" & nimFile2

let eUnknown = refineShedReq(server, uri2, "nope", "n", 30)
check("error" in eUnknown and
      eUnknown["error"]["message"].getStr().contains("unknown shed"),
  "unknown shed -> error, got: " & $eUnknown["error"]["message"])

let eBadTerm = refineShedReq(server, uri2, "only", "addInt n", 31)
check("error" in eBadTerm and
      eBadTerm["error"]["message"].getStr().contains("refine rejected"),
  "ill-typed term -> refine rejected, got: " &
  $eBadTerm["error"]["message"])

let eOk = refineShedReq(server, uri2, "only", "n", 32)
check("error" notin eOk and eOk["result"]["status"].getStr() == "white",
  "well-typed fill accepted")
let eWhite = refineShedReq(server, uri2, "only", "n", 33)
check("error" in eWhite and
      eWhite["error"]["message"].getStr().contains("not refinable"),
  "refining a white shed -> not refinable, got: " &
  $eWhite["error"]["message"])

# --- multi-line fill: later sheds' hole lines shift ------------------------

let dir3 = getTempDir() / "shed_refine_method_multiline"
createDir(dir3)
let nimFile3 = dir3 / "demo.nim"
writeFile(nimFile3, "-- placeholder")
var shedInfos3 = macroTime(nimFile3, @["mA", "mB"], @[2, 3], @[10, 10])
writeShedSidecar(nimFile3, shedInfos3)
let uri3 = "file://" & nimFile3

let refM = refineShedReq(server, uri3, "mA", "addInt n\n      n", 40)
check("error" notin refM and refM["result"]["status"].getStr() == "white",
  "multi-line fill accepted, got: " & $refM)
let sheds3 = readShedSidecar(sidecarPath(nimFile3))
check(sheds3[1].status == ssYellow and sheds3[1].holeLine == 4,
  "multi-line fill: shed mB hole line shifted 3 -> 4, still yellow")
let refM2 = refineShedReq(server, uri3, "mB", "n", 41)
check("error" notin refM2 and
      refM2["result"]["status"].getStr() == "white" and
      refM2["result"]["yellowCount"].getInt() == 0,
  "refine after shift: mB fills, both white")
let sheds3b = readShedSidecar(sidecarPath(nimFile3))
try:
  discard elabCheck(sheds3b[1].genSrc)
  check(true, "multi-line completed source passes strict elabCheck")
except ElabError as e:
  check(false, "multi-line completed source passes strict elabCheck: " & e.msg)

# --- dependent eliminator branch refinement ------------------------------
# Regression for case-split-created sheds: the successor branch of
# natElim over Nat -> Bool has two binders (the predecessor and its
# induction hypothesis). Filling that named shed must accept the lambda
# implementing the branch, then refresh it to white.
let dir4 = getTempDir() / "shed_refine_method_dependent_branch"
createDir(dir4)
let nimFile4 = dir4 / "demo.nim"
writeFile(nimFile4, "-- placeholder")
let natLib = (getCurrentDir() / "lib/nat.ep").replace("\\", "/")
let boolLib = (getCurrentDir() / "lib/bool.ep").replace("\\", "/")
var branchSrc = "import \"" & natLib & "\"\n" &
                "import \"" & boolLib & "\"\n" &
                "proc isZero (n : Nat) : Bool = " &
                "natElim (lam (u : Nat). Bool) true " &
                shedPlaceholder(0) & " n\n"
var branchInfo = @[ShedInfo(name: "isZeroBody_suc", draft: "",
                            nimLine: 5, nimCol: 1, status: ssYellow)]
resolveShedPlaceholders(branchSrc, branchInfo)
branchInfo[0].genSrc = branchSrc
writeShedSidecar(nimFile4, branchInfo)
let branchResp = refineShedReq(
  server, "file://" & nimFile4, "isZeroBody_suc",
  "lam p. lam ih. false", 50)
check("error" notin branchResp,
  "case-split successor shed accepts its two-binder Bool implementation: " &
  (if "error" in branchResp: branchResp["error"]["message"].getStr()
   else: $branchResp))
if "error" notin branchResp:
  check(branchResp["result"]["status"].getStr() == "white",
    "case-split successor shed becomes white after filling")
  let branchAfter = readShedSidecar(sidecarPath(nimFile4))[0]
  check(branchAfter.genSrc.contains("(lam p. lam ih. false)"),
    "dependent branch fill is parenthesized in the recorded source")

removeDir(dir)
removeDir(dir2)
removeDir(dir3)
removeDir(dir4)

if failures > 0:
  echo failures, " FAILURES"
  quit(1)
echo "--- all shed refine-method tests passed ---"
