## Issue #137: end-to-end shed loop, scripted headless.
##
## A shed with two holes (two sheds in one block, each one hole on its own
## line), driven through the real LSP server (`handleMessage`):
##   1. The `shedsBlock` macro wrote the sidecar -> both sheds yellow.
##      (Macro time is simulated by writing the sidecar exactly as the
##      macro would: `writeShedSidecar` with macro-assigned statuses. The
##      macro -> sidecar path itself is covered by `sheds_demo.nim`.)
##   2. `didOpen` the `.nim` doc -> two yellow diagnostics from the sidecar.
##   3. `eponym/shedLayout` -> the box tree with each shed's hole.
##   4. Refine hole 1 via the #58 `textDocument/codeAction` on the
##      generated Eponym source (the server's existing action path);
##      `refreshShedStatuses` -> shed A white, shed B yellow; the sidecar
##      is re-written; `didChange` -> one diagnostic; layout for A is the
##      done box while layout for B still shows its hole.
##   5. Refine hole 2 -> both white; `didChange` -> no diagnostics; the
##      completed source passes strict `elabCheck`.
##
## This is the loop the #136 webview performs with clicks; the headless
## script drives the same server methods in the same order. The one piece
## not closed here (see #136): for real `.nim` docs the server cannot run
## `codeAction` on Nim text -- the client must map the generated-source
## fill back to the shed position; the script simulates that mapping by
## holding the generated source itself.
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

# --- harness (mock conventions shared with test_lsp_actions/test_sheds) ---

proc holePos(src: string, n: int): tuple[line, col: int] =
  ## 0-based position of the n-th `_` hole in the source.
  var seen = 0
  let hlines = src.splitLines()
  for i, ln in hlines:
    var j = 0
    while j < ln.len:
      if ln[j] == '_':
        if seen == n: return (i, j)
        inc seen
      inc j
  (-1, -1)

proc applyEdit(src: string, e: JsonNode): string =
  ## Apply the single text edit of a codeAction, editor-style.
  var change: JsonNode = nil
  for _, v in e["edit"]["changes"].pairs: change = v[0]
  assert not change.isNil, "codeAction edit has no changes"
  let r = change["range"]
  let sl = r["start"]["line"].getInt()
  let sc = r["start"]["character"].getInt()
  let el = r["end"]["line"].getInt()
  let ec = r["end"]["character"].getInt()
  let t = change["newText"].getStr()
  let lines = src.splitLines()
  var res: seq[string] = @[]
  for i, ln in lines:
    if i < sl or i > el: res.add(ln)
    elif i == sl and sl == el: res.add(ln[0 ..< sc] & t & ln[ec .. ^1])
    elif i == sl: res.add(ln[0 ..< sc] & t)
    elif i == el: res.add(ln[ec .. ^1])
  res.join("\n")

proc codeAction(server: var LspServer, uri: string, id: int, line, col: int,
                term = ""): JsonNode =
  var params = %*{
    "textDocument": {"uri": uri},
    "range": {"start": {"line": line, "character": col},
              "end": {"line": line, "character": col}},
    "context": {"diagnostics": []}
  }
  if term != "": params["term"] = %term
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "textDocument/codeAction",
    "params": params})

proc didOpen(server: var LspServer, uri, text: string): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didOpen",
    "params": {"textDocument": {"uri": uri, "text": text}}})

proc didChange(server: var LspServer, uri, text: string): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didChange",
    "params": {"textDocument": {"uri": uri},
               "contentChanges": [{"text": text}]}})

proc shedLayoutReq(server: var LspServer, uri, shedName: string,
                   id: int): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "eponym/shedLayout",
    "params": {"textDocument": {"uri": uri}, "shedName": shedName}})

proc diagsOf(resp: JsonNode): JsonNode =
  resp["params"]["diagnostics"]

# --- the loop -------------------------------------------------------------

# The generated Eponym source the shedsBlock macro feeds the elaborator
# (same shape as test_sheds' srcOneHole, two sheds on separate lines so
# single-line fills keep the line matching exact -- the #134 limitation).
const genSrcV0 = """postulate(Int, Univ)
proc doubleIt (n : Int) : Int = _
proc tripleIt (n : Int) : Int = _
"""

let dir = getTempDir() / "shed_loop_test"
createDir(dir)
let nimFile = dir / "loop_demo.nim"
writeFile(nimFile, "-- placeholder: the server reads shed state from the sidecar")
let nimUri = "file://" & nimFile
const genUri = "file:///loop_gen.ep"  # the generated-source "document"

# 1. Macro time: two sheds, both matched to open holes -> yellow.
var shedInfos = @[
  ShedInfo(name: "shedA", draft: "", nimLine: 7, nimCol: 25,
           holeLine: 2, holeIdx: 0, goal: "Int", ctx: @["n : Int"],
           status: ssYellow),
  ShedInfo(name: "shedB", draft: "", nimLine: 8, nimCol: 25,
           holeLine: 3, holeIdx: 1, goal: "Int", ctx: @["n : Int"],
           status: ssYellow)]
writeShedSidecar(nimFile, shedInfos)

var server = LspServer(documents: initTable[string, string]())

# 2. didOpen the `.nim` doc -> two yellow diagnostics from the sidecar.
let openResp = didOpen(server, nimUri, "-- placeholder")
check(openResp["method"].getStr() == "textDocument/publishDiagnostics",
  "loop: didOpen .nim publishes diagnostics")
check(diagsOf(openResp).len == 2 and
      diagsOf(openResp)[0]["severity"].getInt() == 2 and
      diagsOf(openResp)[1]["severity"].getInt() == 2,
  "loop: both sheds yellow -> two warnings")

# 3. shedLayout for each shed -> the hole box.
let layA = shedLayoutReq(server, nimUri, "shedA", 10)
check("error" notin layA and
      layA["result"]["box"]["holeIds"].elems.len == 1,
  "loop: shedLayout(shedA) shows its hole")
let layB = shedLayoutReq(server, nimUri, "shedB", 11)
check("error" notin layB and
      layB["result"]["box"]["holeIds"].elems.len == 1,
  "loop: shedLayout(shedB) shows its hole")

# 4. Refine hole 1 via the #58 code action on the generated source.
discard didOpen(server, genUri, genSrcV0)
let (h1l, h1c) = holePos(genSrcV0, 0)
let refA = codeAction(server, genUri, 20, h1l, h1c, term = "addInt n n")
check("error" notin refA, "loop: refine hole 1 accepted")
var sawRefine = false
var editA: JsonNode = nil
for a in refA["result"]:
  if a["title"].getStr().startsWith("refine"):
    sawRefine = true
    editA = a
check(sawRefine and not editA.isNil, "loop: refine action offered")
let genSrcV1 = applyEdit(genSrcV0, editA)
check(holePos(genSrcV1, 0) != (-1, -1), "loop: one hole remains after first fill")
discard didChange(server, genUri, genSrcV1)

# The editor loop: re-elaborate the edited source, re-apply the status rule.
refreshShedStatuses(shedInfos, genSrcV1, dir)
check(shedInfos[0].status == ssWhite and shedInfos[1].status == ssYellow,
  "loop: shed A white, shed B still yellow after first fill")
writeShedSidecar(nimFile, shedInfos)

# didChange on the `.nim` doc re-reads the sidecar -> one warning left.
let chResp = didChange(server, nimUri, "-- placeholder")
check(diagsOf(chResp).len == 1 and
      diagsOf(chResp)[0]["severity"].getInt() == 2 and
      diagsOf(chResp)[0]["message"].getStr().contains("shedB"),
  "loop: didChange re-reads sidecar -> only shedB warns")

# Layout updates: A is the done box, B still shows its hole.
let layA2 = shedLayoutReq(server, nimUri, "shedA", 30)
check("error" notin layA2 and
      layA2["result"]["box"]["holeIds"].elems.len == 0,
  "loop: shedLayout(shedA) is the done box after fill")
let layB2 = shedLayoutReq(server, nimUri, "shedB", 31)
check("error" notin layB2 and
      layB2["result"]["box"]["holeIds"].elems.len == 1,
  "loop: shedLayout(shedB) still shows its hole")

# 5. Refine hole 2 -> both white, diagnostics silent.
let (h2l, h2c) = holePos(genSrcV1, 0)
let refB = codeAction(server, genUri, 40, h2l, h2c,
                      term = "addInt (addInt n n) n")
check("error" notin refB, "loop: refine hole 2 accepted")
var editB: JsonNode = nil
for a in refB["result"]:
  if a["title"].getStr().startsWith("refine"): editB = a
check(not editB.isNil, "loop: refine action offered for hole 2")
let genSrcV2 = applyEdit(genSrcV1, editB)
check(holePos(genSrcV2, 0) == (-1, -1), "loop: no holes remain")
discard didChange(server, genUri, genSrcV2)
refreshShedStatuses(shedInfos, genSrcV2, dir)
check(shedInfos[0].status == ssWhite and shedInfos[1].status == ssWhite,
  "loop: both sheds white after second fill")
writeShedSidecar(nimFile, shedInfos)
let chResp2 = didChange(server, nimUri, "-- placeholder")
check(diagsOf(chResp2).len == 0,
  "loop: all white -> diagnostics silent on didChange")

# The completed program elaborates strictly: the loop produced real code.
try:
  discard elabCheck(genSrcV2)
  check(true, "loop: completed program passes strict elabCheck")
except ElabError as e:
  check(false, "loop: completed program passes strict elabCheck: " & e.msg)

if failures > 0:
  echo failures, " FAILURES"
  quit(1)
echo "--- all shed loop tests passed ---"
