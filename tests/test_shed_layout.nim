## Issue #135: 2D box layout engine (Epigram deduction style) + the
## `eponym/shedLayout` LSP method.
##
## Headless tests (no editor): layout constructors, ASCII rendering,
## term layout, hole-ID wiring, JSON shape, and the LSP method round-trip
## through `handleMessage` against a real sidecar file.
import os
import strutils
import sequtils  # anyIt
import json
import tables  # initTable (LSP server in tests)
import eponym_init  # tmApp, tmLam, tmLet, tmMeta, tmInt, vv, `$`
import sheds  # ShedInfo, sidecarPath, writeShedSidecar
import shed_layout
import lsp  # handleMessage, shedLayout

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

# --- goal-state layout: the exact ASCII shape ------------------------------
# goalStateBox(@["n : Int"], 0, "Int") renders:
#   context premise (width 9) above the rule, hole box (width 10) below,
#   both centered in the inner width 10.
let gs = goalStateBox(@["n : Int"], 0, "Int")
check(renderBox(gs) == """
┌──────────┐
│┌───────┐ │
││n : Int│ │
│└───────┘ │
├──────────┤
│┌────────┐│
││?0 : Int││
│└────────┘│
└──────────┘""".strip(), "goal state: exact ASCII snapshot")
check(gs.width == 12 and gs.height == 9,
  "goal state: measured 12x9, got " & $gs.width & "x" & $gs.height)
check(allHoleIds(gs) == @[0], "goal state: hole 0 wired")

# --- case/eliminator: branches side-by-side --------------------------------
let cb = caseBox("n", @[
  (pat: "zero", body: textBox("0")),
  (pat: "suc k", body: textBox("k+1"))])
let cbs = renderBox(cb)
let branchLines = cbs.splitLines()
check(branchLines.anyIt("zero" in it and "suc k" in it),
  "case: both branch patterns on one line (side-by-side)")
measure(cb)
check(cb.width == cb.children[0].width + cb.children[1].width + 2 + 2,
  "case: width = branch widths + gap + borders")
check(allHoleIds(cb) == @[], "case: no holes")

# --- induction: header + case boxes below -----------------------------------
let ib = inductionBox("n", @[
  (pat: "zero", body: textBox("0")),
  (pat: "suc k", body: textBox("k+1"))])
let ibs = renderBox(ib)
check(ibs.contains("by induction on n"), "induction: header line")
check(ibs.splitLines().anyIt("zero" in it and "suc k" in it),
  "induction: case boxes below the header, side-by-side")

# --- let-sequence: stacked labeled deductions -------------------------------
let ls = letSeq(@[
  (name: "a", ty: "Int", val: textBox("1")),
  (name: "b", ty: "Int", val: textBox("a + a"))],
  textBox("b"))
let lss = renderBox(ls)
check(lss.contains("let a : Int") and lss.contains("let b : Int"),
  "let-seq: both binding labels on rules")
let laPos = lss.find("let a : Int")
let lbPos = lss.find("let b : Int")
check(laPos >= 0 and lbPos > laPos,
  "let-seq: bindings stacked vertically (a above b)")

# --- term layout: app as Pi-elim, holes as hole boxes -----------------------
# ((f :$ A x) with a hole argument): premises side-by-side above the rule,
# hole box below carrying the goal.
let tm = tmApp(tmApp(vv(0), tmInt(3)), tmMeta(7, @[]))
let tb = layoutTerm(tm, proc(id: int): string = "Nat")
check(allHoleIds(tb) == @[7], "term layout: hole 7 wired")
let ts = renderBox(tb)
check(ts.contains("?7 : Nat"), "term layout: hole box shows goal")
check(ts.contains("3"), "term layout: int argument rendered")

# --- JSON shape --------------------------------------------------------------
let j = boxToJson(gs)
check(j["holeIds"] == % @[0], "json: holeIds [0]")
check(j["holeGoal"].getStr() == "", "json: rule box is not a hole box")
check(j["conclusion"]["holeGoal"].getStr() == "Int",
  "json: conclusion is the hole box with its goal")
check(j["width"].getInt() == 12 and j["height"].getInt() == 9,
  "json: measured width/height present")
check(j["premises"].len == 1 and j["children"].len == 0,
  "json: rule shape has premises, no children")

# --- `eponym/shedLayout`: LSP round-trip against a real sidecar -------------
block:
  let dir = getTempDir() / "shed_layout_test"
  createDir(dir)
  let nimFile = dir / "demo.nim"
  writeFile(nimFile, "-- demo")
  let uri = "file://" & nimFile
  var shedsIn = @[ShedInfo(name: "quadBody", draft: "", nimLine: 10,
                           nimCol: 5, holeLine: 3, holeIdx: 0,
                           goal: "Int", ctx: @["n : Int"],
                           status: ssYellow)]
  writeShedSidecar(nimFile, shedsIn)
  let resp = shedLayout(uri, "quadBody")
  check(not resp.isNil, "shedLayout: response for known shed")
  check(resp["box"]["holeIds"] == % @[0], "shedLayout: hole id in box")
  check(resp["box"]["conclusion"]["header"] == % @["?0 : Int"],
    "shedLayout: conclusion is the hole box")
  check(shedLayout(uri, "nope").isNil, "shedLayout: nil for unknown shed")
  check(shedLayout("file:///nonexistent/x.nim", "quadBody").isNil,
    "shedLayout: nil when no sidecar")
  # Through the JSON-RPC dispatcher.
  var server = LspServer(documents: initTable[string, string]())
  let rpc = handleMessage(server, %*{
    "jsonrpc": "2.0", "id": 1, "method": "eponym/shedLayout",
    "params": {"textDocument": {"uri": uri}, "shedName": "quadBody"}})
  check(rpc["result"]["box"]["holeIds"] == % @[0],
    "shedLayout: reachable via handleMessage")
  let rpcBad = handleMessage(server, %*{
    "jsonrpc": "2.0", "id": 2, "method": "eponym/shedLayout",
    "params": {"textDocument": {"uri": uri}, "shedName": "nope"}})
  check("error" in rpcBad, "shedLayout: unknown shed -> error response")
  removeDir(dir)

# --- layoutShed: white shed (no open hole) ----------------------------------
block:
  let done = layoutShed(ShedInfo(name: "plus", draft: "", nimLine: 1,
                                 nimCol: 1, holeLine: 0, holeIdx: -1,
                                 goal: "Nat", ctx: @[], status: ssWhite))
  check(allHoleIds(done) == @[], "layoutShed: white shed has no holes")
  check(renderBox(done).contains("no open holes"),
    "layoutShed: white shed renders a done box")

if failures > 0:
  echo failures, " failure(s)"
  quit(1)
echo "--- all shed_layout tests passed ---"
