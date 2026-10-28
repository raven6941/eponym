## Issue #209: `eponym/caseSplitShed` -- shed-aware case-split.
##
## The #208 webview case-split button called the `.ep`
## `textDocument/codeAction` path, which parses the document as Eponym
## source and rewrites a proc into a clause-def -- neither of which works
## for a `.nim` shed document (parse error on `!`; a clause-def cannot
## round-trip through the `![...]` expression node).
##
## `eponym/caseSplitShed` is the shed-aware backend: given (shedName,
## variable), it fills the shed's hole with an eliminator application
## whose method holes become fresh sub-sheds, returning nim-syntax text
## for the client to splice over the `![shedName]` node:
##   `![isZeroBody]` --case-split n-->
##   `natElim(lam(u: Nat) => Bool, ![isZeroBody_zero], ![isZeroBody_suc], n)`
##
## The test drives the method through `handleMessage` with a simulated
## macro-time sidecar (same pattern as test_shed_refine_method.nim).
import json
import os
import strutils
import tables
import lsp
import sheds

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

proc caseSplitReq(server: var LspServer, uri, shedName, variable: string,
                  id: int): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "eponym/caseSplitShed",
    "params": {"textDocument": {"uri": uri}, "shedName": shedName,
             "variable": variable}})

proc macroTime(nimFile: string, name: string,
               nimLine, nimCol: int): ShedInfo =
  ## Simulate `eponymBlock` for a single Nat->Bool shed: the generated
  ## source has one hole; resolveShedPlaceholders records its line/col.
  var src = "import \"lib/nat.ep\"\nimport \"lib/bool.ep\"\n" &
            "proc isZero (n : Nat) : Bool = " & shedPlaceholder(0) & "\n"
  result = ShedInfo(name: name, draft: "", nimLine: nimLine, nimCol: nimCol,
                    status: ssYellow)
  var infos = @[result]
  resolveShedPlaceholders(src, infos)
  result = infos[0]
  result.genSrc = src

let dir = getTempDir() / "shed_casesplit_method_test"
createDir(dir)
let nimFile = dir / "demo.nim"
# The nim file content only matters for the splice position; the server
# works from the sidecar + recorded genSrc.
let nimV0 = """import eponym_mac
eponymBlock:
  import "lib/nat.ep"
  import "lib/bool.ep"
  proc isZero(n: Nat): Bool = ![isZeroBody]
"""
writeFile(nimFile, nimV0)
let nimUri = "file://" & nimFile
let shedLine = 5
let shedCol = nimV0.splitLines()[4].find("![") + 1  # 1-based

var info = macroTime(nimFile, "isZeroBody", shedLine, shedCol)
check(info.holeLine == 3 and info.holeCol == 32,
  "macro-time: hole at 3:32, got " & $info.holeLine & ":" & $info.holeCol)
# The genSrc imports must resolve from the repo: rewrite to absolute.
# (And set the goal the macro would have recorded.)
info.genSrc = info.genSrc.replace("lib/nat.ep",
  getCurrentDir() / "lib/nat.ep").replace("lib/bool.ep",
  getCurrentDir() / "lib/bool.ep")
info.goal = "Bool"
info.ctx = @["n : Nat"]
writeShedSidecar(nimFile, @[info])

var server = LspServer(documents: initTable[string, string]())

# Happy path: case-split on n : Nat.
let cs = caseSplitReq(server, nimUri, "isZeroBody", "n", 1)
check("error" notin cs, "caseSplitShed(n): accepted, got: " & $cs)
let res = cs["result"]
check(res["term"].getStr() ==
      "natElim(lam(u: Nat) => Bool, ![isZeroBody_zero], ![isZeroBody_suc], n)",
  "case-split term is the eliminator application with sub-shed nodes")
check(res["nimLine"].getInt() == shedLine and
      res["nimCol"].getInt() == shedCol,
  "splice position matches the ![...] node")
check(res["subSheds"].len == 2 and
      res["subSheds"][0].getStr() == "isZeroBody_zero" and
      res["subSheds"][1].getStr() == "isZeroBody_suc",
  "two sub-sheds, one per constructor")

# Error paths.
let csBadVar = caseSplitReq(server, nimUri, "isZeroBody", "zzz", 2)
check("error" in csBadVar and
      "not in scope" in csBadVar["error"]["message"].getStr(),
  "unknown variable rejected with 'not in scope'")
let csBadShed = caseSplitReq(server, nimUri, "nope", "n", 3)
check("error" in csBadShed and
      "unknown shed" in csBadShed["error"]["message"].getStr(),
  "unknown shed rejected")

if failures > 0:
  echo failures, " FAILURES"
  quit(1)
echo "all case-split method tests passed"
