## Issue #58: LSP hole commands — hover slice.
##
## Headless scripted mock-LSP session (no editor): drives the server's
## message handlers in-process over a Vec program with a `_` hole and
## asserts hover returns the goal type + context at the hole.
import json
import strutils
import tables
import lsp

const vecSrc = """data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc headDefault (A : ?) (n : Nat) (d : A) (xs : Vec A (suc n)) : A =
  _
"""

proc msg(s: string): JsonNode = parseJson(s)

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

# --- unit: hoverAt -------------------------------------------------------
let md = hoverAt(vecSrc, 7, 2)  # 0-based: line of `  _`, col of `_`
check(md.contains("goal"), "hoverAt returns a goal at the hole")
check(md.contains("context"), "hoverAt returns the context at the hole")
for name in ["xs", "d", "n", "A"]:
  check(md.contains(name), "hoverAt context mentions `" & name & "`")
check(hoverAt(vecSrc, 0, 0) == "", "hoverAt returns \"\" away from holes")
check(hoverAt("proc broken = = =", 0, 0) == "",
  "hoverAt returns \"\" for an unparseable document")

# --- issue #139: name-resolving pretty-printer -----------------------------
# Globals render as source names, not `R<n>` rigids.
check(md.contains("goal : A"), "hover goal resolves to `A`")
check(md.contains("`xs : (Vec A (suc n))`"),
  "hover ctx resolves `Vec` and `suc`")
check(md.contains("`n : Nat`"), "hover ctx resolves `Nat`")
check(md.contains("`A : ?`"), "hover ctx renders the universe as `?`")
# No `libpcre` in this VM, so scan for `R<digit>` without the `re` module.
proc hasRigidRender(s: string): bool =
  var i = 0
  while i < s.len - 1:
    if s[i] == 'R' and s[i+1] in {'0'..'9'}: return true
    inc i
  false
check(not hasRigidRender(md),
  "hover shows no rigid `R<n>` renderings for globals")
const natGoalSrc = """data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
proc f : Nat =
  _
"""
let mdNat = hoverAt(natGoalSrc, 4, 2)
check(mdNat.contains("goal : Nat"),
  "hover goal resolves a global type name (`Nat`)")

# --- protocol: scripted session through handleMessage --------------------
var server = LspServer(documents: initTable[string, string]())

let initResp = server.handleMessage(msg(
  """{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"""))
check(initResp["result"]["capabilities"]["hoverProvider"].getBool(),
  "initialize advertises hoverProvider")

let openResp = server.handleMessage(%*{
  "jsonrpc": "2.0",
  "method": "textDocument/didOpen",
  "params": {"textDocument": {"uri": "file:///vec.ep", "text": vecSrc}}})
check(openResp["method"].getStr() == "textDocument/publishDiagnostics",
  "didOpen yields publishDiagnostics")
check(openResp["params"]["diagnostics"].len == 0,
  "hole program publishes no diagnostics (holes are not errors)")

let hoverResp = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 2, "method": "textDocument/hover",
  "params": {"textDocument": {"uri": "file:///vec.ep"},
             "position": {"line": 7, "character": 2}}})
let contents = hoverResp["result"]["contents"]["value"].getStr()
check(contents.contains("goal"), "protocol hover returns goal markdown")
check(contents.contains("xs"), "protocol hover returns context")

let hoverMiss = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 3, "method": "textDocument/hover",
  "params": {"textDocument": {"uri": "file:///vec.ep"},
             "position": {"line": 0, "character": 0}}})
check(hoverMiss["result"].kind == JNull,
  "protocol hover away from holes returns null")

# A genuine error after a hole still surfaces as a diagnostic.
let badSrc = vecSrc & "proc bad : Nat =\n  zero zero\n"
let badOpen = server.handleMessage(%*{
  "jsonrpc": "2.0",
  "method": "textDocument/didOpen",
  "params": {"textDocument": {"uri": "file:///bad.ep", "text": badSrc}}})
check(badOpen["params"]["diagnostics"].len == 1,
  "non-hole error after a hole still publishes one diagnostic")
# ...but the hole from the successful prefix is still hoverable.
let badHover = server.handleMessage(%*{
  "jsonrpc": "2.0", "id": 6, "method": "textDocument/hover",
  "params": {"textDocument": {"uri": "file:///bad.ep"},
             "position": {"line": 7, "character": 2}}})
check(badHover["result"]["contents"]["value"].getStr().contains("goal"),
  "hole in the successful prefix stays hoverable past a later error")

let unknownResp = server.handleMessage(msg(
  """{"jsonrpc":"2.0","id":4,"method":"nope/nothing","params":{}}"""))
check(unknownResp["error"]["code"].getInt() == -32601,
  "unknown method returns Method not found")

let shutdownResp = server.handleMessage(msg(
  """{"jsonrpc":"2.0","id":5,"method":"shutdown","params":{}}"""))
check(shutdownResp["result"].kind == JNull, "shutdown returns null result")

if failures > 0:
  echo failures, " FAILURES"
  quit(1)
echo "all lsp hole tests passed"
