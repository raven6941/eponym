## Issue #58: LSP hole commands — refine / case-split / give slice.
##
## Headless scripted mock-LSP session (no editor): develops `Vec` append
## hole-by-hole through `textDocument/codeAction`, applying each returned
## edit the way an editor would (didChange), and re-hovering to see the
## new goal state. Ends with a complete, strictly-elaborating definition.
import json
import strutils
import tables
import elab
import lsp

const appendSrc = """data(Nat, Univ) where
| zero : Nat
| suc (n : Nat) : Nat
def(add, Nat -> Nat -> Nat):
clause([zero, n], n)
clause([(suc m), n], suc (add m n))
data(Vec, [A : Univ], Nat -> Univ) where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
proc append {A : Univ} {m : Nat} {n : Nat} (xs : Vec A m) (ys : Vec A n) : Vec A (add m n) =
  _
"""

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

proc msg(s: string): JsonNode = parseJson(s)

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

proc holePos(src: string, n: int): tuple[line, col: int] =
  ## 0-based position of the n-th `_` hole in the source.
  var seen = 0
  let lines = src.splitLines()
  for i, ln in lines:
    var j = 0
    while j < ln.len:
      if ln[j] == '_':
        if seen == n: return (i, j)
        inc seen
      inc j
  (-1, -1)

proc codeAction(server: var LspServer, uri: string, id: int, line, col: int,
                variable = "", term = ""): JsonNode =
  var params = %*{
    "textDocument": {"uri": uri},
    "range": {"start": {"line": line, "character": col},
              "end": {"line": line, "character": col}},
    "context": {"diagnostics": []}
  }
  if variable != "": params["variable"] = %variable
  if term != "": params["term"] = %term
  server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "textDocument/codeAction",
    "params": params})

proc didChange(server: var LspServer, uri, text: string): JsonNode =
  server.handleMessage(%*{
    "jsonrpc": "2.0", "method": "textDocument/didChange",
    "params": {"textDocument": {"uri": uri},
               "contentChanges": [{"text": text}]}})

proc hoverMd(server: var LspServer, uri: string, id: int,
             line, col: int): string =
  let resp = server.handleMessage(%*{
    "jsonrpc": "2.0", "id": id, "method": "textDocument/hover",
    "params": {"textDocument": {"uri": uri},
               "position": {"line": line, "character": col}}})
  if resp["result"].kind == JNull: ""
  else: resp["result"]["contents"]["value"].getStr()

# --- session -------------------------------------------------------------
var server = LspServer(documents: initTable[string, string]())
const uri = "file:///append.ep"

let initResp = server.handleMessage(msg(
  """{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"""))
check(initResp["result"]["capabilities"]["codeActionProvider"].getBool(),
  "initialize advertises codeActionProvider")

var cur = appendSrc
let openResp = server.handleMessage(%*{
  "jsonrpc": "2.0", "method": "textDocument/didOpen",
  "params": {"textDocument": {"uri": uri, "text": cur}}})
check(openResp["params"]["diagnostics"].len == 0,
  "hole program publishes no diagnostics")

# 1. case-split on xs ------------------------------------------------------
let (hl, hc) = holePos(cur, 0)
check(hoverMd(server, uri, 10, hl, hc).contains("goal"),
  "hole in proc body shows a goal before splitting")
let csResp = codeAction(server, uri, 11, hl, hc, variable = "xs")
check("error" notin csResp, "case-split xs accepted")
let csActs = csResp["result"]
check(csActs.len == 1 and csActs[0]["title"].getStr() == "case-split xs",
  "one case-split action offered")
cur = applyEdit(cur, csActs[0])
check(cur.contains("clause([nil, ys], _)"), "split generated the nil clause")
check(cur.contains("clause([cons(n1, x, xs1), ys], _)"),
  "split generated the cons clause with freshened binders")
let chResp = didChange(server, uri, cur)
check(chResp["params"]["diagnostics"].len == 0,
  "split clauses elaborate (checked by the elaborator, not just text)")
let (h1l, h1c) = holePos(cur, 0)
let (h2l, h2c) = holePos(cur, 1)
check(hoverMd(server, uri, 20, h1l, h1c).contains("goal"),
  "nil-clause hole shows a goal after split")
check(hoverMd(server, uri, 21, h2l, h2c).contains("goal"),
  "cons-clause hole shows a goal after split")

# 2. refine the nil clause with `ys` ----------------------------------------
let refResp = codeAction(server, uri, 30, h1l, h1c, term = "ys")
check("error" notin refResp, "refine accepted")
let refActs = refResp["result"]
var hasRefine = false
var hasGive = false
for a in refActs:
  if a["title"].getStr() == "refine hole": hasRefine = true
  if a["title"].getStr() == "give ys": hasGive = true
check(hasRefine and hasGive,
  "hole-free refine offers both refine and give")
cur = applyEdit(cur, refActs[0])
discard didChange(server, uri, cur)
check(hoverMd(server, uri, 31, h1l, h1c) == "",
  "refined hole is gone (new goal state: no goal there)")
let (h2l2, h2c2) = holePos(cur, 0)
check(hoverMd(server, uri, 32, h2l2, h2c2).contains("goal"),
  "cons-clause hole still shows its goal after refine")

# 3. give the cons clause the recursive call --------------------------------
let giveResp = codeAction(server, uri, 40, h2l2, h2c2,
                          term = "cons A (add n1 n) x (append xs1 ys)")
check("error" notin giveResp, "give accepted")
let giveActs = giveResp["result"]
var sawGive = false
for a in giveActs:
  if a["title"].getStr().startsWith("give"): sawGive = true
check(sawGive, "give action offered for the recursive call")
cur = applyEdit(cur, giveActs[giveActs.len - 1])
let finalDiag = didChange(server, uri, cur)
check(finalDiag["params"]["diagnostics"].len == 0,
  "completed definition publishes no diagnostics")
check(holePos(cur, 0) == (-1, -1), "no holes remain")
try:
  discard elabCheck(cur)
  check(true, "completed append passes strict elabCheck")
except ElabError as e:
  check(false, "completed append passes strict elabCheck: " & e.msg)

# 4. negative paths (fresh document) -----------------------------------------
const uri2 = "file:///neg.ep"
discard server.handleMessage(%*{
  "jsonrpc": "2.0", "method": "textDocument/didOpen",
  "params": {"textDocument": {"uri": uri2, "text": appendSrc}}})
let (nhl, nhc) = holePos(appendSrc, 0)

let badRef = codeAction(server, uri2, 50, nhl, nhc, term = "ys ys")
check("error" in badRef and badRef["error"]["message"].getStr().contains("rejected"),
  "ill-typed refine rejected with a reason")

let badSplit = codeAction(server, uri2, 51, nhl, nhc, variable = "A")
check("error" in badSplit,
  "case-split on a non-datatype variable rejected")

let badSplit2 = codeAction(server, uri2, 52, nhl, nhc, variable = "ys")
check("error" in badSplit2 and
      badSplit2["error"]["message"].getStr().contains("first explicit"),
  "case-split on a non-first argument rejected with the clause restriction")

let holeTerm = codeAction(server, uri2, 53, nhl, nhc, term = "_")
let htActs = holeTerm["result"]
var htGive = false
for a in htActs:
  if a["title"].getStr().startsWith("give"): htGive = true
check(not htGive and htActs.len == 1,
  "term with holes offers refine only, not give")

if failures > 0:
  echo failures, " FAILURES"
  quit(1)
echo "all lsp action tests passed"
