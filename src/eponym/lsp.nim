# lsp.nim — Minimal LSP server for Eponym (Experiment 7)
#
# Exposes the elaborator via the Language Server Protocol:
# - Diagnostics: parse and elaboration errors at surface locations
# - Hover (issue #58): goal type + context at `_` holes
#
# This is a minimal version: stdio JSON-RPC, full-document sync.
# Code actions (refine, case-split, give) and incremental sync are future work.
#
# Usage: nim c -r --path:src src/lsp.nim
# Then configure your editor to use it for .ep files.

import json
import strutils
import tables
import elab
import preterm
import ett_init  # `$` for Term (issue #58)
import parse_surf
import unify  # HoleInfo, zonk (issue #58)

type
  LspServer* = object
    documents*: Table[string, string]  # uri -> text

proc readMessage(): JsonNode =
  ## Read one LSP message from stdin (Content-Length framed).
  var contentLength = 0
  while true:
    let line = stdin.readLine()
    if line == "":
      break  # end of headers
    if line.startsWith("Content-Length:"):
      contentLength = parseInt(line[15..^1].strip())
  if contentLength == 0:
    return nil
  var body = newString(contentLength)
  let n = stdin.readBuffer(addr body[0], contentLength)
  body.setLen(n)
  parseJson(body)

proc writeMessage(msg: JsonNode) =
  ## Write one LSP message to stdout.
  let body = $msg
  stdout.write("Content-Length: " & $body.len & "\r\n\r\n" & body)
  stdout.flushFile()

proc makeDiagnostic(uri: string, line, col: int, msg: string): JsonNode =
  %*{
    "uri": uri,
    "diagnostics": [
      {
        "range": {
          "start": {"line": line - 1, "character": col - 1},
          "end": {"line": line - 1, "character": col}
        },
        "severity": 1,  # Error
        "message": msg,
        "source": "eponym"
      }
    ]
  }

proc publishDiagnostics(server: var LspServer, uri: string): JsonNode =
  ## Elaborate the document and build the publishDiagnostics notification.
  ## Returns nil only when the document is unknown (no notification sent).
  if uri notin server.documents:
    return nil
  let text = server.documents[uri]
  var params: JsonNode
  try:
    # Issue #58: hole-tolerant — open holes are goals, not errors; only
    # the first non-hole failure (if any) becomes a diagnostic.
    let res = elabCheckHoles(text)
    if res.errMsg == "":
      params = %*{"uri": uri, "diagnostics": []}
    else:
      params = makeDiagnostic(uri, res.errLoc.line, res.errLoc.col, res.errMsg)
  except ParseError as e:
    params = makeDiagnostic(uri, e.loc.line, e.loc.col, e.msg)
  %*{
    "jsonrpc": "2.0",
    "method": "textDocument/publishDiagnostics",
    "params": params
  }

proc hoverAt*(src: string, line, col: int): string =
  ## Issue #58: goal type + context at a `_` hole.
  ## `line`, `col` are 0-based (LSP positions). Returns markdown, or ""
  ## when no hole sits at the position or the document does not elaborate.
  try:
    let (_, ms, _, _) = elabCheckHoles(src)
    for h in ms.holes:
      # `_` is one char: 1-based loc.col maps to 0-based [col, col].
      if h.holeLoc.line == line + 1 and h.holeLoc.col - 1 == col:
        let goal = $(zonk(ms, h.holeGoal))
        var lines: seq[string] = @["```", "goal : " & goal, "```"]
        if h.holeCtx.len > 0:
          lines.add("**context**")
          for (n, t) in h.holeCtx:  # innermost-first
            lines.add("- `" & n & " : " & $(zonk(ms, t)) & "`")
        return lines.join("\n")
  except ParseError, ElabError:
    discard
  ""

proc handleMessage*(server: var LspServer, msg: JsonNode): JsonNode =
  ## Handle one incoming message; returns the outgoing message, or nil
  ## when there is no response (e.g. `initialized`, `exit` handled by caller).
  if msg.isNil or "method" notin msg:
    return nil
  let meth = msg["method"].getStr()
  case meth
  of "initialize":
    let id = msg["id"]
    return %*{
      "jsonrpc": "2.0",
      "id": id,
      "result": {
        "capabilities": {
          "textDocumentSync": 1,  # Full document sync
          "hoverProvider": true   # Issue #58: goals at holes
        }
      }
    }
  of "initialized":
    return nil  # no-op
  of "textDocument/didOpen":
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let text = msg["params"]["textDocument"]["text"].getStr()
    server.documents[uri] = text
    return publishDiagnostics(server, uri)
  of "textDocument/didChange":
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let text = msg["params"]["contentChanges"][0]["text"].getStr()
    server.documents[uri] = text
    return publishDiagnostics(server, uri)
  of "textDocument/hover":
    let id = msg["id"]
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let line = msg["params"]["position"]["line"].getInt()
    let col = msg["params"]["position"]["character"].getInt()
    if uri notin server.documents:
      return %*{"jsonrpc": "2.0", "id": id, "result": nil}
    let md = hoverAt(server.documents[uri], line, col)
    if md == "":
      return %*{"jsonrpc": "2.0", "id": id, "result": nil}
    return %*{
      "jsonrpc": "2.0",
      "id": id,
      "result": {"contents": {"kind": "markdown", "value": md}}
    }
  of "shutdown":
    let id = msg["id"]
    return %*{"jsonrpc": "2.0", "id": id, "result": nil}
  of "exit":
    return nil  # caller quits
  else:
    # Unknown method: respond with error if it has an id
    if "id" in msg:
      return %*{
        "jsonrpc": "2.0",
        "id": msg["id"],
        "error": {"code": -32601, "message": "Method not found"}
      }
    return nil

when isMainModule:
  var server = LspServer(documents: initTable[string, string]())
  while true:
    let msg = readMessage()
    if msg.isNil:
      break
    let resp = handleMessage(server, msg)
    if not resp.isNil:
      writeMessage(resp)
    if not msg.isNil and "method" in msg and msg["method"].getStr() == "exit":
      quit(0)
