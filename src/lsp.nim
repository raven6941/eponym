# lsp.nim — Minimal LSP server for Eponym (Experiment 7)
#
# Exposes the elaborator via the Language Server Protocol:
# - Diagnostics: parse and elaboration errors at surface locations
#
# This is a minimal version: stdio JSON-RPC, textDocumentSync only.
# Hover, code actions, and incremental sync are future work.
#
# Usage: nim c -r --path:src src/lsp.nim
# Then configure your editor to use it for .ep files.

import json
import strutils
import tables
import elab
import preterm
import parse_surf

type
  LspServer = object
    documents: Table[string, string]  # uri -> text

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

proc publishDiagnostics(server: var LspServer, uri: string) =
  ## Elaborate the document and publish diagnostics.
  let text = server.documents[uri]
  try:
    discard elabCheck(text)
    # Success: clear diagnostics
    writeMessage(%*{
      "jsonrpc": "2.0",
      "method": "textDocument/publishDiagnostics",
      "params": {"uri": uri, "diagnostics": []}
    })
  except ParseError as e:
    let notif = makeDiagnostic(uri, e.loc.line, e.loc.col, e.msg)
    writeMessage(%*{
      "jsonrpc": "2.0",
      "method": "textDocument/publishDiagnostics",
      "params": notif
    })
  except ElabError as e:
    let notif = makeDiagnostic(uri, e.loc.line, e.loc.col, e.msg)
    writeMessage(%*{
      "jsonrpc": "2.0",
      "method": "textDocument/publishDiagnostics",
      "params": notif
    })

proc handleMessage(server: var LspServer, msg: JsonNode) =
  if msg.isNil or "method" notin msg:
    return
  let meth = msg["method"].getStr()
  case meth
  of "initialize":
    let id = msg["id"]
    writeMessage(%*{
      "jsonrpc": "2.0",
      "id": id,
      "result": {
        "capabilities": {
          "textDocumentSync": 1  # Full document sync
        }
      }
    })
  of "initialized":
    discard  # no-op
  of "textDocument/didOpen":
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let text = msg["params"]["textDocument"]["text"].getStr()
    server.documents[uri] = text
    publishDiagnostics(server, uri)
  of "textDocument/didChange":
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let text = msg["params"]["contentChanges"][0]["text"].getStr()
    server.documents[uri] = text
    publishDiagnostics(server, uri)
  of "shutdown":
    let id = msg["id"]
    writeMessage(%*{"jsonrpc": "2.0", "id": id, "result": nil})
  of "exit":
    quit(0)
  else:
    # Unknown method: ignore (or respond with error if it has an id)
    if "id" in msg:
      writeMessage(%*{
        "jsonrpc": "2.0",
        "id": msg["id"],
        "error": {"code": -32601, "message": "Method not found"}
      })

when isMainModule:
  var server = LspServer(documents: initTable[string, string]())
  while true:
    let msg = readMessage()
    if msg.isNil:
      break
    handleMessage(server, msg)
