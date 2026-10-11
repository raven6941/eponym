# lsp.nim — Minimal LSP server for Eponym (Experiment 7)
#
# Exposes the elaborator via the Language Server Protocol:
# - Diagnostics: parse and elaboration errors at surface locations
# - Shed status (issue #134): white/yellow/brown per shed, read from the
#   `<nimfile>.sheds.json` sidecar the shedsBlock macro writes; published
#   as diagnostics (yellow -> Warning, brown -> Error, white -> none)
# - Hover (issue #58): goal type + context at `_` holes
# - Code actions (issue #58): refine, case-split, give at holes
#
# This is a minimal version: stdio JSON-RPC, full-document sync.
# Incremental sync is future work.
#
# Mock-session convention: `textDocument/codeAction` accepts non-standard
# optional params `variable` (name to case-split) and `term` (refine/give
# candidate). A real client would fill these from the goal buffer UI.
#
# Usage: nim c -r --path:src src/lsp.nim
# Then configure your editor to use it for .ep files.

import json
import strutils
import tables
import os  # fileExists (issue #134: shed sidecar)
import elab
import preterm
import ett_init  # `$` for Term (issue #58)
import parse_surf
import unify  # HoleInfo, zonk (issue #58)
import sheds  # ShedInfo, ShedStatus, sidecarPath, readShedSidecarEx (issue #134)
import shed_layout  # Box, layoutShed, boxToJson (issue #135)

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

# --- issue #134: shed status diagnostics ----------------------------------

proc uriToPath(uri: string): string =
  ## `file:///abs/path` -> `/abs/path`.
  if uri.startsWith("file://"): uri[len("file://") .. ^1]
  else: uri

proc shedDiagnostics*(uri: string): JsonNode =
  ## Per-shed status diagnostics for a `.nim` document, from its
  ## `<nimfile>.sheds.json` sidecar: yellow -> Warning ("stuck"),
  ## brown -> Error, white -> no diagnostic. Returns nil when no sidecar
  ## exists (the macro has not compiled this file yet).
  let sc = sidecarPath(uriToPath(uri))
  if not fileExists(sc):
    return nil
  let (sheds, errMsg) = readShedSidecarEx(sc)
  var diags = newJArray()
  for s in sheds:
    let rng = %*{
      "start": {"line": s.nimLine - 1, "character": s.nimCol - 1},
      "end": {"line": s.nimLine - 1, "character": s.nimCol}}
    case s.status
    of ssYellow:
      diags.add(%*{
        "range": rng,
        "severity": 2,  # Warning
        "message": "shed '" & s.name & "': stuck (yellow); goal: " & s.goal,
        "source": "eponym"})
    of ssBrown:
      var msg = "shed '" & s.name & "': elaboration failed (brown)"
      if errMsg != "":
        msg &= ": " & errMsg
      diags.add(%*{
        "range": rng,
        "severity": 1,  # Error
        "message": msg,
        "source": "eponym"})
    of ssWhite:
      discard  # white: no diagnostic
  %*{"uri": uri, "diagnostics": diags}

# --- issue #135: 2D box layout of a shed's proof state ----------------------

proc shedLayout*(uri, shedName: string): JsonNode =
  ## `eponym/shedLayout` (issue #135): the box tree for a shed with holes,
  ## laid out Epigram deduction-style (context above the rule, the hole
  ## below it). Returns nil when no sidecar exists or the shed is unknown;
  ## `handleMessage` turns the latter into an error response.
  let sc = sidecarPath(uriToPath(uri))
  if not fileExists(sc):
    return nil
  for s in readShedSidecar(sc):
    if s.name == shedName:
      return %*{"box": boxToJson(layoutShed(s))}
  nil

proc publishDiagnostics(server: var LspServer, uri: string): JsonNode =
  ## Elaborate the document and build the publishDiagnostics notification.
  ## Returns nil only when the document is unknown (no notification sent).
  if uri notin server.documents:
    return nil
  # Issue #134: `.nim` documents carry Epigram-style sheds; their status
  # comes from the sidecar the shedsBlock macro wrote at compile time,
  # re-read on every didOpen/didChange so the editor tracks status as the
  # Nim compiler re-runs the macro. (A `.nim` file is not Eponym source,
  # so elaborating its text directly would only yield a parse error.)
  if uri.endsWith(".nim"):
    let sd = shedDiagnostics(uri)
    if not sd.isNil:
      return %*{
        "jsonrpc": "2.0",
        "method": "textDocument/publishDiagnostics",
        "params": sd
      }
    # No sidecar (yet): fall through to the Eponym-source path, which
    # reports the document as unparseable -- same as before #134.
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

proc findHoleAt*(ms: MetaStore, line, col: int): int =
  ## 0-based LSP position -> index into ms.holes, or -1.
  ## `_` is one char: 1-based loc.col maps to 0-based [col, col].
  for i, h in ms.holes:
    if h.holeLoc.line == line + 1 and h.holeLoc.col - 1 == col:
      return i
  -1

proc hoverAt*(src: string, line, col: int): string =
  ## Issue #58: goal type + context at a `_` hole.
  ## `line`, `col` are 0-based (LSP positions). Returns markdown, or ""
  ## when no hole sits at the position or the document does not elaborate.
  try:
    let (_, ms, _, _) = elabCheckHoles(src)
    let i = findHoleAt(ms, line, col)
    if i >= 0:
      let h = ms.holes[i]
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

# --- code actions: refine, case-split, give (issue #58, steps 2-4) --------

proc typeHeadDataName(ms: MetaStore, ty: Term): string =
  ## Zonk and strip the application spine; when the head is a `tR`
  ## registered as a datatype (issue #80 ctorTable), return its surface
  ## name, else "".
  var t = zonk(ms, ty)
  while t != nil and t.kind == tApp:
    t = t.fn
  if t != nil and t.kind == tR and t.refId in ms.ctorTable.dataNames:
    return ms.ctorTable.dataNames[t.refId]
  ""

proc freshen(base: string, used: seq[string]): string =
  result = base
  var k = 1
  while result in used:
    result = base & $k
    inc k

proc caseSplitAt*(src: string, line, col: int, varName: string):
    tuple[ok: bool, why: string, startLine, startChar, endLine, endChar: int,
          newText: string] =
  ## Issue #58: case-split on `varName` (a datatype-typed variable in the
  ## hole's context) at the hole at 0-based (line, col). Rewrites the
  ## enclosing `proc` into a clause-style `def` (#32) with one covering
  ## clause per constructor, each RHS a fresh `_`. The split variable must
  ## be the first explicit argument (the clause machinery eliminates on
  ## the first explicit Pi domain). On failure ok=false and `why` names
  ## the reason.
  try:
    let (_, ms, _, _) = elabCheckHoles(src)
    let hi = findHoleAt(ms, line, col)
    if hi < 0:
      return (false, "no hole at the requested position", 0,0,0,0, "")
    let h = ms.holes[hi]
    var varTy: Term = nil
    for (nm, ty) in h.holeCtx:
      if nm == varName: varTy = ty
    if varTy.isNil:
      return (false, "'" & varName & "' is not in scope at the hole", 0,0,0,0, "")
    let dataName = typeHeadDataName(ms, varTy)
    if dataName == "":
      return (false, "'" & varName & "' does not have a datatype type", 0,0,0,0, "")
    let decls = parseProgram(src)
    var ctors: seq[DataCtor] = @[]
    for d in decls:
      if d.kind == dkData and d.dname == dataName:
        ctors = d.ctors
        break
    if ctors.len == 0:
      return (false, "no constructors found for '" & dataName & "'", 0,0,0,0, "")
    # Enclosing `proc`: the dkDef with the greatest start line at-or-above
    # the hole (1-based locs).
    var procDef: SurfDef
    var procLine1 = -1
    var procIdx = -1
    for i, d in decls:
      if d.kind == dkDef and d.def.loc.line <= h.holeLoc.line and
         d.def.loc.line > procLine1:
        procLine1 = d.def.loc.line
        procDef = d.def
        procIdx = i
    if procIdx < 0:
      return (false, "hole is not inside a `proc` body", 0,0,0,0, "")
    var explicitNames: seq[string] = @[]
    for b in procDef.tele:
      if not b.impl: explicitNames.add(b.name)
    var splitIdx = -1
    for i, nm in explicitNames:
      if nm == varName: splitIdx = i
    if splitIdx < 0:
      return (false, "'" & varName & "' is not an explicit argument of '" &
              procDef.name & "'", 0,0,0,0, "")
    if splitIdx != 0:
      return (false, "case-split needs '" & varName &
              "' as the first explicit argument (clause form eliminates " &
              "on the first explicit Pi domain)", 0,0,0,0, "")
    var used: seq[string] = @[]
    for (nm, _) in h.holeCtx: used.add(nm)
    var newLines: seq[string] = @[
      "def " & procDef.name & " : " & $desugarTy(procDef)]
    for c in ctors:
      var pat = c.name
      if c.tele.len > 0:
        var args: seq[string] = @[]
        for b in c.tele:
          let fresh = freshen(b.name, used)
          used.add(fresh)
          args.add(fresh)
        pat = "(" & c.name & " " & args.join(" ") & ")"
      var newPats: seq[string] = @[pat]
      for i in 1 ..< explicitNames.len: newPats.add(explicitNames[i])
      newLines.add("| " & newPats.join(" ") & " = _")
    # Replace the whole proc decl: from its first line to the line before
    # the next decl (or end of file).
    let lines = src.splitLines()
    let startLine0 = procLine1 - 1
    var endLine0 = lines.high
    for i in procIdx + 1 ..< decls.len:
      let dl = case decls[i].kind
        of dkDef: decls[i].def.loc.line
        of dkPostulate, dkElim: decls[i].dloc.line
        of dkRed: decls[i].rloc.line
        of dkData: decls[i].daloc.line
        of dkClauses: decls[i].clausesDef.loc.line
        of dkImport: decls[i].iloc.line  # issue #49: import decls have no body to split
      if dl > procLine1:
        endLine0 = dl - 2
        break
    (true, "", startLine0, 0, endLine0, lines[endLine0].len,
     newLines.join("\n"))
  except ParseError as e:
    (false, "parse error: " & e.msg, 0,0,0,0, "")

proc fillHoleAt*(src: string, line, col: int, term: string):
    tuple[ok: bool, why: string, errLine, errCol: int,
          startLine, startChar, endLine, endChar: int, newSrc: string,
          holesInRegion: int] =
  ## Replace the `_` at 0-based (line, col) with `term` and re-elaborate
  ## hole-tolerantly. ok=false when the document no longer parses or the
  ## filled region fails to elaborate (why carries the message, errLine/
  ## errCol its 0-based location). holesInRegion counts holes left inside
  ## the replaced span (refine tolerates them; give rejects them).
  let lines = src.splitLines()
  if line < 0 or line >= lines.len or col < 0 or col >= lines[line].len or
     lines[line][col] != '_':
    return (false, "no '_' hole at the requested position", 0, 0,
            0,0,0,0, "", 0)
  let newLine = lines[line][0 ..< col] & term & lines[line][col + 1 .. ^1]
  var newLines = lines
  newLines[line] = newLine
  let newSrc = newLines.join("\n")
  # End of the replaced span, 1-based (line, col-exclusive), walking the term.
  var eLine = line + 1
  var eCol = col + 1
  for ch in term:
    if ch == '\n': inc eLine; eCol = 1
    else: inc eCol
  let sLine = line + 1
  let sCol = col + 1
  try:
    let (_, ms, errLoc, errMsg) = elabCheckHoles(newSrc)
    if errMsg != "":
      return (false, errMsg, errLoc.line - 1, errLoc.col - 1,
              0,0,0,0, "", 0)
    var inRegion = 0
    for hh in ms.holes:
      let afterStart = hh.holeLoc.line > sLine or
        (hh.holeLoc.line == sLine and hh.holeLoc.col >= sCol)
      let beforeEnd = hh.holeLoc.line < eLine or
        (hh.holeLoc.line == eLine and hh.holeLoc.col < eCol)
      if afterStart and beforeEnd: inc inRegion
    # Edit range is the original `_` char in the pre-edit document; the
    # (sLine..eLine) span above is only for the holes-in-region check.
    (true, "", 0, 0, line, col, line, col + 1, newSrc, inRegion)
  except ParseError as e:
    (false, "parse error: " & e.msg, e.loc.line - 1, e.loc.col - 1,
     0,0,0,0, "", 0)

proc editJson(uri: string, sLine, sChar, eLine, eChar: int,
              newText: string): JsonNode =
  %*{
    "changes": {
      uri: [{
        "range": {
          "start": {"line": sLine, "character": sChar},
          "end": {"line": eLine, "character": eChar}
        },
        "newText": newText
      }]
    }
  }

proc codeActionError(id: JsonNode, msg: string): JsonNode =
  %*{"jsonrpc": "2.0", "id": id,
      "error": {"code": -32602, "message": msg}}

proc codeActionsAt*(src, uri: string, line, col: int, variable, term: string,
                    id: JsonNode): JsonNode =
  ## Build the `textDocument/codeAction` response at 0-based (line, col).
  ## `variable` requests a case-split; `term` requests refine (+ give).
  ## An explicitly requested action that fails validation becomes an
  ## error response naming the reason; otherwise the applicable actions
  ## are listed (Agda-style: the client applies the edit, re-syncs, and
  ## re-hovers to see the new goal state).
  var actions: seq[JsonNode] = @[]
  if variable != "":
    let cs = caseSplitAt(src, line, col, variable)
    if not cs.ok:
      return codeActionError(id, "case-split rejected: " & cs.why)
    actions.add(%*{
      "title": "case-split " & variable,
      "kind": "refactor",
      "edit": editJson(uri, cs.startLine, cs.startChar, cs.endLine,
                       cs.endChar, cs.newText)
    })
  elif term != "":
    let f = fillHoleAt(src, line, col, term)
    if not f.ok:
      return codeActionError(id, "refine rejected at " &
        $(f.errLine + 1) & ":" & $(f.errCol + 1) & ": " & f.why)
    actions.add(%*{
      "title": "refine hole",
      "kind": "refactor",
      "edit": editJson(uri, f.startLine, f.startChar, f.endLine, f.endChar,
                       term)
    })
    if f.holesInRegion == 0:
      actions.add(%*{
        "title": "give " & term,
        "kind": "refactor",
        "edit": editJson(uri, f.startLine, f.startChar, f.endLine, f.endChar,
                         term)
      })
    # else: the term leaves holes behind — only refine is offered.
  else:
    # No explicit request: offer a case-split for every datatype-typed
    # variable in scope at the hole.
    try:
      let (_, ms, _, _) = elabCheckHoles(src)
      let hi = findHoleAt(ms, line, col)
      if hi >= 0:
        for (nm, ty) in ms.holes[hi].holeCtx:
          if typeHeadDataName(ms, ty) != "":
            let cs = caseSplitAt(src, line, col, nm)
            if cs.ok:
              actions.add(%*{
                "title": "case-split " & nm,
                "kind": "refactor",
                "edit": editJson(uri, cs.startLine, cs.startChar, cs.endLine,
                                 cs.endChar, cs.newText)
              })
    except ParseError, ElabError:
      discard
  %*{"jsonrpc": "2.0", "id": id, "result": actions}

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
          "hoverProvider": true,  # Issue #58: goals at holes
          "codeActionProvider": true  # Issue #58: refine/case-split/give
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
  of "textDocument/codeAction":
    let id = msg["id"]
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    if uri notin server.documents:
      return codeActionError(id, "unknown document")
    var line = -1
    var col = -1
    if "range" in msg["params"]:
      line = msg["params"]["range"]["start"]["line"].getInt()
      col = msg["params"]["range"]["start"]["character"].getInt()
    elif "position" in msg["params"]:
      line = msg["params"]["position"]["line"].getInt()
      col = msg["params"]["position"]["character"].getInt()
    var variable = ""
    var term = ""
    if "variable" in msg["params"]:
      variable = msg["params"]["variable"].getStr()
    if "term" in msg["params"]:
      term = msg["params"]["term"].getStr()
    return codeActionsAt(server.documents[uri], uri, line, col, variable,
                         term, id)
  of "eponym/shedLayout":
    let id = msg["id"]
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let shedName = msg["params"]["shedName"].getStr()
    let res = shedLayout(uri, shedName)
    if res.isNil:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "no layout: unknown shed '" & shedName &
                            "' or no sheds sidecar for " & uri}}
    return %*{"jsonrpc": "2.0", "id": id, "result": res}
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
