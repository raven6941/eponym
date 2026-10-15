# lsp.nim — Minimal LSP server for Eponym (Experiment 7)
#
# Exposes the elaborator via the Language Server Protocol:
# - Diagnostics: parse and elaboration errors at surface locations
# - Shed status (issue #134): white/yellow/brown per shed, read from the
#   `<nimfile>.sheds.json` sidecar the shedsBlock macro writes; published
#   as diagnostics (yellow -> Warning, brown -> Error, white -> none)
# - Hover (issue #58): goal type + context at `_` holes
# - Code actions (issue #58): refine, case-split, give at holes
# - `eponym/refineShed` (issue #137): the server-owned refine round-trip
#   for real `.nim` shed documents -- fill the hole in the macro-recorded
#   generated source, refresh statuses, rewrite the sidecar, and return
#   the term plus the `.nim` splice position for the client
# - `eponym/shedNames` (issue #137): shed names from a `.nim` sidecar, for
#   client pickers
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
import eponym_init  # `$` for Term (issue #58)
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
      # Issue #139: name-resolving pretty-printer. Binder names come from
      # the hole context (innermost-first, matching Ctx); global names come
      # from ms.refNames, populated by the elaborator at global
      # registration. Unknown refIds keep the `R<n>` fallback.
      var ctx: Ctx = @[]
      for (n, t) in h.holeCtx:
        ctx.add(CtxEntry(name: n, ty: zonk(ms, t), qty: qOmega))
      let goal = prettyTerm(zonk(ms, h.holeGoal), ctx, ms.refNames, ms.recordFields)
      var lines: seq[string] = @["```", "goal : " & goal, "```"]
      if h.holeCtx.len > 0:
        lines.add("**context**")
        for (n, t) in h.holeCtx:  # innermost-first
          lines.add("- `" & n & " : " &
            prettyTerm(zonk(ms, t), ctx, ms.refNames, ms.recordFields) & "`")
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
        of dkInterface: decls[i].ifloc.line  # issue #177
        of dkCommand: decls[i].cloc.line      # issue #177
        of dkRecord: decls[i].recloc.line    # issue #37
      if dl > procLine1:
        endLine0 = dl - 2
        break
    (true, "", startLine0, 0, endLine0, lines[endLine0].len,
     newLines.join("\n"))
  except ParseError as e:
    (false, "parse error: " & e.msg, 0,0,0,0, "")

proc fillHoleAt*(src: string, line, col: int, term: string,
                baseDir = ""):
    tuple[ok: bool, why: string, errLine, errCol: int,
          startLine, startChar, endLine, endChar: int, newSrc: string,
          holesInRegion: int] =
  ## Replace the `_` at 0-based (line, col) with `term` and re-elaborate
  ## hole-tolerantly. ok=false when the document no longer parses or the
  ## filled region fails to elaborate (why carries the message, errLine/
  ## errCol its 0-based location). holesInRegion counts holes left inside
  ## the replaced span (refine tolerates them; give rejects them).
  ## `baseDir` (issue #137): when non-empty, elaboration resolves
  ## `import` declarations relative to it (elabCheckHolesDir semantics,
  ## as the shedsBlock macro does); empty keeps the old elabCheckHoles
  ## behavior for `.ep` documents.
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
    let (_, ms, errLoc, errMsg) =
      if baseDir == "": elabCheckHoles(newSrc)
      else: elabCheckHolesDir(newSrc, baseDir)
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

# --- issue #137: server-owned refine round-trip for `.nim` sheds -------

proc shedNames*(uri: string): seq[string] =
  ## `eponym/shedNames`: shed names from the `.nim` document's sidecar, so
  ## a client can offer a picker instead of a free-form name box. Empty
  ## when no sidecar exists (the macro has not compiled this file yet).
  let sc = sidecarPath(uriToPath(uri))
  if not fileExists(sc):
    return @[]
  for s in readShedSidecar(sc):
    result.add(s.name)

proc refineShed*(nimFile, shedName, term: string):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          status: string, yellowCount: int] =
  ## Issue #137: the server-owned refine round-trip for real `.nim` shed
  ## documents -- the #136 gap. The #58 `textDocument/codeAction` path
  ## elaborates document text as Eponym source, which a `.nim` file is
  ## not; here the client sends only (shedName, term) and the server does
  ## the whole loop: fill the hole in the macro-recorded generated source
  ## (`ShedInfo.genSrc`), refresh statuses, rewrite the sidecar, and
  ## return the term plus the `.nim` splice position (`nimLine`, `nimCol`:
  ## 1-based start of the `![...]` node -- the client replaces that node,
  ## a single-line span, with the term).
  ##
  ## Sheds from other shedsBlock expansions in the same file are
  ## identified by sharing the block's `genSrc` string: their sources are
  ## updated to the filled source and their hole lines shifted past a
  ## multi-line fill, while sheds from other blocks are untouched.
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)",
            "", 0, 0, "", 0)
  let (sheds0, errMsg0) = readShedSidecarEx(sc)
  var sheds = sheds0
  var si = -1
  for i in 0 ..< sheds.len:
    if sheds[i].name == shedName:
      si = i
      break
  if si < 0:
    return (false, "unknown shed '" & shedName & "'", "", 0, 0, "", 0)
  let oldSrc = sheds[si].genSrc
  if oldSrc == "":
    return (false, "shed '" & shedName &
            "': no generated source recorded (sidecar predates #137; " &
            "recompile)", "", 0, 0, "", 0)
  if sheds[si].status != ssYellow:
    return (false, "shed '" & shedName & "' is not refinable (status " &
            shedStatusToStr(sheds[si].status) & ")", "", 0, 0, "", 0)
  let baseDir = parentDir(nimFile)
  # Locate the hole in the recorded source: exact (line, col) when the
  # column is known, else the first line match (the #134 rule).
  var holeLine1 = -1
  var holeCol1 = -1
  try:
    let r = elabCheckHolesDir(oldSrc, baseDir)
    var best = -1
    for k, h in r.ms.holes:
      if h.holeLoc.line != sheds[si].holeLine: continue
      if best < 0: best = k  # first line match: the fallback
      if sheds[si].holeCol > 0 and h.holeLoc.col == sheds[si].holeCol:
        best = k
        break  # exact match wins
    if best < 0:
      return (false, "shed '" & shedName &
              "': hole no longer open in the recorded source " &
              "(sidecar stale? recompile)", "", 0, 0, "", 0)
    holeLine1 = r.ms.holes[best].holeLoc.line
    holeCol1 = r.ms.holes[best].holeLoc.col
  except ParseError as e:
    return (false, "recorded source no longer parses: " & e.msg,
            "", 0, 0, "", 0)
  let f = fillHoleAt(oldSrc, holeLine1 - 1, holeCol1 - 1, term, baseDir)
  if not f.ok:
    return (false, "refine rejected: " & f.why, "", 0, 0, "", 0)
  # A multi-line fill shifts later sheds' generated-source lines; the
  # filled shed keeps its line (the fill starts there) and is re-matched
  # by refreshShedStatuses below.
  let newSrc = f.newSrc
  let filledLine = sheds[si].holeLine
  let linesAdded = term.count('\n')
  for i in 0 ..< sheds.len:
    if sheds[i].genSrc == oldSrc:
      sheds[i].genSrc = newSrc
      if sheds[i].holeLine > filledLine:
        sheds[i].holeLine += linesAdded
  refreshShedStatuses(sheds, newSrc, baseDir, onlyGenSrc = newSrc)
  writeShedSidecar(nimFile, sheds, errMsg0)  # keep the doc-level message
  var yellowCount = 0
  for s in sheds:
    if s.status == ssYellow: inc yellowCount
  (true, "", term, sheds[si].nimLine, sheds[si].nimCol,
   shedStatusToStr(sheds[si].status), yellowCount)

proc caseSplitShed*(nimFile, shedName, variable: string):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          subSheds: seq[string]] =
  ## Issue #209: shed-aware case-split (term-level via eliminators).
  ##
  ## The `.ep` `textDocument/codeAction` path rewrites a `proc` into a
  ## clause-style `def`, which cannot round-trip through the nim `![...]`
  ## node (an expression position; a clause-def is not a term and not
  ## valid Nim). Instead, fill the shed's hole with an eliminator
  ## application whose method holes become fresh sub-sheds:
  ##   `![isZeroBody]` --case-split n--> `natElim(lam(u, Nat, Bool),
  ##    ![isZeroBody_zero], ![isZeroBody_suc], n)`
  ## The returned `term` is nim-syntax text for the client to splice over
  ## the `![shedName]` node; `subSheds` are the fresh sub-shed names.
  ## Only non-parameterized, non-indexed datatypes are supported for now.
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)",
            "", 0, 0, @[])
  let (sheds0, errMsg0) = readShedSidecarEx(sc)
  var si = -1
  for i in 0 ..< sheds0.len:
    if sheds0[i].name == shedName:
      si = i
      break
  if si < 0:
    return (false, "unknown shed '" & shedName & "'", "", 0, 0, @[])
  let oldSrc = sheds0[si].genSrc
  if oldSrc == "":
    return (false, "shed '" & shedName &
            "': no generated source recorded (sidecar predates #137; " &
            "recompile)",
            "", 0, 0, @[])
  if sheds0[si].status != ssYellow:
    return (false, "shed '" & shedName & "' is not open (status " &
            shedStatusToStr(sheds0[si].status) & ")", "", 0, 0, @[])
  let baseDir = parentDir(nimFile)
  # Locate the hole and get its context.
  var ms: MetaStore
  var holeIdx = -1
  try:
    let r = elabCheckHolesDir(oldSrc, baseDir)
    ms = r.ms
    var best = -1
    for k, h in r.ms.holes:
      if h.holeLoc.line != sheds0[si].holeLine: continue
      if best < 0: best = k
      if sheds0[si].holeCol > 0 and h.holeLoc.col == sheds0[si].holeCol:
        best = k
        break
    if best < 0:
      return (false, "shed '" & shedName &
              "': hole no longer open in the recorded source " &
              "(sidecar stale? recompile)", "", 0, 0, @[])
    holeIdx = best
  except ParseError as e:
    return (false, "recorded source no longer parses: " & e.msg,
            "", 0, 0, @[])
  let h = ms.holes[holeIdx]
  var varTy: Term = nil
  for (nm, ty) in h.holeCtx:
    if nm == variable: varTy = ty
  if varTy.isNil:
    return (false, "'" & variable & "' is not in scope at the hole",
            "", 0, 0, @[])
  # The variable's type must be a plain datatype (tR, no params/indices).
  var ty = zonk(ms, varTy)
  if ty == nil or ty.kind != tR:
    return (false, "'" & variable &
            "' does not have a simple datatype type " &
            "(parameterized/indexed datatypes not yet supported)",
            "", 0, 0, @[])
  let dataRef = ty.refId
  if dataRef notin ms.ctorTable.dataNames:
    return (false, "'" & variable & "' does not have a datatype type",
            "", 0, 0, @[])
  let dataName = ms.ctorTable.dataNames[dataRef]
  let elimName = elimNameFor(dataName)
  # Constructor names for the sub-sheds.
  var ctorNames: seq[string] = @[]
  if dataRef in ms.ctorTable.dataCtors:
    for cid in ms.ctorTable.dataCtors[dataRef]:
      ctorNames.add(ms.ctorTable.ctorNames[cid])
  if ctorNames.len == 0:
    return (false, "datatype '" & dataName & "' has no constructors",
            "", 0, 0, @[])
  # Fresh sub-shed names.
  var used: seq[string] = @[]
  for s in sheds0: used.add(s.name)
  var subSheds: seq[string] = @[]
  for cn in ctorNames:
    var nm = shedName & "_" & cn
    var k = 1
    while nm in used:
      nm = shedName & "_" & cn & $k
      inc k
    used.add(nm)
    subSheds.add(nm)
  # Build the terms. The Eponym term (for validation) uses `_` holes;
  # the nim term uses `![sub]` shed nodes so recompile discovers them.
  let goalStr = sheds0[si].goal
  if goalStr == "":
    return (false, "shed '" & shedName & "': no goal recorded",
            "", 0, 0, @[])
  let motiveEp = "(lam (u : " & dataName & "). " & goalStr & ")"
  let motiveNim = "lam(u, " & dataName & ", " & goalStr & ")"
  var epArgs: seq[string] = @[motiveEp]
  var nimArgs: seq[string] = @[motiveNim]
  for ss in subSheds:
    epArgs.add("_")
    nimArgs.add("![" & ss & "]")
  epArgs.add(variable)
  nimArgs.add(variable)
  let epTerm = elimName & " " & epArgs.join(" ")
  let nimTerm = elimName & "(" & nimArgs.join(", ") & ")"
  # Validate: fill the hole in a copy of the source and re-elaborate.
  # (Catches unparseable motives/goals before touching the nim file.)
  let f = fillHoleAt(oldSrc, sheds0[si].holeLine - 1, sheds0[si].holeCol - 1,
                     epTerm, baseDir)
  if not f.ok:
    return (false, "case-split rejected: " & f.why, "", 0, 0, @[])
  (true, "", nimTerm, sheds0[si].nimLine, sheds0[si].nimCol, subSheds)

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
  of "eponym/shedNames":
    let id = msg["id"]
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    var arr = newJArray()
    for nm in shedNames(uri): arr.add(%nm)
    return %*{"jsonrpc": "2.0", "id": id, "result": arr}
  of "eponym/refineShed":
    let id = msg["id"]
    if "textDocument" notin msg["params"] or "shedName" notin msg["params"] or
       "term" notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "eponym/refineShed needs " &
                            "textDocument.uri, shedName, term"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let shedName = msg["params"]["shedName"].getStr()
    let term = msg["params"]["term"].getStr()
    let r = refineShed(uriToPath(uri), shedName, term)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id,
              "result": {"shedName": shedName, "term": r.term,
                         "nimLine": r.nimLine, "nimCol": r.nimCol,
                         "status": r.status, "yellowCount": r.yellowCount}}
  of "eponym/caseSplitShed":
    let id = msg["id"]
    if "textDocument" notin msg["params"] or "shedName" notin msg["params"] or
       "variable" notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "eponym/caseSplitShed needs " &
                            "textDocument.uri, shedName, variable"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let shedName = msg["params"]["shedName"].getStr()
    let variable = msg["params"]["variable"].getStr()
    let r = caseSplitShed(uriToPath(uri), shedName, variable)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id,
              "result": {"shedName": shedName, "term": r.term,
                         "nimLine": r.nimLine, "nimCol": r.nimCol,
                         "subSheds": r.subSheds}}
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
