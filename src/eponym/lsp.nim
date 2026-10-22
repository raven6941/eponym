# lsp.nim — Minimal LSP server for Eponym (Experiment 7)
#
# Exposes the elaborator via the Language Server Protocol:
# - Diagnostics: parse and elaboration errors at surface locations
# - Shed status (issue #134): white/yellow/brown per shed, read from the
#   `<nimfile>.sheds.json` sidecar the shedsBlock macro writes; published
#   as diagnostics (yellow -> Warning, brown -> Error, white -> none)
# - Hover (issue #58): goal type + context at `?` holes
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
import algorithm
import sequtils
import strutils
import tables
import os  # fileExists (issue #134: shed sidecar)
import elab
import preterm
import eponym_init  # `$` for Term (issue #58)
import parse_surf
import unify  # HoleInfo, zonk (issue #58)
import sheds_mac  # shedGoalAndCtx for residual refinement holes
import sheds  # ShedInfo, semanticShedState, renderShedHover, sidecar IO
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
  ## Issue #58: goal type + context at a `?` hole.
  ## `line`, `col` are 0-based (LSP positions). Returns markdown, or ""
  ## when no hole sits at the position or the document does not elaborate.
  try:
    let (_, ms, _, _) = elabCheckHoles(src)
    let i = findHoleAt(ms, line, col)
    if i >= 0:
      return renderShedHover(ms, semanticShedState(ms, ms.holes[i]))
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

proc applicationSpine(term: Term): tuple[head: Term, args: seq[Term]] =
  result.head = term
  while result.head != nil and result.head.kind == tApp:
    result.args.add(result.head.arg)
    result.head = result.head.fn
  result.args.reverse()

proc freshen(base: string, used: seq[string]): string

proc nimTypeExpr(term: Term, ctx: seq[HoleContextBinder],
                 ms: MetaStore, rendered: var string): bool =
  ## Render the surface-compatible type-level fragment needed to replay
  ## datatype parameters in a generated Nim shed expression. Data families use
  ## bracket applications; constructors nested inside an index use normal
  ## calls after their family parameters.
  if term == nil: return false
  case term.kind
  of tR:
    if term.refId notin ms.refNames: return false
    rendered = ms.refNames[term.refId]
    true
  of tV:
    if term.idx < 0 or term.idx >= ctx.len or ctx[term.idx].name == "_":
      return false
    rendered = ctx[term.idx].name
    true
  of tInt:
    rendered = $term.intVal
    true
  of tNatLit:
    rendered = $term.natLitVal
    true
  of tApp:
    let spine = applicationSpine(term)
    var argTexts: seq[string] = @[]
    for arg in spine.args:
      var argText = ""
      if not nimTypeExpr(zonk(ms, arg), ctx, ms, argText): return false
      argTexts.add(argText)
    if spine.head == nil or spine.head.kind != tR or
        spine.head.refId notin ms.refNames:
      return false
    var headName = ms.refNames[spine.head.refId]
    if spine.head.refId in ms.ctorTable.dataNames:
      rendered = headName & "[" & argTexts.join(", ") & "]"
    elif spine.head.refId in ms.ctorTable.ctorData:
      let family = ms.ctorTable.ctorData[spine.head.refId]
      let nParams = ms.ctorTable.dataParamCounts.getOrDefault(family, -1)
      if nParams < 0 or argTexts.len < nParams: return false
      var paramTexts: seq[string] = @[]
      var valueTexts: seq[string] = @[]
      if nParams > 0: paramTexts = argTexts[0 ..< nParams]
      if argTexts.len > nParams: valueTexts = argTexts[nParams .. ^1]
      if nParams > 0: headName &= "[" & paramTexts.join(", ") & "]"
      if valueTexts.len > 0: headName &= "(" & valueTexts.join(", ") & ")"
      rendered = headName
    else:
      # Ordinary type constructors and type-level functions use Nim's
      # parenthesized call syntax; datatype families above use brackets.
      rendered = headName & "(" & argTexts.join(", ") & ")"
    true
  of tPi:
    var dom = ""
    if not nimTypeExpr(zonk(ms, term.dom), ctx, ms, dom): return false
    let requestedName = if term.scope.adv == "" or term.scope.adv == "_":
        "x"
      else: term.scope.adv
    let binderName = freshen(requestedName, ctx.mapIt(it.name))
    var bodyCtx = @[HoleContextBinder(name: binderName, ty: term.dom,
                                      qty: qOmega)]
    bodyCtx.add(ctx)
    var body = ""
    if not nimTypeExpr(zonk(ms, term.scope.bdy), bodyCtx, ms, body):
      return false
    rendered = "Pi(" & binderName & ", " & dom & ", " & body & ")"
    true
  of tSi:
    var dom = ""
    if not nimTypeExpr(zonk(ms, term.dom), ctx, ms, dom): return false
    let requestedName = if term.scope.adv == "" or term.scope.adv == "_":
        "x"
      else: term.scope.adv
    let binderName = freshen(requestedName, ctx.mapIt(it.name))
    var bodyCtx = @[HoleContextBinder(name: binderName, ty: term.dom,
                                      qty: qOmega)]
    bodyCtx.add(ctx)
    var body = ""
    if not nimTypeExpr(zonk(ms, term.scope.bdy), bodyCtx, ms, body):
      return false
    rendered = "Sig(" & binderName & ", " & dom & ", " & body & ")"
    true
  else:
    false

proc sameTerm(a, b: Term): bool =
  ## Structural equality for occurrence abstraction. This intentionally does
  ## not use definitional equality: the elaborator validates the final motive.
  if a == nil or b == nil: return a == b
  if a.kind != b.kind: return false
  case a.kind
  of tR: a.refId == b.refId
  of tV: a.idx == b.idx
  of tPi, tSi, tLam:
    a.impl == b.impl and a.erased == b.erased and a.qty == b.qty and
      sameTerm(a.dom, b.dom) and sameTerm(a.scope.bdy, b.scope.bdy)
  of tPair:
    sameTerm(a.pFst, b.pFst) and sameTerm(a.pSnd, b.pSnd) and
      sameTerm(a.pScope.bdy, b.pScope.bdy)
  of tApp: sameTerm(a.fn, b.fn) and sameTerm(a.arg, b.arg)
  of tFst, tSnd, tAbsurd: sameTerm(a.sub, b.sub)
  of tC: a.c == b.c
  of tLet:
    sameTerm(a.letVal, b.letVal) and sameTerm(a.letTy, b.letTy) and
      sameTerm(a.letScope.bdy, b.letScope.bdy)
  of tMeta:
    if a.metaId != b.metaId or a.metaSpine.len != b.metaSpine.len:
      return false
    for i in 0 ..< a.metaSpine.len:
      if not sameTerm(a.metaSpine[i], b.metaSpine[i]): return false
    true
  of tInt: a.intVal == b.intVal
  of tPrim: a.primOp == b.primOp and sameTerm(a.primTy, b.primTy)
  of tNatLit: a.natLitVal == b.natLitVal
  of tNatSing: a.natSingVal == b.natSingVal
  of tType: a.lvl == b.lvl

proc termSize(term: Term): int =
  if term == nil: return 0
  result = 1
  case term.kind
  of tPi, tSi, tLam:
    result += termSize(term.dom) + termSize(term.scope.bdy)
  of tPair:
    result += termSize(term.pFst) + termSize(term.pSnd) +
      termSize(term.pScope.bdy)
  of tApp: result += termSize(term.fn) + termSize(term.arg)
  of tFst, tSnd, tAbsurd: result += termSize(term.sub)
  of tLet:
    result += termSize(term.letVal) + termSize(term.letTy) +
      termSize(term.letScope.bdy)
  of tMeta:
    for arg in term.metaSpine: result += termSize(arg)
  of tPrim: result += termSize(term.primTy)
  of tR, tV, tC, tInt, tNatLit, tNatSing, tType: discard

proc replaceOccurrences(term, pattern: Term, replacement: int,
                        depth = 0): tuple[term: Term, count: int] =
  ## Replace exact occurrences of a root-context pattern by the motive index
  ## variable, respecting binders in the target.
  if term == nil: return (nil, 0)
  var shiftedPattern = pattern
  for _ in 0 ..< depth: shiftedPattern = weaken(shiftedPattern)
  if sameTerm(term, shiftedPattern):
    return (vv(replacement + depth), 1)
  template recur(child: Term, childDepth: int): untyped =
    replaceOccurrences(child, pattern, replacement, childDepth)
  case term.kind
  of tR, tV, tC, tInt, tNatLit, tNatSing, tType: (term, 0)
  of tPrim:
    let ty = recur(term.primTy, depth)
    (tmPrim(term.primOp, ty.term), ty.count)
  of tPi, tSi, tLam:
    let dom = recur(term.dom, depth)
    let bdy = recur(term.scope.bdy, depth + 1)
    let rebuilt = case term.kind
      of tPi: tmPi(dom.term, term.scope.adv, bdy.term, term.impl,
                   term.erased, term.qty, term.peg)
      of tSi: tmSi(dom.term, term.scope.adv, bdy.term, term.impl,
                   term.erased, term.qty)
      of tLam: tmLam(dom.term, term.scope.adv, bdy.term, term.impl,
                     term.erased, term.qty, term.peg)
      else: term
    (rebuilt, dom.count + bdy.count)
  of tPair:
    let fst = recur(term.pFst, depth)
    let snd = recur(term.pSnd, depth)
    let bdy = recur(term.pScope.bdy, depth + 1)
    (tmPair(fst.term, snd.term, term.pScope.adv, bdy.term),
     fst.count + snd.count + bdy.count)
  of tApp:
    let fn = recur(term.fn, depth)
    let arg = recur(term.arg, depth)
    (tmApp(fn.term, arg.term), fn.count + arg.count)
  of tFst, tSnd, tAbsurd:
    let sub = recur(term.sub, depth)
    let rebuilt = case term.kind
      of tFst: tmFst(sub.term)
      of tSnd: tmSnd(sub.term)
      of tAbsurd: tmAbsurd(sub.term)
      else: term
    (rebuilt, sub.count)
  of tLet:
    let value = recur(term.letVal, depth)
    let ty = recur(term.letTy, depth)
    let bdy = recur(term.letScope.bdy, depth + 1)
    (tmLet(value.term, ty.term, term.letScope.adv, bdy.term),
     value.count + ty.count + bdy.count)
  of tMeta:
    var spine: seq[Term] = @[]
    var count = 0
    for arg in term.metaSpine:
      let next = recur(arg, depth)
      spine.add(next.term)
      count += next.count
    (tmMeta(term.metaId, spine), count)

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
    for b in h.holeCtx:
      if b.name == varName: varTy = b.ty
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
    for b in h.holeCtx: used.add(b.name)
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
      newLines.add("| " & newPats.join(" ") & " = ?")
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
        of dkMutual: decls[i].mutualLoc.line  # issue #42
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
          holesInRegion: int,
          editRanges: seq[tuple[startLine, startChar, endLine, endChar: int]]] =
  ## Replace the selected `_`/`?` hole and re-elaborate. Repeated named holes
  ## (`?n`) are replaced together, as they share one metavariable.
  let lines = src.splitLines()
  if line < 0 or line >= lines.len or col < 0 or col >= lines[line].len:
    return (false, "no hole at the requested position", 0, 0,
            0,0,0,0, "", 0, @[])
  var selected = ""
  let c = lines[line][col]
  if c == '_': selected = "_"
  elif c == '?':
    selected = "?"
    var j = col + 1
    while j < lines[line].len and lines[line][j] in {'0'..'9'}:
      selected.add(lines[line][j]); inc j
  else:
    return (false, "no hole at the requested position", 0, 0,
            0,0,0,0, "", 0, @[])

  # Find the exact token at every source occurrence. For a named hole, all
  # token occurrences are one metavariable and therefore must be filled as a
  # single editor action. Ignore comments to avoid rewriting explanatory text.
  var offsets: seq[int] = @[]
  var offset = 0
  var selectedOffset = col
  for li in 0 ..< line: selectedOffset += lines[li].len + 1
  proc startsDecl(ln: string): bool =
    let t = ln.strip()
    for kw in ["proc ", "def ", "data ", "postulate ", "elim ",
               "red ", "record ", "mutual ", "command ", "interface ",
               "import "]:
      if t.startsWith(kw): return true
    false
  var declStart = 0
  for li in countdown(line, 0):
    if startsDecl(lines[li]): declStart = li; break
  var declEnd = lines.len
  for li in line + 1 ..< lines.len:
    if startsDecl(lines[li]): declEnd = li; break
  for li, ln in lines:
    if li < declStart or li >= declEnd:
      offset += ln.len + (if li < lines.high: 1 else: 0)
      continue
    let commentAt = min((if ln.find("--") >= 0: ln.find("--") else: ln.len),
                        (if ln.find('#') >= 0: ln.find('#') else: ln.len))
    var i = 0
    while i < commentAt:
      if ln[i ..< min(ln.len, i + selected.len)] == selected and
         (selected == "_" or
          (i + selected.len == ln.len or ln[i + selected.len] notin {'0'..'9'})):
        if selected == "_" or (i + selected.len == ln.len or
           not (ln[i + selected.len].isAlphaNumeric or ln[i + selected.len] == '_')):
          offsets.add(offset + i)
      inc i
    offset += ln.len + (if li < lines.high: 1 else: 0)
  if selected == "_" or selected == "?": offsets = @[selectedOffset]
  if offsets.len == 0:
    return (false, "no hole at the requested position", 0, 0,
            0,0,0,0, "", 0, @[])

  var edited = src
  for o in countdown(offsets.high, 0):
    let at = offsets[o]
    edited = edited[0 ..< at] & term & edited[at + selected.len .. ^1]
  let newSrc = edited
  var editRanges: seq[tuple[startLine, startChar, endLine, endChar: int]] = @[]
  for at in offsets:
    let before = src[0 ..< at]
    let lineNo = before.count('\n')
    let lineStart = before.rfind('\n') + 1
    editRanges.add((lineNo, at - lineStart, lineNo, at - lineStart + selected.len))
  editRanges.sort(proc(x, y: tuple[startLine, startChar, endLine, endChar: int]): int =
    if x.startLine != y.startLine: cmp(y.startLine, x.startLine)
    else: cmp(y.startChar, x.startChar))

  # Holes introduced by the replacement term are counted per occurrence;
  # this preserves the refine/give distinction for shared holes.
  var termHoles = 0
  for ch in term:
    if ch == '?': inc termHoles
  try:
    let (_, ms, errLoc, errMsg) =
      if baseDir == "": elabCheckHoles(newSrc)
      else: elabCheckHolesDir(newSrc, baseDir)
    if errMsg != "":
      return (false, errMsg, errLoc.line - 1, errLoc.col - 1,
              0,0,0,0, "", 0, @[])
    let first = editRanges[^1]
    (true, "", 0, 0, first.startLine, first.startChar,
     first.endLine, first.endChar, newSrc, termHoles * offsets.len, editRanges)
  except ParseError as e:
    (false, "parse error: " & e.msg, e.loc.line - 1, e.loc.col - 1,
     0,0,0,0, "", 0, @[])

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

proc editJsonMany(uri: string,
    ranges: seq[tuple[startLine, startChar, endLine, endChar: int]],
    newText: string): JsonNode =
  var edits = newJArray()
  for r in ranges:
    edits.add(%*{
      "range": {"start": {"line": r.startLine, "character": r.startChar},
                "end": {"line": r.endLine, "character": r.endChar}},
      "newText": newText
    })
  %*{"changes": {uri: edits}}

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
      "edit": editJsonMany(uri, f.editRanges, term)
    })
    if f.holesInRegion == 0:
      actions.add(%*{
        "title": "give " & term,
        "kind": "refactor",
        "edit": editJsonMany(uri, f.editRanges, term)
      })
    # else: the term leaves holes behind — only refine is offered.
  else:
    # No explicit request: offer a case-split for every datatype-typed
    # variable in scope at the hole.
    try:
      let (_, ms, _, _) = elabCheckHoles(src)
      let hi = findHoleAt(ms, line, col)
      if hi >= 0:
        for b in ms.holes[hi].holeCtx:
          if typeHeadDataName(ms, b.ty) != "":
            let cs = caseSplitAt(src, line, col, b.name)
            if cs.ok:
              actions.add(%*{
                "title": "case-split " & b.name,
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

proc sourceOffset(src: string, line, col: int): int =
  ## Convert a 1-based source position to a byte offset.
  if line < 1 or col < 1: return -1
  var currentLine = 1
  while currentLine < line:
    let nl = src.find('\n', result)
    if nl < 0: return -1
    result = nl + 1
    inc currentLine
  result += col - 1
  if result > src.len: return -1

proc sourcePosition(src: string, offset: int): tuple[line, col: int] =
  ## Convert a byte offset to a 1-based source position.
  result = (1, 1)
  for i in 0 ..< min(offset, src.len):
    if src[i] == '\n':
      inc result.line
      result.col = 1
    else:
      inc result.col

proc freshShedName(base: string, used: var seq[string]): string =
  result = base
  var suffix = 1
  while result in used:
    result = base & "_" & $suffix
    inc suffix
  used.add(result)

proc refineShed*(nimFile, shedName, term: string,
                 requireComplete = false):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          status: string, yellowCount: int] =
  ## Issue #137: the server-owned refine round-trip for real `.nim` shed
  ## documents -- the #136 gap. The #58 `textDocument/codeAction` path
  ## elaborates document text as Eponym source, which a `.nim` file is
  ## not; here the client sends only (shedName, term) and the server does
  ## the whole loop: fill the hole in the macro-recorded generated source
  ## (`ShedInfo.genSrc`), refresh statuses, rewrite the sidecar, and
  ## return a Nim splice plus its replacement position (`nimLine`,
  ## `nimCol`: 1-based start of the original shed marker). Residual `_`
  ## holes become `shedHole(name)` markers in the splice and new sidecar
  ## entries, so recompiling the source preserves their goals.
  ##
  ## Sheds from other shedsBlock expansions in the same file are
  ## identified by sharing the block's `genSrc` string: their sources are
  ## updated to the filled source and their generated-source hole
  ## positions shifted, while sheds from other blocks are untouched.
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
  let spliceLine = sheds[si].nimLine
  let spliceCol = sheds[si].nimCol
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
  # A replacement can sit inside a larger application (for example a
  # natElim branch followed by its scrutinee). Parenthesize it in the
  # generated source so low-precedence forms such as `lam p. ...` do not
  # absorb the following application arguments. The client receives a Nim
  # splice, with residual holes converted to nested shed markers below.
  let wrappedTerm = "(" & term & ")"
  let f = fillHoleAt(oldSrc, holeLine1 - 1, holeCol1 - 1,
                     wrappedTerm, baseDir)
  if not f.ok:
    return (false, "refine rejected: " & f.why, "", 0, 0, "", 0)
  let newSrc = f.newSrc
  let fillOffset = sourceOffset(oldSrc, holeLine1, holeCol1)
  if fillOffset < 0:
    return (false, "recorded hole position is outside its generated source",
            "", 0, 0, "", 0)
  let regionStart = fillOffset + 1  # skip the grouping `(`

  # Re-elaborate to discover every residual hole created by this term.
  # Each one must become a named Nim shed in the splice, or the next
  # shedsBlock compilation would silently drop it from the sidecar.
  var checked: MetaStore
  try:
    let r = elabCheckHolesDir(newSrc, baseDir)
    if r.errMsg != "":
      return (false, "refine rejected: " & r.errMsg, "", 0, 0, "", 0)
    checked = r.ms
  except ParseError as e:
    return (false, "refine rejected: parse error: " & e.msg,
            "", 0, 0, "", 0)

  var residual: seq[tuple[offset, holeIdx: int, hole: HoleInfo]] = @[]
  let regionEnd = regionStart + term.len
  for hi, h in checked.holes:
    let absolute = sourceOffset(newSrc, h.holeLoc.line, h.holeLoc.col)
    if absolute >= regionStart and absolute < regionEnd:
      let relative = absolute - regionStart
      # Surface holes are `?`/`?N`; `_` is now a discard wildcard.
      if relative < term.len and term[relative] == '?':
        residual.add((relative, hi, h))
  residual.sort(proc(a, b: tuple[offset, holeIdx: int, hole: HoleInfo]): int =
    cmp(a.offset, b.offset))
  if requireComplete and residual.len > 0:
    return (false, "give rejected: candidate leaves " & $residual.len &
            " open hole(s)", "", 0, 0, "", 0)

  var usedNames: seq[string] = @[]
  for i, s in sheds:
    if i != si: usedNames.add(s.name)
  var residualNames: seq[string] = @[]
  for i in 0 ..< residual.len:
    let base = if i == 0: shedName else: shedName & "_" & $i
    residualNames.add(freshShedName(base, usedNames))

  var clientTerm = ""
  var termCursor = 0
  var markerOffsets: seq[int] = @[]
  for i, h in residual:
    clientTerm.add(term[termCursor ..< h.offset])
    markerOffsets.add(clientTerm.len)
    # Nim cannot parse prefix `![name]` in every expression position (for
    # example, after the dot in `lam f. lam g. ...`). Use a call-form
    # residual marker there; shedsBlock and the extension treat it as the
    # same named shed and turn it back into an Eponym hole.
    clientTerm.add("shedHole(" & residualNames[i] & ")")
    # Preserve the whole source token: `?` is anonymous and `?N` is a
    # numbered hole. Replacing only `?` would leave the number behind.
    termCursor = h.offset + 1 + h.hole.holeName.len
  if termCursor < term.len:
    clientTerm.add(term[termCursor .. ^1])

  # Update old shed locations by offsets, so same-line and multi-line
  # fills both move later holes correctly.
  for i in 0 ..< sheds.len:
    if sheds[i].genSrc != oldSrc or i == si: continue
    let oldOffset = sourceOffset(oldSrc, sheds[i].holeLine, sheds[i].holeCol)
    if oldOffset >= 0:
      let movedOffset = if oldOffset > fillOffset:
        oldOffset + wrappedTerm.len - 1
      else:
        oldOffset
      let pos = sourcePosition(newSrc, movedOffset)
      sheds[i].holeLine = pos.line
      sheds[i].holeCol = pos.col
    sheds[i].genSrc = newSrc

  # The original shed becomes one child per residual hole. A single child
  # keeps the original name, allowing the current panel to continue.
  if residual.len == 0:
    sheds[si].genSrc = newSrc
    sheds[si].holeIdx = -1
    sheds[si].status = ssWhite
  else:
    var children: seq[ShedInfo] = @[]
    for i, h in residual:
      let (goal, ctx, goalPi) = shedGoalAndCtx(checked, h.hole)
      let (termLine, termCol) = sourcePosition(clientTerm, markerOffsets[i])
      let nimLine = sheds[si].nimLine + termLine - 1
      let nimCol = if termLine == 1:
        sheds[si].nimCol + termCol - 1
      else:
        termCol
      children.add(ShedInfo(
        name: residualNames[i], draft: "", nimLine: nimLine, nimCol: nimCol,
        holeLine: h.hole.holeLoc.line, holeCol: h.hole.holeLoc.col,
        holeIdx: h.holeIdx, genSrc: newSrc, goal: goal, ctx: ctx,
        goalPi: goalPi, status: ssYellow))
    sheds.delete(si)
    for i, child in children:
      sheds.insert(child, si + i)

  refreshShedStatuses(sheds, newSrc, baseDir, onlyGenSrc = newSrc)
  writeShedSidecar(nimFile, sheds, errMsg0)  # keep the doc-level message
  var yellowCount = 0
  for s in sheds:
    if s.status == ssYellow: inc yellowCount
  let responseName = if residual.len == 0: shedName else: residualNames[0]
  var responseShed: ShedInfo
  var foundResponseShed = false
  for s in sheds:
    if s.name == responseName and s.genSrc == newSrc:
      responseShed = s
      foundResponseShed = true
      break
  if not foundResponseShed:
    return (false, "internal error: refinement result shed metadata missing",
            "", 0, 0, "", 0)
  (true, "", clientTerm, spliceLine, spliceCol,
   shedStatusToStr(responseShed.status), yellowCount)

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
  for b in h.holeCtx:
    if b.name == variable: varTy = b.ty
  if varTy.isNil:
    return (false, "'" & variable & "' is not in scope at the hole",
            "", 0, 0, @[])
  # Resolve the datatype head and recover its parameter and index
  # applications. The eliminator motive quantifies over every index, then
  # over a value at those generalized indices.
  let ty = zonk(ms, varTy)
  let spine = applicationSpine(ty)
  if spine.head == nil or spine.head.kind != tR:
    return (false, "'" & variable &
            "' does not have a datatype type", "", 0, 0, @[])
  let dataRef = spine.head.refId
  if dataRef notin ms.ctorTable.dataNames:
    return (false, "'" & variable & "' does not have a datatype type",
            "", 0, 0, @[])
  let dataName = ms.ctorTable.dataNames[dataRef]
  let paramCount = ms.ctorTable.dataParamCounts.getOrDefault(dataRef, 0)
  let indexCount = ms.ctorTable.dataIndexCounts.getOrDefault(dataRef, 0)
  if spine.args.len != paramCount + indexCount:
    return (false, "cannot recover the parameter and index application for " &
            "datatype '" & dataName & "'", "", 0, 0, @[])
  let rawIndexDomains = ms.ctorTable.dataIndexDomains.getOrDefault(dataRef)
  if rawIndexDomains.len != indexCount:
    return (false, "cannot recover the index telescope for datatype '" &
            dataName & "'", "", 0, 0, @[])
  var paramEp: seq[string] = @[]
  var paramNim: seq[string] = @[]
  var holeCtx: Ctx = @[]
  for b in h.holeCtx:
    holeCtx.add(CtxEntry(name: b.name, ty: b.ty, qty: b.qty))
  var paramTerms: seq[Term] = @[]
  for i in 0 ..< paramCount:
    let normalized = zonk(ms, spine.args[i])
    paramTerms.add(normalized)
    paramEp.add(prettyTerm(normalized, holeCtx, ms.refNames,
                           ms.recordFields))
    var argNim = ""
    if not nimTypeExpr(normalized, h.holeCtx, ms, argNim):
      return (false, "cannot render a parameter of datatype '" & dataName &
              "' in Nim shed syntax", "", 0, 0, @[])
    paramNim.add(argNim)
  var usedIndexNames: seq[string] = @[]
  for b in h.holeCtx: usedIndexNames.add(b.name)
  usedIndexNames.add("u")
  var indexNames: seq[string] = @[]
  var indexDomains: seq[Term] = @[]
  var indexDomainEp: seq[string] = @[]
  var indexDomainNim: seq[string] = @[]
  var indexEp: seq[string] = @[]
  var indexNim: seq[string] = @[]
  var indexCtx: seq[HoleContextBinder] = @[]
  for j in 0 ..< indexCount:
    let iname = freshen("i" & $j, usedIndexNames)
    usedIndexNames.add(iname)
    indexNames.add(iname)
    var domain = rawIndexDomains[j]
    # The stored family telescope is scoped over earlier indices and
    # parameters. Substitute parameters from innermost to outermost.
    for p in countdown(paramTerms.high, 0):
      var actualParam = paramTerms[p]
      for _ in 0 ..< j: actualParam = weaken(actualParam)
      domain = subst(domain, j, actualParam)
    domain = zonk(ms, domain)
    indexDomains.add(domain)
    var domainCtx = indexCtx
    domainCtx.add(h.holeCtx)
    var domainCoreCtx: Ctx = @[]
    for b in domainCtx:
      domainCoreCtx.add(CtxEntry(name: b.name, ty: b.ty, qty: b.qty))
    indexDomainEp.add(prettyTerm(domain, domainCoreCtx, ms.refNames,
                                 ms.recordFields))
    var domainNim = ""
    if not nimTypeExpr(domain, domainCtx, ms, domainNim):
      return (false, "cannot render an index type of datatype '" & dataName &
              "' in Nim shed syntax", "", 0, 0, @[])
    indexDomainNim.add(domainNim)
    let actual = zonk(ms, spine.args[paramCount + j])
    var actualNim = ""
    if not nimTypeExpr(actual, h.holeCtx, ms, actualNim):
      return (false, "cannot render an index of datatype '" & dataName &
              "' in Nim shed syntax", "", 0, 0, @[])
    indexNim.add(actualNim)
    indexEp.add(prettyTerm(actual, holeCtx, ms.refNames, ms.recordFields))
    indexCtx.insert(HoleContextBinder(name: iname, ty: domain, qty: qOmega), 0)
  var familyEp = dataName
  var familyEpArgs = paramEp
  familyEpArgs.add(indexNames)
  if familyEpArgs.len > 0: familyEp &= " " & familyEpArgs.join(" ")
  var familyNim = dataName
  var familyNimArgs = paramNim
  familyNimArgs.add(indexNames)
  if familyNimArgs.len > 0:
    familyNim &= "[" & familyNimArgs.join(", ") & "]"
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
  # Build the terms. The Eponym term (for validation) uses `?` holes;
  # the nim term uses `![sub]` shed nodes so recompile discovers them.
  let goalStr = sheds0[si].goal
  if goalStr == "":
    return (false, "shed '" & shedName & "': no goal recorded",
            "", 0, 0, @[])
  # Abstract exact occurrences of the actual indices in the target. Process
  # larger index expressions first so an index such as `suc n` is abstracted
  # as a unit before a separate index `n` is considered. Eponym validates the
  # completed motive against the original goal before returning the splice.
  var generalizedGoal = zonk(ms, h.holeGoal)
  let motiveBinders = indexCount + 1 # all indices, then the value binder
  for _ in 0 ..< motiveBinders: generalizedGoal = weaken(generalizedGoal)
  var indexPatterns: seq[tuple[term: Term, index: int]] = @[]
  for j in 0 ..< indexCount:
    var pattern = zonk(ms, spine.args[paramCount + j])
    for _ in 0 ..< motiveBinders: pattern = weaken(pattern)
    indexPatterns.add((pattern, j))
  indexPatterns.sort(proc(a, b: tuple[term: Term, index: int]): int =
    cmp(termSize(b.term), termSize(a.term)))
  for (pattern, index) in indexPatterns:
    let replaced = replaceOccurrences(generalizedGoal, pattern,
                                      indexCount - index)
    generalizedGoal = replaced.term
  var goalTextCtx: Ctx = @[]
  var goalNimCtx: seq[HoleContextBinder] = @[]
  goalTextCtx.add(CtxEntry(name: "u", ty: nil, qty: qOmega))
  goalNimCtx.add(HoleContextBinder(name: "u", ty: nil, qty: qOmega))
  for j in countdown(indexCount - 1, 0):
    goalTextCtx.add(CtxEntry(name: indexNames[j], ty: indexDomains[j],
                             qty: qOmega))
    goalNimCtx.add(HoleContextBinder(name: indexNames[j],
      ty: indexDomains[j], qty: qOmega))
  goalTextCtx.add(holeCtx)
  goalNimCtx.add(h.holeCtx)
  let motiveGoalEp = if indexCount == 0: goalStr else:
    prettyTerm(generalizedGoal, goalTextCtx, ms.refNames, ms.recordFields)
  var motiveGoalNim = goalStr
  if indexCount > 0 and
      not nimTypeExpr(generalizedGoal, goalNimCtx, ms, motiveGoalNim):
    return (false, "cannot render the generalized target of datatype '" &
            dataName & "' in Nim shed syntax", "", 0, 0, @[])
  var motiveEp = "(lam (u : " & familyEp & "). " & motiveGoalEp & ")"
  var motiveNim = "lam(u, " & familyNim & ", " & motiveGoalNim & ")"
  for j in countdown(indexCount - 1, 0):
    motiveEp = "(lam (" & indexNames[j] & " : " & indexDomainEp[j] &
               "). " & motiveEp & ")"
    motiveNim = "lam(" & indexNames[j] & ", " & indexDomainNim[j] &
                ", " & motiveNim & ")"
  var epArgs: seq[string] = paramEp
  epArgs.add(motiveEp)
  var nimArgs: seq[string] = @[motiveNim]
  for ss in subSheds:
    epArgs.add("?")
    nimArgs.add("![" & ss & "]")
  epArgs.add(indexEp)
  nimArgs.add(indexNim)
  epArgs.add(variable)
  nimArgs.add(variable)
  let epTerm = elimName & " " & epArgs.join(" ")
  let nimHead = if paramNim.len > 0:
      elimName & "[" & paramNim.join(", ") & "]"
    else:
      elimName
  let nimTerm = nimHead & "(" & nimArgs.join(", ") & ")"
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
    let requireComplete = "requireComplete" in msg["params"] and
      msg["params"]["requireComplete"].getBool()
    let r = refineShed(uriToPath(uri), shedName, term, requireComplete)
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
