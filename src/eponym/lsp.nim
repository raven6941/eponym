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
import shed_state
import shed_state_dag
import sha256

const MaxShedHistoryTransitions = 64
const MaxShedActionStateVersions = 128
const MaxShedStateNodes = 4096

type
  ShedActionKind* = enum
    sakRefine, sakGive, sakCaseSplit

  ShedHistoryMove* = enum
    shmNone, shmCommit, shmUndo, shmRedo

  ShedGoalSnapshot* = object
    shedName*: string
    goal*: string
    context*: seq[string]
    status*: string

  ShedActionTransition* = object
    ## A validated, editor-independent edit together with the source snapshots
    ## that let clients safely project, undo, and replay it.
    id*: int
    kind*: ShedActionKind
    shedName*: string
    term*: string
    variable*: string
    requireComplete*: bool
    beforeDocument*: string
    afterDocument*: string
    beforeGenSrc*: string
    afterGenSrc*: string
    beforeGoal*: string
    beforeContext*: seq[string]
    spliceTerm*: string
    nimLine*: int
    nimCol*: int
    status*: string
    yellowCount*: int
    subSheds*: seq[string]
    afterGoals*: seq[ShedGoalSnapshot]

  ShedActionHistory* = object
    uri*: string
    transitions*: seq[ShedActionTransition]
    cursor*: int
    pendingMove*: ShedHistoryMove
    pendingId*: int

  ShedActionStateVersion* = object
    version*: int
    uri*: string
    shedName*: string
    documentRevision*: int
    generatedSource*: string
    goal*: string
    context*: seq[string]
    actions*: JsonNode

  LspServer* = object
    documents*: Table[string, string]  # uri -> text
    shedHistories*: seq[ShedActionHistory]
    nextShedTransitionId*: int
    documentRevisions*: seq[tuple[uri: string, revision: int]]
    shedActionStateVersions*: seq[ShedActionStateVersion]
    nextShedActionStateVersion*: int
    stateNodeCache*: NodeCache

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
    if spine.head == nil: return false
    if spine.head.kind != tR or spine.head.refId notin ms.refNames:
      var headText = ""
      if not nimTypeExpr(zonk(ms, spine.head), ctx, ms, headText): return false
      rendered = headText & "(" & argTexts.join(", ") & ")"
      return true
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
  of tPi, tLam:
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
    let constructor = if term.kind == tPi: "Pi" else: "lam"
    rendered = constructor & "(" & binderName & ", " & dom & ", " & body & ")"
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

proc replaceOccurrenceAt(term, pattern: Term, replacement, wanted: int,
                         seen: var int, depth = 0):
    tuple[term: Term, found: bool] =
  ## Replace one preorder occurrence while preserving binder depth. This is
  ## used by equality rewrite so repeated endpoints are individually
  ## selectable rather than all silently rewritten together.
  if term == nil: return (nil, false)
  var shiftedPattern = pattern
  for _ in 0 ..< depth: shiftedPattern = weaken(shiftedPattern)
  if sameTerm(term, shiftedPattern):
    if seen == wanted: return (vv(replacement + depth), true)
    inc seen
    return (term, false)
  template recur(child: Term, childDepth: int): untyped =
    replaceOccurrenceAt(child, pattern, replacement, wanted, seen, childDepth)
  case term.kind
  of tR, tV, tC, tInt, tNatLit, tNatSing, tType: (term, false)
  of tPrim:
    let ty = recur(term.primTy, depth)
    (tmPrim(term.primOp, ty.term), ty.found)
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
    (rebuilt, dom.found or bdy.found)
  of tPair:
    let fst = recur(term.pFst, depth)
    let snd = recur(term.pSnd, depth)
    let bdy = recur(term.pScope.bdy, depth + 1)
    (tmPair(fst.term, snd.term, term.pScope.adv, bdy.term),
     fst.found or snd.found or bdy.found)
  of tApp:
    let fn = recur(term.fn, depth)
    let arg = recur(term.arg, depth)
    (tmApp(fn.term, arg.term), fn.found or arg.found)
  of tFst, tSnd, tAbsurd:
    let sub = recur(term.sub, depth)
    let rebuilt = case term.kind
      of tFst: tmFst(sub.term)
      of tSnd: tmSnd(sub.term)
      of tAbsurd: tmAbsurd(sub.term)
      else: term
    (rebuilt, sub.found)
  of tLet:
    let value = recur(term.letVal, depth)
    let ty = recur(term.letTy, depth)
    let bdy = recur(term.letScope.bdy, depth + 1)
    (tmLet(value.term, ty.term, term.letScope.adv, bdy.term),
     value.found or ty.found or bdy.found)
  of tMeta:
    var spine: seq[Term] = @[]
    var found = false
    for arg in term.metaSpine:
      let next = recur(arg, depth)
      spine.add(next.term)
      found = found or next.found
    (tmMeta(term.metaId, spine), found)

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
      "def(" & procDef.name & ", " & $desugarTy(procDef) & "):"]
    for c in ctors:
      var pat = c.name
      if c.tele.len > 0:
        var args: seq[string] = @[]
        for b in c.tele:
          let fresh = freshen(b.name, used)
          used.add(fresh)
          args.add(fresh)
        pat = c.name & "(" & args.join(", ") & ")"
      var newPats: seq[string] = @[pat]
      for i in 1 ..< explicitNames.len: newPats.add(explicitNames[i])
      newLines.add("  clause([" & newPats.join(", ") & "], _)")
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

proc sourceOffset(src: string, line, col: int): int

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

  # Holes introduced by the replacement term, counted from the
  # re-elaborated store inside the inserted regions. Text counting
  # cannot work here: `_` is a hole in term position but a discard in
  # binder/pattern position, so only real holes count. The caller uses
  # this for the give/refine distinction (zero vs nonzero), which is
  # preserved for shared holes: one shared hole still counts.
  try:
    let (_, ms, errLoc, errMsg) =
      if baseDir == "": elabCheckHoles(newSrc)
      else: elabCheckHolesDir(newSrc, baseDir)
    if errMsg != "":
      return (false, errMsg, errLoc.line - 1, errLoc.col - 1,
              0,0,0,0, "", 0, @[])
    var termHoles = 0
    var delta = 0
    for at in offsets:
      let newStart = at + delta
      delta += term.len - selected.len
      for h in ms.holes:
        let absolute = sourceOffset(newSrc, h.holeLoc.line, h.holeLoc.col)
        if absolute >= newStart and absolute < newStart + term.len:
          inc termHoles
    let first = editRanges[^1]
    (true, "", 0, 0, first.startLine, first.startChar,
     first.endLine, first.endChar, newSrc, termHoles, editRanges)
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

proc cloneShedInfos(input: seq[ShedInfo]): seq[ShedInfo] =
  result = newSeq[ShedInfo](input.len)
  for i, item in input:
    result[i] = item
    result[i].ctx = newSeq[string](item.ctx.len)
    for j, value in item.ctx: result[i].ctx[j] = value
    result[i].goalPi = newSeq[string](item.goalPi.len)
    for j, value in item.goalPi: result[i].goalPi[j] = value

proc refineShedPlan*(nimFile, shedName, term: string,
                     inputSheds: seq[ShedInfo], inputErrMsg: string,
                     updatedSheds: var seq[ShedInfo],
                     requireComplete = false):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          status: string, yellowCount: int] =
  ## Compute a checked refine result without reading or writing the
  ## document or sidecar. The caller owns persistence/adoption. This pure
  ## planning boundary is used by the state-DAG experiment (#450).
  ##
  ## Sheds from other shedsBlock expansions in the same file are
  ## identified by sharing the block's `genSrc` string: their sources are
  ## updated to the filled source and their generated-source hole
  ## positions shifted, while sheds from other blocks are untouched.
  var sheds = cloneShedInfos(inputSheds)
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
  # generated source so low-precedence forms such as `lam(p: P) => ...` do not
  # absorb the following application arguments. The client receives a Nim
  # splice, with residual holes converted to nested shed markers below.
  let rejectionLabel = if requireComplete: "give rejected" else: "refine rejected"
  let wrappedTerm = "(" & term & ")"
  let f = fillHoleAt(oldSrc, holeLine1 - 1, holeCol1 - 1,
                     wrappedTerm, baseDir)
  if not f.ok:
    return (false, rejectionLabel & ": " & f.why, "", 0, 0, "", 0)
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
      return (false, rejectionLabel & ": " & r.errMsg, "", 0, 0, "", 0)
    checked = r.ms
  except ParseError as e:
    return (false, rejectionLabel & ": parse error: " & e.msg,
            "", 0, 0, "", 0)

  var residual: seq[tuple[offset, holeIdx: int, hole: HoleInfo]] = @[]
  let regionEnd = regionStart + term.len
  for hi, h in checked.holes:
    let absolute = sourceOffset(newSrc, h.holeLoc.line, h.holeLoc.col)
    if absolute >= regionStart and absolute < regionEnd:
      let relative = absolute - regionStart
      # Surface holes are `_` (anonymous) and `?N` (named). A `_`
      # in binder/pattern position is a discard and never appears in
      # checked.holes, so it is already excluded by this loop.
      if relative < term.len and (term[relative] == '?' or term[relative] == '_'):
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
    # example, after the arrow in `lam(f: F) => lam(g: G) => ...`). Use a
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
    # Do not persist: this result is still hypothetical until the client
    # chooses a source projection to adopt.
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
  updatedSheds = sheds
  (true, "", clientTerm, spliceLine, spliceCol,
   shedStatusToStr(responseShed.status), yellowCount)

proc refineShed*(nimFile, shedName, term: string,
                 requireComplete = false):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          status: string, yellowCount: int] =
  ## Legacy disk-backed adapter. The state-addressed protocol calls
  ## refineShedPlan directly and leaves source/sidecar adoption to VS Code.
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)",
            "", 0, 0, "", 0)
  let (sheds, errMsg) = readShedSidecarEx(sc)
  var updated: seq[ShedInfo] = @[]
  result = refineShedPlan(nimFile, shedName, term, sheds, errMsg,
                          updated, requireComplete)
  if result.ok:
    writeShedSidecar(nimFile, updated, errMsg)

proc introShedPlan*(nimFile, shedName: string, count: int,
                    inputSheds: seq[ShedInfo], inputErrMsg: string,
                    updatedSheds: var seq[ShedInfo]):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          status: string, yellowCount: int] =
  ## Goal-directed Intro for a real `.nim` shed. The selected Pi binders
  ## are read from the checked hole goal, rendered as typed lambda binders,
  ## then passed through refineShed's normal checker and source round-trip.
  ## Clients request the semantic operation and never synthesize lambda text.
  if count < 1:
    return (false, "Intro needs a positive binder count", "", 0, 0, "", 0)
  let sheds = inputSheds
  var si = -1
  for i, shed in sheds:
    if shed.name == shedName:
      si = i
      break
  if si < 0:
    return (false, "unknown shed '" & shedName & "'", "", 0, 0, "", 0)
  if sheds[si].genSrc == "":
    return (false, "shed '" & shedName &
            "': no generated source recorded (sidecar predates #137; " &
            "recompile)", "", 0, 0, "", 0)
  if sheds[si].status != ssYellow:
    return (false, "shed '" & shedName & "' is not open (status " &
            shedStatusToStr(sheds[si].status) & ")", "", 0, 0, "", 0)

  var ms: MetaStore
  var holeIdx = -1
  try:
    let checked = elabCheckHolesDir(sheds[si].genSrc, parentDir(nimFile))
    ms = checked.ms
    for i, h in ms.holes:
      if h.holeLoc.line != sheds[si].holeLine: continue
      if sheds[si].holeCol <= 0 or h.holeLoc.col == sheds[si].holeCol:
        holeIdx = i
        break
  except ParseError as e:
    return (false, "recorded source no longer parses: " & e.msg,
            "", 0, 0, "", 0)
  if holeIdx < 0:
    return (false, "shed '" & shedName &
            "': hole no longer open in the recorded source (sidecar stale? recompile)",
            "", 0, 0, "", 0)

  let state = semanticShedState(ms, ms.holes[holeIdx])
  if count > state.goalPi.len:
    return (false, "Intro requested " & $count & " binder(s), but the goal " &
            "has only " & $state.goalPi.len & " leading function binder(s)",
            "", 0, 0, "", 0)

  var ctx = semanticContext(state)
  var usedNames = state.context.mapIt(it.name)
  var checkedTerm = ""
  var clientPrefixes: seq[string] = @[]
  var checkedPrefixLen = 0
  for i in 0 ..< count:
    let binder = state.goalPi[i]
    let baseName = if binder.name.len > 0 and binder.name != "_":
                     binder.name
                   else: "intro"
    let name = freshShedName(baseName, usedNames)
    let domain = prettyTerm(binder.domain, ctx, ms.refNames, ms.recordFields)
    var quantity = ""
    if binder.qty == q0 or binder.erased: quantity = "0 "
    elif binder.qty == q1: quantity = "1 "
    if binder.implicit:
      let prefix = "lam({" & name & ": " & domain & "}) => "
      checkedTerm.add(prefix)
      checkedPrefixLen += prefix.len
      clientPrefixes.add("lam({" & name & ": " & domain & "}) => ")
    else:
      let prefix = "lam(" & quantity & name & ": " & domain & ") => "
      checkedTerm.add(prefix)
      checkedPrefixLen += prefix.len
      let clientName = if quantity == "1 ": name & " {.linear.}"
                       elif quantity == "0 ": name & " {.erased.}"
                       else: name
      clientPrefixes.add("lam(" & clientName & ": " & domain & ") => ")
    ctx = @[CtxEntry(name: name, ty: binder.domain, qty: toQty(binder.qty))] & ctx
  checkedTerm.add("_")
  var plannedSheds: seq[ShedInfo] = @[]
  result = refineShedPlan(nimFile, shedName, checkedTerm, sheds,
                          inputErrMsg, plannedSheds)
  if result.ok:
    updatedSheds = plannedSheds
    let residualBody = result.term[checkedPrefixLen .. ^1]
    result.term = clientPrefixes.join("") & residualBody

proc introShed*(nimFile, shedName: string, count = 1):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          status: string, yellowCount: int] =
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)", "", 0, 0, "", 0)
  let (sheds, errMsg) = readShedSidecarEx(sc)
  var updated: seq[ShedInfo] = @[]
  result = introShedPlan(nimFile, shedName, count, sheds, errMsg, updated)
  if result.ok: writeShedSidecar(nimFile, updated, errMsg)

proc refineConstructorsShedPlan*(nimFile, shedName: string, selected: string,
                             inputSheds: seq[ShedInfo], inputErrMsg: string,
                             updatedSheds: var seq[ShedInfo]):
    tuple[ok: bool, why: string, constructors: seq[string], term: string,
          nimLine, nimCol: int, status: string, yellowCount: int] =
  ## Goal-directed constructor refinement (#426). Candidate feasibility is
  ## decided by the normal elaborator: each constructor is applied to typed
  ## holes for its complete Pi telescope and checked against the selected
  ## shed goal. The probe never writes the sidecar. Selecting a candidate
  ## delegates to refineShed so generated field goals become real sheds.
  let sheds = inputSheds
  var si = -1
  for i, shed in sheds:
    if shed.name == shedName: si = i; break
  if si < 0:
    return (false, "unknown shed '" & shedName & "'", @[], "", 0, 0, "", 0)
  if sheds[si].genSrc == "":
    return (false, "shed '" & shedName & "': no generated source recorded; recompile",
            @[], "", 0, 0, "", 0)
  if sheds[si].status != ssYellow:
    return (false, "shed '" & shedName & "' is not open (status " &
            shedStatusToStr(sheds[si].status) & ")", @[], "", 0, 0, "", 0)

  let oldSrc = sheds[si].genSrc
  let baseDir = parentDir(nimFile)
  var ms: MetaStore
  var target: HoleInfo
  var found = false
  try:
    let checked = elabCheckHolesDir(oldSrc, baseDir)
    ms = checked.ms
    for h in ms.holes:
      if h.holeLoc.line == sheds[si].holeLine and
         (sheds[si].holeCol <= 0 or h.holeLoc.col == sheds[si].holeCol):
        target = h
        found = true
        break
  except ParseError as e:
    return (false, "recorded source no longer parses: " & e.msg,
            @[], "", 0, 0, "", 0)
  if not found:
    return (false, "shed hole is no longer open (sidecar stale? recompile)",
            @[], "", 0, 0, "", 0)

  let spine = applicationSpine(zonk(ms, target.holeGoal))
  if spine.head == nil or spine.head.kind != tR or
     spine.head.refId notin ms.ctorTable.dataCtors:
    return (false, "goal is not headed by a registered datatype",
            @[], "", 0, 0, "", 0)
  let family = spine.head.refId

  var candidates: seq[string] = @[]
  var selectedTerm = ""
  for cid in ms.ctorTable.dataCtors[family]:
    if cid notin ms.ctorTable.ctorTypes: continue
    var arity = 0
    var ty = zonk(ms, ms.ctorTable.ctorTypes[cid])
    while ty != nil and ty.kind == tPi:
      inc arity
      ty = zonk(ms, ty.scope.bdy)
    let name = ms.ctorTable.ctorNames[cid]
    let candidate = name & repeat(" _", arity)
    let p = sourceOffset(oldSrc, sheds[si].holeLine, sheds[si].holeCol)
    if p < 0: continue
    let (line, col) = sourcePosition(oldSrc, p)
    let probe = fillHoleAt(oldSrc, line - 1, col - 1,
                           "(" & candidate & ")", baseDir)
    if probe.ok:
      candidates.add(name)
      if name == selected: selectedTerm = candidate
  if selected.len == 0:
    if candidates.len == 0:
      return (true, "no constructor is currently known to fit this goal",
              @[], "", 0, 0, "", 0)
    return (true, "", candidates, "", 0, 0, "", 0)
  if selected notin candidates:
    return (false, "constructor '" & selected &
            "' is not feasible for this goal; available: " & candidates.join(", "),
            candidates, "", 0, 0, "", 0)
  var plannedSheds: seq[ShedInfo] = @[]
  let refined = refineShedPlan(nimFile, shedName, selectedTerm, sheds,
                               inputErrMsg, plannedSheds)
  if not refined.ok:
    return (false, refined.why, candidates, "", 0, 0, "", 0)
  updatedSheds = plannedSheds
  (true, "", candidates, refined.term, refined.nimLine, refined.nimCol,
   refined.status, refined.yellowCount)

proc refineConstructorsShed*(nimFile, shedName: string, selected = ""):
    tuple[ok: bool, why: string, constructors: seq[string], term: string,
          nimLine, nimCol: int, status: string, yellowCount: int] =
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)", @[], "", 0, 0, "", 0)
  let (sheds, errMsg) = readShedSidecarEx(sc)
  var updated: seq[ShedInfo] = @[]
  result = refineConstructorsShedPlan(nimFile, shedName, selected, sheds, errMsg, updated)
  if result.ok and selected.len > 0:
    writeShedSidecar(nimFile, updated, errMsg)

proc refineFromContextShedPlan*(nimFile, shedName: string, selected: string,
                            inputSheds: seq[ShedInfo], inputErrMsg: string,
                            updatedSheds: var seq[ShedInfo]):
    tuple[ok: bool, why: string, candidates: seq[string], term: string,
          nimLine, nimCol: int, status: string, yellowCount: int] =
  ## Goal-directed Apply (#427). Each local hypothesis is tried as a head,
  ## with one typed hole per Pi binder. Normal elaboration determines which
  ## holes can be solved from the expected goal and validates the residual
  ## dependent argument goals. Candidate enumeration is read-only; applying
  ## one uses refineShed's checked round-trip.
  let sheds = inputSheds
  var si = -1
  for i, shed in sheds:
    if shed.name == shedName: si = i; break
  if si < 0:
    return (false, "unknown shed '" & shedName & "'", @[], "", 0, 0, "", 0)
  if sheds[si].genSrc == "":
    return (false, "shed '" & shedName & "': no generated source recorded; recompile",
            @[], "", 0, 0, "", 0)
  if sheds[si].status != ssYellow:
    return (false, "shed '" & shedName & "' is not open (status " &
            shedStatusToStr(sheds[si].status) & ")", @[], "", 0, 0, "", 0)

  let oldSrc = sheds[si].genSrc
  let baseDir = parentDir(nimFile)
  var ms: MetaStore
  var target: HoleInfo
  var found = false
  try:
    let checked = elabCheckHolesDir(oldSrc, baseDir)
    ms = checked.ms
    for h in ms.holes:
      if h.holeLoc.line == sheds[si].holeLine and
         (sheds[si].holeCol <= 0 or h.holeLoc.col == sheds[si].holeCol):
        target = h
        found = true
        break
  except ParseError as e:
    return (false, "recorded source no longer parses: " & e.msg,
            @[], "", 0, 0, "", 0)
  if not found:
    return (false, "shed hole is no longer open (sidecar stale? recompile)",
            @[], "", 0, 0, "", 0)

  let p = sourceOffset(oldSrc, sheds[si].holeLine, sheds[si].holeCol)
  if p < 0:
    return (false, "shed hole position is outside its generated source",
            @[], "", 0, 0, "", 0)
  let (line, col) = sourcePosition(oldSrc, p)
  var candidates: seq[string] = @[]
  var selectedTerm = ""
  var context: Ctx = @[]
  for b in target.holeCtx:
    context.add(CtxEntry(name: b.name, ty: b.ty, qty: b.qty))
  for b in target.holeCtx:
    if b.name.len == 0 or b.name == "_": continue
    var arity = 0
    var ty = zonk(ms, b.ty)
    while ty != nil and ty.kind == tPi:
      inc arity
      ty = zonk(ms, ty.scope.bdy)
    let candidate = b.name & repeat(" _", arity)
    let probe = fillHoleAt(oldSrc, line - 1, col - 1,
                           "(" & candidate & ")", baseDir)
    if probe.ok:
      # Expected-type unification can solve some argument holes. Reify those
      # solutions in the picker term (e.g. `f _` becomes `f a` when the goal
      # forces the dependent argument to the in-scope value `a`).
      var rendered = candidate
      try:
        let checked = elabCheckHolesDir(probe.newSrc, baseDir)
        if checked.errMsg == "":
          var placeholderPositions: seq[int] = @[]
          for i, ch in candidate:
            if ch == '?' or ch == '_': placeholderPositions.add(i)
          var replacements = initTable[int, string]()
          let candidateStart = p + 1 # skip the probe's opening parenthesis
          for h in checked.ms.holes:
            let holeOffset = sourceOffset(probe.newSrc,
              h.holeLoc.line, h.holeLoc.col)
            let relative = holeOffset - candidateStart
            if relative notin placeholderPositions: continue
            let solved = zonk(checked.ms, h.holeTerm)
            if solved.kind != tMeta:
              replacements[relative] = prettyTerm(solved, context,
                checked.ms.refNames, checked.ms.recordFields)
          for pos in countdown(candidate.high, 0):
            if pos in replacements:
              let value = replacements[pos]
              rendered = rendered[0 ..< pos] & value & rendered[pos + 1 .. ^1]
      except ParseError:
        discard
      candidates.add(rendered)
      if rendered == selected: selectedTerm = rendered

  if selected.len == 0:
    if candidates.len == 0:
      return (true, "no local hypothesis is currently known to fit this goal",
              @[], "", 0, 0, "", 0)
    return (true, "", candidates, "", 0, 0, "", 0)
  if selected notin candidates:
    return (false, "candidate '" & selected &
            "' is not feasible for this goal; available: " & candidates.join(", "),
            candidates, "", 0, 0, "", 0)
  var plannedSheds: seq[ShedInfo] = @[]
  let refined = refineShedPlan(nimFile, shedName, selectedTerm, sheds,
                               inputErrMsg, plannedSheds)
  if not refined.ok:
    return (false, refined.why, candidates, "", 0, 0, "", 0)
  updatedSheds = plannedSheds
  (true, "", candidates, refined.term, refined.nimLine, refined.nimCol,
   refined.status, refined.yellowCount)

proc refineFromContextShed*(nimFile, shedName: string, selected = ""):
    tuple[ok: bool, why: string, candidates: seq[string], term: string,
          nimLine, nimCol: int, status: string, yellowCount: int] =
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)", @[], "", 0, 0, "", 0)
  let (sheds, errMsg) = readShedSidecarEx(sc)
  var updated: seq[ShedInfo] = @[]
  result = refineFromContextShedPlan(nimFile, shedName, selected, sheds, errMsg, updated)
  if result.ok and selected.len > 0:
    writeShedSidecar(nimFile, updated, errMsg)

proc refineEqualityShedPlan*(nimFile, shedName: string, selected: string,
                         inputSheds: seq[ShedInfo], inputErrMsg: string,
                         updatedSheds: var seq[ShedInfo]):
    tuple[ok: bool, why: string, candidates: seq[string], term: string,
          nimLine, nimCol: int, status: string, yellowCount: int] =
  ## Equality rewrite (#428). Offer each orientation of an in-scope Eq proof
  ## whose endpoint occurs structurally in the target. Build transport with
  ## Eq's generated eliminator, leave the rewritten target as a checked hole,
  ## and let refineShed create its durable child shed after selection.
  let sheds = inputSheds
  var si = -1
  for i, shed in sheds:
    if shed.name == shedName: si = i; break
  if si < 0:
    return (false, "unknown shed '" & shedName & "'", @[], "", 0, 0, "", 0)
  if sheds[si].genSrc == "":
    return (false, "shed '" & shedName & "': no generated source recorded; recompile",
            @[], "", 0, 0, "", 0)
  if sheds[si].status != ssYellow:
    return (false, "shed '" & shedName & "' is not open (status " &
            shedStatusToStr(sheds[si].status) & ")", @[], "", 0, 0, "", 0)

  let oldSrc = sheds[si].genSrc
  let baseDir = parentDir(nimFile)
  var ms: MetaStore
  var target: HoleInfo
  var found = false
  try:
    let checked = elabCheckHolesDir(oldSrc, baseDir)
    ms = checked.ms
    for h in ms.holes:
      if h.holeLoc.line == sheds[si].holeLine and
         (sheds[si].holeCol <= 0 or h.holeLoc.col == sheds[si].holeCol):
        target = h
        found = true
        break
  except ParseError as e:
    return (false, "recorded source no longer parses: " & e.msg,
            @[], "", 0, 0, "", 0)
  if not found:
    return (false, "shed hole is no longer open (sidecar stale? recompile)",
            @[], "", 0, 0, "", 0)

  let p = sourceOffset(oldSrc, sheds[si].holeLine, sheds[si].holeCol)
  if p < 0:
    return (false, "shed hole position is outside its generated source",
            @[], "", 0, 0, "", 0)
  let (line, col) = sourcePosition(oldSrc, p)
  let goal = zonk(ms, target.holeGoal)
  var ctx: Ctx = @[]
  for b in target.holeCtx:
    ctx.add(CtxEntry(name: b.name, ty: zonk(ms, b.ty), qty: b.qty))
  var candidates: seq[string] = @[]
  var selectedTerm = ""
  var selectedClientTerm = ""

  for b in target.holeCtx:
    let eqTy = zonk(ms, b.ty)
    let eqSpine = applicationSpine(eqTy)
    if eqSpine.head == nil or eqSpine.head.kind != tR or
       ms.refNames.getOrDefault(eqSpine.head.refId, "") != "Eq" or
       eqSpine.args.len != 3:
      continue
    let aTy = zonk(ms, eqSpine.args[0])
    let x = zonk(ms, eqSpine.args[1])
    let y = zonk(ms, eqSpine.args[2])
    for reverse in [false, true]:
      let start = if reverse: y else: x
      let finish = if reverse: x else: y
      let shiftedGoal = weaken(weaken(goal))
      let shiftedStart = weaken(weaken(start))
      let occurrenceCount = replaceOccurrences(
        shiftedGoal, shiftedStart, 1).count
      if occurrenceCount == 0: continue

      let zName = freshen("rewriteValue", target.holeCtx.mapIt(it.name))
      let qName = freshen("rewriteProof", target.holeCtx.mapIt(it.name) & @[zName])
      let pName = freshen("rewriteGoal", target.holeCtx.mapIt(it.name) & @[zName, qName])
      let zCtx = @[CtxEntry(name: zName, ty: aTy, qty: qOmega)] & ctx
      let xAtZ = weaken(start)
      let aAtZ = weaken(aTy)
      let qTy = tmApp(tmApp(tmApp(eqSpine.head, aAtZ), xAtZ), vv(0))
      let qCtx = @[CtxEntry(name: qName, ty: qTy, qty: qOmega)] & zCtx
      let goalUnderMotive = weaken(weaken(goal))
      let goalUnderText = prettyTerm(goalUnderMotive, qCtx,
        ms.refNames, ms.recordFields)
      let aText = prettyTerm(aTy, ctx, ms.refNames, ms.recordFields)
      let startText = prettyTerm(start, ctx, ms.refNames, ms.recordFields)
      let finishText = prettyTerm(finish, ctx, ms.refNames, ms.recordFields)
      let qTyText = prettyTerm(qTy, zCtx, ms.refNames, ms.recordFields)
      let goalText = prettyTerm(goal, ctx, ms.refNames, ms.recordFields)
      let xText = prettyTerm(x, ctx, ms.refNames, ms.recordFields)
      let yText = prettyTerm(y, ctx, ms.refNames, ms.recordFields)
      let proofText = if reverse:
          "(sym " & aText & " " & xText & " " & yText & " " & b.name & ")"
        else: b.name
      for occurrence in 0 ..< occurrenceCount:
        var seen = 0
        let replaced = replaceOccurrenceAt(shiftedGoal, shiftedStart, 1,
                                            occurrence, seen)
        if not replaced.found: continue
        let rewrittenText = prettyTerm(replaced.term, qCtx,
          ms.refNames, ms.recordFields)
        let candidate = "eqElim " & aText & " " & startText &
          " (lam(" & zName & ": " & aText & ") => lam(" & qName & ": " &
          qTyText & ") => (" & rewrittenText & " -> " & goalUnderText & ")) " &
          " (lam(" & pName & ": " & goalText & ") => " & pName & ") " &
          finishText & " " & proofText & " _"
        let key = b.name & (if reverse: " reverse" else: " forward") &
          " occurrence " & $(occurrence + 1)
        var nimAText, nimStart, nimFinish, nimX, nimY: string
        var nimQTy, nimRewritten, nimGoalUnder, nimGoal: string
        var zHoleCtx: seq[HoleContextBinder] = @[]
        var qHoleCtx: seq[HoleContextBinder] = @[]
        for entry in zCtx:
          zHoleCtx.add(HoleContextBinder(name: entry.name,
            ty: entry.ty, qty: entry.qty))
        for entry in qCtx:
          qHoleCtx.add(HoleContextBinder(name: entry.name,
            ty: entry.ty, qty: entry.qty))
        if not nimTypeExpr(aTy, target.holeCtx, ms, nimAText) or
           not nimTypeExpr(start, target.holeCtx, ms, nimStart) or
           not nimTypeExpr(finish, target.holeCtx, ms, nimFinish) or
           not nimTypeExpr(x, target.holeCtx, ms, nimX) or
           not nimTypeExpr(y, target.holeCtx, ms, nimY) or
           not nimTypeExpr(qTy, zHoleCtx, ms, nimQTy) or
           not nimTypeExpr(replaced.term, qHoleCtx, ms, nimRewritten) or
           not nimTypeExpr(goalUnderMotive, qHoleCtx, ms, nimGoalUnder) or
           not nimTypeExpr(goal, target.holeCtx, ms, nimGoal):
          continue
        let nimProof = if reverse:
          "sym[" & nimAText & "](" & nimX & ", " & nimY & ", " & b.name & ")"
        else: b.name
        let nimMotive = "lam(" & zName & ": " & nimAText & ") => lam(" &
          qName & ": " & nimQTy & ") => Pi(" & pName & ": " & nimRewritten &
          ", " & nimGoalUnder & ")"
        let nimBase = "lam(" & pName & ": " & nimGoal & ") => " & pName
        let nimCandidate = "eqElim[" & nimAText & "](" & nimStart & ", " &
          nimMotive & ", " & nimBase & ", " & nimFinish & ", " & nimProof &
          ", shedHole(" & shedName & "))"
        let probe = fillHoleAt(oldSrc, line - 1, col - 1,
                               "(" & candidate & ")", baseDir)
        if not probe.ok:
          continue
        candidates.add(key)
        if key == selected:
          selectedTerm = candidate
          selectedClientTerm = nimCandidate

  if selected.len == 0:
    if candidates.len == 0:
      return (true, "No checked equality rewrite is available. The goal must " &
        "contain an exact structural endpoint from an in-scope Eq proof, and " &
        "the resulting motive must be expressible in shed syntax. No edit was made.",
        @[], "", 0, 0, "", 0)
    return (true, "", candidates, "", 0, 0, "", 0)
  if selected notin candidates:
    return (false, "rewrite choice '" & selected &
            "' is not feasible for this goal; available: " & candidates.join(", "),
            candidates, "", 0, 0, "", 0)
  var plannedSheds: seq[ShedInfo] = @[]
  let refined = refineShedPlan(nimFile, shedName, selectedTerm, sheds,
                               inputErrMsg, plannedSheds)
  if not refined.ok:
    return (false, refined.why, candidates, "", 0, 0, "", 0)
  updatedSheds = plannedSheds
  (true, "", candidates, selectedClientTerm, refined.nimLine, refined.nimCol,
   refined.status, refined.yellowCount)

proc refineEqualityShed*(nimFile, shedName: string, selected = ""):
    tuple[ok: bool, why: string, candidates: seq[string], term: string,
          nimLine, nimCol: int, status: string, yellowCount: int] =
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)", @[], "", 0, 0, "", 0)
  let (sheds, errMsg) = readShedSidecarEx(sc)
  var updated: seq[ShedInfo] = @[]
  result = refineEqualityShedPlan(nimFile, shedName, selected, sheds, errMsg, updated)
  if result.ok and selected.len > 0:
    writeShedSidecar(nimFile, updated, errMsg)

proc caseSplitShedDetailedPlan(nimFile, shedName, variable: string,
                           inputSheds: seq[ShedInfo], generatedSource: var string,
                           updatedSheds: var seq[ShedInfo]):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          subSheds: seq[string]] =
  ## Issue #209: shed-aware case-split (term-level via eliminators).
  ##
  ## The `.ep` `textDocument/codeAction` path rewrites a `proc` into a
  ## clause-style `def`, which cannot round-trip through the nim `![...]`
  ## node (an expression position; a clause-def is not a term and not
  ## valid Nim). Instead, fill the shed's hole with an eliminator
  ## application whose method holes become fresh sub-sheds:
  ##   `![isZeroBody]` --case-split n--> `natElim(lam(u: Nat) => Bool,
  ##    ![isZeroBody_zero], ![isZeroBody_suc], n)`
  ## The returned `term` is nim-syntax text for the client to splice over
  ## the `![shedName]` node; `subSheds` are the fresh sub-shed names.
  ## Only non-parameterized, non-indexed datatypes are supported for now.
  let sheds0 = cloneShedInfos(inputSheds)
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
  var motiveEp = "(lam(u: " & familyEp & ") => " & motiveGoalEp & ")"
  var motiveNim = "lam(u: " & familyNim & ") => " & motiveGoalNim
  for j in countdown(indexCount - 1, 0):
    motiveEp = "(lam(" & indexNames[j] & ": " & indexDomainEp[j] &
               ") => " & motiveEp & ")"
    motiveNim = "lam(" & indexNames[j] & ": " & indexDomainNim[j] &
                ") => " & motiveNim
  var epArgs: seq[string] = paramEp
  epArgs.add(motiveEp)
  var nimArgs: seq[string] = @[motiveNim]
  for ss in subSheds:
    epArgs.add("_")
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
  generatedSource = f.newSrc
  let fillOffset = sourceOffset(oldSrc, sheds0[si].holeLine, sheds0[si].holeCol)
  if fillOffset < 0:
    return (false, "case-split hole position is outside its generated source", "", 0, 0, @[])
  let checkedAfter = elabCheckHolesDir(f.newSrc, baseDir)
  if checkedAfter.errMsg != "":
    return (false, "case-split rejected: " & checkedAfter.errMsg, "", 0, 0, @[])
  var after: seq[ShedInfo] = @[]
  for i, oldItem in sheds0:
    var oldShed = oldItem
    if oldShed.genSrc != oldSrc:
      after.add(oldShed)
      continue
    if i == si: continue
    let oldOffset = sourceOffset(oldSrc, oldShed.holeLine, oldShed.holeCol)
    if oldOffset < 0: continue
    var movedOffset = oldOffset
    for edit in f.editRanges:
      let editOffset = sourceOffset(oldSrc, edit.startLine + 1, edit.startChar + 1)
      let removed = edit.endChar - edit.startChar
      if editOffset < oldOffset: movedOffset += epTerm.len - removed
    var matched = -1
    for hi, hole in checkedAfter.ms.holes:
      if sourceOffset(f.newSrc, hole.holeLoc.line, hole.holeLoc.col) == movedOffset:
        matched = hi
        oldShed.holeLine = hole.holeLoc.line
        oldShed.holeCol = hole.holeLoc.col
        let (goal, ctx, goalPi) = shedGoalAndCtx(checkedAfter.ms, hole)
        oldShed.goal = goal
        oldShed.ctx = ctx
        oldShed.goalPi = goalPi
        break
    if matched >= 0:
      oldShed.holeIdx = matched
      oldShed.genSrc = f.newSrc
      oldShed.status = ssYellow
      after.add(oldShed)
  var childIndex = 0
  for holeIndex, hole in checkedAfter.ms.holes:
    let holeOffset = sourceOffset(f.newSrc, hole.holeLoc.line, hole.holeLoc.col)
    if holeOffset < fillOffset or holeOffset >= fillOffset + epTerm.len: continue
    if childIndex >= subSheds.len: break
    let subName = subSheds[childIndex]
    let (goal, ctx, goalPi) = shedGoalAndCtx(checkedAfter.ms, hole)
    let markerOffset = nimTerm.find("![" & subName)
    if markerOffset < 0:
      return (false, "case-split result is missing child marker " & subName, "", 0, 0, @[])
    let markerPos = sourcePosition(nimTerm, markerOffset)
    let childLine = sheds0[si].nimLine + markerPos.line - 1
    let childCol = if markerPos.line == 1: sheds0[si].nimCol + markerPos.col - 1
                   else: markerPos.col
    after.add(ShedInfo(name: subName, nimLine: childLine, nimCol: childCol,
      holeLine: hole.holeLoc.line, holeCol: hole.holeLoc.col,
      holeIdx: holeIndex, genSrc: f.newSrc, goal: goal, ctx: ctx,
      goalPi: goalPi, status: ssYellow))
    inc childIndex
  if childIndex != subSheds.len:
    return (false, "case-split result did not preserve all child goals", "", 0, 0, @[])
  refreshShedStatuses(after, f.newSrc, baseDir, onlyGenSrc = f.newSrc)
  updatedSheds = after
  (true, "", nimTerm, sheds0[si].nimLine, sheds0[si].nimCol, subSheds)

proc caseSplitShedDetailed(nimFile, shedName, variable: string,
                           generatedSource: var string):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          subSheds: seq[string]] =
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)", "", 0, 0, @[])
  let (sheds, _) = readShedSidecarEx(sc)
  var updated: seq[ShedInfo] = @[]
  caseSplitShedDetailedPlan(nimFile, shedName, variable, sheds,
                            generatedSource, updated)

proc caseSplitShed*(nimFile, shedName, variable: string):
    tuple[ok: bool, why: string, term: string, nimLine, nimCol: int,
          subSheds: seq[string]] =
  ## Public disk-backed compatibility wrapper over the in-memory planner.
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar for " & nimFile &
            " (compile the file with shedsBlock first)", "", 0, 0, @[])
  let (sheds, errMsg) = readShedSidecarEx(sc)
  var generated = ""
  var updated: seq[ShedInfo] = @[]
  result = caseSplitShedDetailedPlan(nimFile, shedName, variable, sheds,
                                     generated, updated)
  discard errMsg

proc documentRevision(server: LspServer, uri: string): int =
  for item in server.documentRevisions:
    if item.uri == uri: return item.revision

proc bumpDocumentRevision(server: var LspServer, uri: string) =
  for i in 0 ..< server.documentRevisions.len:
    if server.documentRevisions[i].uri == uri:
      inc server.documentRevisions[i].revision
      return
  server.documentRevisions.add((uri, 1))

proc invalidateShedActionVersions(server: var LspServer, uri: string) =
  var live: seq[ShedActionStateVersion] = @[]
  for version in server.shedActionStateVersions:
    if version.uri != uri: live.add(version)
  server.shedActionStateVersions = live

proc actionDescriptor(id, kind, label, argumentName, argumentType: string,
                      choices, expectedSubgoals: JsonNode): JsonNode =
  var argument = %*{"name": argumentName, "type": argumentType,
                     "required": true}
  if not choices.isNil: argument["choices"] = choices
  %*{"id": id, "kind": kind, "label": label,
     "arguments": [argument], "expectedSubgoals": expectedSubgoals}

proc checkedSubgoalSnapshots(generatedSource, nimFile, previousSource: string,
                             holeLine, holeCol: int,
                             names: seq[string]): JsonNode =
  result = newJArray()
  try:
    let checked = elabCheckHolesDir(generatedSource, parentDir(nimFile))
    let holeOffset = sourceOffset(previousSource, holeLine, holeCol)
    if holeOffset < 0: return
    var tokenLen = 1
    while holeOffset + tokenLen < previousSource.len and
          previousSource[holeOffset + tokenLen] in {'0'..'9'}:
      inc tokenLen
    let prefix = previousSource[0 ..< holeOffset]
    let suffixOffset = holeOffset + tokenLen
    let suffix = if suffixOffset < previousSource.len:
      previousSource[suffixOffset .. ^1]
    else: ""
    if not generatedSource.startsWith(prefix) or
       (suffix.len > 0 and not generatedSource.endsWith(suffix)):
      return
    let changedEnd = generatedSource.len - suffix.len
    var index = 0
    for hole in checked.ms.holes:
      let offset = sourceOffset(generatedSource, hole.holeLoc.line,
                                hole.holeLoc.col)
      if offset < prefix.len or offset >= changedEnd: continue
      let (goal, context, _) = shedGoalAndCtx(checked.ms, hole)
      let name = if index < names.len: names[index] else: "goal" & $index
      result.add(%*{"name": name, "goal": goal, "context": context})
      inc index
  except ParseError:
    discard

proc availableShedActions*(server: var LspServer, uri, shedName: string):
    tuple[ok: bool, why: string, result: JsonNode] =
  ## Query checker-backed affordances for one open shed. Returned choices are
  ## presentation-neutral; consumers choose how to rank or render them.
  if uri notin server.documents:
    return (false, "unknown document; open it before querying shed actions", nil)
  let nimFile = uriToPath(uri)
  if not fileExists(nimFile):
    return (false, "document file does not exist: " & nimFile, nil)
  if readFile(nimFile) != server.documents[uri]:
    return (false, "document changed on disk; synchronize or save before querying shed actions", nil)
  let sc = sidecarPath(nimFile)
  if not fileExists(sc):
    return (false, "no sheds sidecar; compile the document before querying shed actions", nil)
  var target: ShedInfo
  var found = false
  for shed in readShedSidecar(sc):
    if shed.name == shedName:
      target = shed
      found = true
      break
  if not found:
    return (false, "unknown shed '" & shedName & "'", nil)
  if target.status != ssYellow or target.genSrc == "":
    return (false, "shed '" & shedName & "' is not an open checked goal", nil)

  var ms: MetaStore
  var targetHole: HoleInfo
  var foundHole = false
  try:
    ms = elabCheckHolesDir(target.genSrc, parentDir(nimFile)).ms
    for hole in ms.holes:
      if hole.holeLoc.line == target.holeLine and
         (target.holeCol <= 0 or hole.holeLoc.col == target.holeCol):
        targetHole = hole
        foundHole = true
        break
  except ParseError as e:
    return (false, "checked shed source no longer parses: " & e.msg, nil)
  if not foundHole:
    return (false, "shed goal is stale; compile the document again", nil)

  let semantic = semanticShedState(ms, targetHole)
  let rendered = renderShedGoalCtx(ms, semantic)
  var actions = newJArray()
  actions.add(actionDescriptor("refine", "refine", "Refine with a term",
    "term", "eponym-term", nil,
    %*{"kind": "checker-determined", "description":
       "The accepted term may leave zero or more typed goals."}))
  actions.add(actionDescriptor("give", "give", "Give a complete term",
    "term", "eponym-term", nil,
    %*{"kind": "complete-proof", "description":
       "The checker requires the term to close this goal completely."}))

  if semantic.goalPi.len > 0:
    var counts = newJArray()
    var shapes = newJObject()
    for count in 1 .. semantic.goalPi.len:
      counts.add(%count)
      var binders = newJArray()
      var goal = zonk(ms, semantic.goal)
      var context = semanticContext(semantic)
      for _ in 0 ..< count:
        if goal.kind != tPi: break
        let name = goal.scope.adv
        let domain = zonk(ms, goal.dom)
        binders.add(%*{"name": name,
                       "type": prettyTerm(domain, context, ms.refNames,
                                            ms.recordFields),
                       "implicit": goal.impl,
                       "quantity": $goal.qty})
        context = @[CtxEntry(name: name, ty: domain,
                             qty: toQty(goal.qty))] & context
        goal = zonk(ms, goal.scope.bdy)
      shapes[$count] = %*{"binders": binders,
        "goal": prettyTerm(goal, context, ms.refNames, ms.recordFields)}
    actions.add(actionDescriptor("intro", "intro", "Introduce binders",
      "count", "positive-integer", counts,
      %*{"kind": "byChoice", "choices": shapes}))

  var splitChoices = newJArray()
  var splitShapes = newJObject()
  for binder in semantic.context:
    if binder.name.len == 0 or binder.name == "_": continue
    var generated = ""
    let split = caseSplitShedDetailed(nimFile, shedName, binder.name, generated)
    if not split.ok: continue
    splitChoices.add(%binder.name)
    splitShapes[binder.name] = checkedSubgoalSnapshots(generated, nimFile,
      target.genSrc, target.holeLine, target.holeCol, split.subSheds)
  if splitChoices.len > 0:
    actions.add(actionDescriptor("caseSplit", "caseSplit", "Case-split",
      "variable", "local-variable", splitChoices,
      %*{"kind": "constructor-branches", "byChoice": splitShapes}))

  let constructors = refineConstructorsShed(nimFile, shedName)
  if constructors.ok and constructors.constructors.len > 0:
    var choices = newJArray()
    var shapeByConstructor = newJObject()
    for name in constructors.constructors: choices.add(%name)
    for cid, ctorName in ms.ctorTable.ctorNames:
      if ctorName notin constructors.constructors or
         cid notin ms.ctorTable.ctorTypes: continue
      var arity = 0
      var ctorTy = zonk(ms, ms.ctorTable.ctorTypes[cid])
      while ctorTy != nil and ctorTy.kind == tPi:
        inc arity
        ctorTy = zonk(ms, ctorTy.scope.bdy)
      let candidate = ctorName & repeat(" _", arity)
      let probe = fillHoleAt(target.genSrc, target.holeLine - 1,
        target.holeCol - 1, "(" & candidate & ")", parentDir(nimFile))
      if not probe.ok: continue
      var fieldNames: seq[string] = @[]
      for i in 0 ..< arity:
        fieldNames.add(ctorName & "_field" & $i)
      shapeByConstructor[ctorName] = checkedSubgoalSnapshots(probe.newSrc,
        nimFile, target.genSrc, target.holeLine, target.holeCol, fieldNames)
    actions.add(actionDescriptor("construct", "construct",
      "Construct a value", "constructor", "feasible-constructor", choices,
      %*{"kind": "byChoice", "choices": shapeByConstructor}))

  let applications = refineFromContextShed(nimFile, shedName)
  if applications.ok and applications.candidates.len > 0:
    var choices = newJArray()
    var shapeByCandidate = newJObject()
    for candidate in applications.candidates:
      choices.add(%candidate)
      let probe = fillHoleAt(target.genSrc, target.holeLine - 1,
        target.holeCol - 1, "(" & candidate & ")", parentDir(nimFile))
      var goalNames: seq[string] = @[]
      for i in 0 ..< candidate.splitWhitespace().count("_") + candidate.count('?'):
        goalNames.add("apply_goal" & $i)
      shapeByCandidate[candidate] = if probe.ok:
        checkedSubgoalSnapshots(probe.newSrc, nimFile, target.genSrc,
          target.holeLine, target.holeCol, goalNames)
      else: newJArray()
    actions.add(actionDescriptor("apply", "apply",
      "Apply a local hypothesis", "candidate", "feasible-application",
      choices, %*{"kind": "byChoice", "choices": shapeByCandidate}))

  let rewrites = refineEqualityShed(nimFile, shedName)
  if rewrites.ok and rewrites.candidates.len > 0:
    var choices = newJArray()
    for candidate in rewrites.candidates: choices.add(%candidate)
    actions.add(actionDescriptor("rewrite", "rewrite",
      "Rewrite using an equality", "rewrite", "checked-equality-rewrite",
      choices, %*{"kind": "one-residual-goal"}))

  inc server.nextShedActionStateVersion
  let version = server.nextShedActionStateVersion
  if server.shedActionStateVersions.len >= MaxShedActionStateVersions:
    server.shedActionStateVersions.delete(0)
  server.shedActionStateVersions.add(ShedActionStateVersion(
    version: version, uri: uri, shedName: shedName,
    documentRevision: documentRevision(server, uri),
    generatedSource: target.genSrc, goal: rendered.goal,
    context: rendered.ctx, actions: actions))
  result = (true, "", %*{
    "stateVersion": version,
    "goal": rendered.goal,
    "context": rendered.ctx,
    "actions": actions
  })

proc validateShedActionVersion(server: LspServer, uri, shedName: string,
                               version: int, actionId: string):
    tuple[ok: bool, why: string, snapshot: ShedActionStateVersion] =
  var found = false
  for snapshot in server.shedActionStateVersions:
    if snapshot.version == version:
      result.snapshot = snapshot
      found = true
      break
  if not found or result.snapshot.uri != uri or
     result.snapshot.shedName != shedName:
    return (false, "unknown or expired proof-state version", result.snapshot)
  if uri notin server.documents or
     documentRevision(server, uri) != result.snapshot.documentRevision or
     not fileExists(uriToPath(uri)) or
     readFile(uriToPath(uri)) != server.documents[uri]:
    return (false, "proof state changed since actions were queried", result.snapshot)
  var currentGenSrc = ""
  for shed in readShedSidecar(sidecarPath(uriToPath(uri))):
    if shed.name == shedName:
      currentGenSrc = shed.genSrc
      break
  if currentGenSrc == "" or currentGenSrc != result.snapshot.generatedSource:
    return (false, "proof state changed since actions were queried", result.snapshot)
  var actionFound = false
  for action in result.snapshot.actions:
    if action["id"].getStr() == actionId:
      actionFound = true
      break
  if not actionFound:
    return (false, "action was not offered for this proof-state version", result.snapshot)
  (true, "", result.snapshot)

proc argumentOffered(action: JsonNode, arguments: JsonNode): bool =
  if arguments.kind != JObject or "arguments" notin action: return false
  let schema = action["arguments"]
  for key in arguments.keys:
    var known = false
    for argument in schema:
      if argument["name"].getStr() == key:
        known = true
        break
    if not known: return false
  for required in schema:
    let name = required["name"].getStr()
    if required["required"].getBool() and name notin arguments: return false
    if name notin arguments: continue
    if "choices" in required:
      var choiceFound = false
      for choice in required["choices"]:
        if choice == arguments[name]: choiceFound = true
      if not choiceFound: return false
    case required["type"].getStr()
    of "positive-integer":
      if arguments[name].kind != JInt or arguments[name].getInt() < 1:
        return false
    of "string", "eponym-term", "local-variable", "feasible-constructor",
       "feasible-application", "checked-equality-rewrite":
      if arguments[name].kind != JString: return false
    else: discard
  true

proc currentShedGoals(nimFile, shedName, previousSource: string): JsonNode =
  result = newJArray()
  if not fileExists(sidecarPath(nimFile)): return
  let sheds = readShedSidecar(sidecarPath(nimFile))
  var resultingSource = ""
  for shed in sheds:
    if shed.genSrc != "" and shed.genSrc != previousSource:
      resultingSource = shed.genSrc
      break
  if resultingSource == "":
    for shed in sheds:
      if shed.name == shedName or shed.name.startsWith(shedName & "_"):
        resultingSource = shed.genSrc
        break
  if resultingSource == "": return
  for shed in sheds:
    if shed.genSrc == resultingSource and shed.status == ssYellow:
      result.add(%*{"name": shed.name, "goal": shed.goal,
                     "context": shed.ctx, "status": shedStatusToStr(shed.status)})

proc prepareShedAction*(server: var LspServer, uri, shedName,
                        actionName, term, variable: string,
                        requireComplete: bool):
    tuple[ok: bool, why: string, result: JsonNode]

proc submitShedAction*(server: var LspServer, uri, shedName: string,
                       stateVersion: int, actionId: string,
                       arguments: JsonNode):
    tuple[ok: bool, why: string, result: JsonNode] =
  let checkedVersion = validateShedActionVersion(server, uri, shedName,
                                                  stateVersion, actionId)
  if not checkedVersion.ok: return (false, checkedVersion.why, nil)
  var descriptor: JsonNode
  for item in checkedVersion.snapshot.actions:
    if item["id"].getStr() == actionId:
      descriptor = item
      break
  if descriptor.isNil or not argumentOffered(descriptor, arguments):
    return (false, "action arguments do not match the queried affordance", nil)

  let kind = descriptor["kind"].getStr()
  let term = if "term" in arguments: arguments["term"].getStr() else: ""
  let variable = if "variable" in arguments: arguments["variable"].getStr() else: ""
  let previousSource = checkedVersion.snapshot.generatedSource
  if kind == "refine" or kind == "give" or kind == "caseSplit":
    let r = prepareShedAction(server, uri, shedName, kind, term, variable,
                              kind == "give")
    if not r.ok: return (false, r.why, nil)
    invalidateShedActionVersions(server, uri)
    var payload = r.result
    payload["proofStateVersion"] = %stateVersion
    payload["action"]["id"] = %actionId
    return (true, "", payload)

  var editTerm = ""
  var nimLine = 0
  var nimCol = 0
  var status = "yellow"
  var yellowCount = 0
  var subSheds: seq[string] = @[]
  var actionArguments = arguments
  case kind
  of "intro":
    let count = arguments["count"].getInt()
    let r = introShed(uriToPath(uri), shedName, count)
    if not r.ok: return (false, r.why, nil)
    editTerm = r.term
    nimLine = r.nimLine
    nimCol = r.nimCol
    status = r.status
    yellowCount = r.yellowCount
  of "construct":
    let constructor = arguments["constructor"].getStr()
    let r = refineConstructorsShed(uriToPath(uri), shedName, constructor)
    if not r.ok: return (false, r.why, nil)
    editTerm = r.term
    nimLine = r.nimLine
    nimCol = r.nimCol
    status = r.status
    yellowCount = r.yellowCount
  of "apply":
    let candidate = arguments["candidate"].getStr()
    let r = refineFromContextShed(uriToPath(uri), shedName, candidate)
    if not r.ok: return (false, r.why, nil)
    editTerm = r.term
    nimLine = r.nimLine
    nimCol = r.nimCol
    status = r.status
    yellowCount = r.yellowCount
  of "rewrite":
    let rewrite = arguments["rewrite"].getStr()
    let r = refineEqualityShed(uriToPath(uri), shedName, rewrite)
    if not r.ok: return (false, r.why, nil)
    editTerm = r.term
    nimLine = r.nimLine
    nimCol = r.nimCol
    status = r.status
    yellowCount = r.yellowCount
  else:
    return (false, "unsupported semantic shed action '" & kind & "'", nil)

  let afterGoals = currentShedGoals(uriToPath(uri), shedName, previousSource)
  for goal in afterGoals:
    let name = goal["name"].getStr()
    if name.startsWith(shedName & "_"): subSheds.add(name)
  invalidateShedActionVersions(server, uri)
  result = (true, "", %*{
    "id": stateVersion,
    "proofStateVersion": stateVersion,
    "action": {"id": actionId, "kind": kind, "target": shedName,
                "arguments": actionArguments},
    "before": {"goal": checkedVersion.snapshot.goal,
               "context": checkedVersion.snapshot.context},
    "edit": {"term": editTerm, "nimLine": nimLine, "nimCol": nimCol},
    "after": {"goals": afterGoals},
    "validation": {"accepted": true, "status": status,
                   "yellowCount": yellowCount},
    "subSheds": subSheds
  })

proc shedHistoryIndex(server: LspServer, uri: string): int =
  for i, history in server.shedHistories:
    if history.uri == uri: return i
  -1

proc ensureShedHistory(server: var LspServer, uri: string): int =
  result = shedHistoryIndex(server, uri)
  if result < 0:
    server.shedHistories.add(ShedActionHistory(uri: uri, cursor: 0))
    result = server.shedHistories.high

proc actionKindName(kind: ShedActionKind): string =
  case kind
  of sakRefine: "refine"
  of sakGive: "give"
  of sakCaseSplit: "caseSplit"

proc actionKindFromName(name: string, kind: var ShedActionKind): bool =
  case name
  of "refine": kind = sakRefine
  of "give": kind = sakGive
  of "caseSplit": kind = sakCaseSplit
  else: return false
  true

proc historyHasSource(nimFile, generatedSource: string): bool =
  if generatedSource == "" or not fileExists(sidecarPath(nimFile)): return false
  for shed in readShedSidecar(sidecarPath(nimFile)):
    if shed.genSrc == generatedSource: return true

proc transitionJson(transition: ShedActionTransition): JsonNode =
  var args = newJObject()
  case transition.kind
  of sakRefine, sakGive:
    args["term"] = %transition.term
  of sakCaseSplit:
    args["variable"] = %transition.variable
  %*{
    "id": transition.id,
    "action": {"kind": actionKindName(transition.kind),
                "target": transition.shedName, "arguments": args},
    "before": {"goal": transition.beforeGoal,
               "context": transition.beforeContext},
    "edit": {"term": transition.spliceTerm,
             "nimLine": transition.nimLine, "nimCol": transition.nimCol},
    "after": {"goals": transition.afterGoals},
    "validation": {"accepted": true, "status": transition.status,
                   "yellowCount": transition.yellowCount},
    "subSheds": transition.subSheds
  }

proc prepareShedAction*(server: var LspServer, uri, shedName,
                        actionName, term, variable: string,
                        requireComplete: bool):
    tuple[ok: bool, why: string, result: JsonNode] =
  ## Run a proof edit through the common, checker-backed transition API.
  ## The client owns source projection and must commit only after applying the
  ## returned edit and compiling the resulting Nim document.
  if uri notin server.documents:
    return (false, "unknown document; open it before applying a shed action", nil)
  var kind: ShedActionKind
  if not actionKindFromName(actionName, kind):
    return (false, "unknown shed action '" & actionName & "'", nil)
  if kind in {sakRefine, sakGive} and term.len == 0:
    return (false, "refine/give action requires a term", nil)
  if kind == sakCaseSplit and variable.len == 0:
    return (false, "caseSplit action requires a variable", nil)
  let nimFile = uriToPath(uri)
  if not fileExists(nimFile):
    return (false, "document file does not exist: " & nimFile, nil)
  let beforeDocument = server.documents[uri]
  if readFile(nimFile) != beforeDocument:
    return (false, "document changed on disk; synchronize or save before acting", nil)
  let historyIdx = ensureShedHistory(server, uri)
  if server.shedHistories[historyIdx].pendingMove != shmNone:
    return (false, "a shed transition is awaiting client commit", nil)

  let beforeSheds = readShedSidecar(sidecarPath(nimFile))
  var targetBefore: ShedInfo
  var foundTarget = false
  for shed in beforeSheds:
    if shed.name == shedName:
      targetBefore = shed
      foundTarget = true
      break
  if not foundTarget:
    return (false, "unknown shed '" & shedName & "'", nil)
  if targetBefore.genSrc == "":
    return (false, "shed '" & shedName & "' has no checked source; recompile", nil)

  var spliceTerm = ""
  var nimLine = 0
  var nimCol = 0
  var status = ""
  var yellowCount = 0
  var subSheds: seq[string] = @[]
  var afterGenSrc = ""
  case kind
  of sakRefine, sakGive:
    let r = refineShed(nimFile, shedName, term,
                       requireComplete or kind == sakGive)
    if not r.ok: return (false, r.why, nil)
    spliceTerm = r.term
    nimLine = r.nimLine
    nimCol = r.nimCol
    status = r.status
    yellowCount = r.yellowCount
  of sakCaseSplit:
    let r = caseSplitShedDetailed(nimFile, shedName, variable, afterGenSrc)
    if not r.ok: return (false, r.why, nil)
    spliceTerm = r.term
    nimLine = r.nimLine
    nimCol = r.nimCol
    subSheds = r.subSheds
    status = "yellow"
    yellowCount = r.subSheds.len

  let afterSheds = readShedSidecar(sidecarPath(nimFile))
  if afterGenSrc == "":
    for shed in afterSheds:
      if shed.genSrc != targetBefore.genSrc:
        afterGenSrc = shed.genSrc
        break
  if afterGenSrc == "":
    # A valid edit may leave the generated Eponym text unchanged (for
    # example, refining with a new named hole); use the target's new entry.
    for shed in afterSheds:
      if shed.name == shedName or shed.name.startsWith(shedName & "_"):
        afterGenSrc = shed.genSrc
        break
  if afterGenSrc == "":
    return (false, "the checked edit did not produce refreshed shed metadata", nil)
  var afterGoals: seq[ShedGoalSnapshot] = @[]
  for shed in afterSheds:
    if shed.genSrc == afterGenSrc:
      afterGoals.add(ShedGoalSnapshot(shedName: shed.name,
        goal: shed.goal, context: shed.ctx,
        status: shedStatusToStr(shed.status)))
  if kind == sakCaseSplit and afterGoals.len == 0:
    try:
      let checked = elabCheckHolesDir(afterGenSrc, parentDir(nimFile))
      for i, hole in checked.ms.holes:
        let (goal, context, _) = shedGoalAndCtx(checked.ms, hole)
        let name = if i < subSheds.len: subSheds[i]
                   else: shedName & "_goal" & $i
        afterGoals.add(ShedGoalSnapshot(shedName: name, goal: goal,
          context: context, status: "yellow"))
    except ParseError as e:
      return (false, "case-split transition could not be summarized: " & e.msg, nil)

  var transition = ShedActionTransition(
    id: server.nextShedTransitionId + 1,
    kind: kind, shedName: shedName, term: term, variable: variable,
    requireComplete: requireComplete or kind == sakGive,
    beforeDocument: beforeDocument, beforeGenSrc: targetBefore.genSrc,
    afterGenSrc: afterGenSrc, beforeGoal: targetBefore.goal,
    beforeContext: targetBefore.ctx,
    spliceTerm: spliceTerm, nimLine: nimLine, nimCol: nimCol,
    status: status, yellowCount: yellowCount, subSheds: subSheds,
    afterGoals: afterGoals)
  server.nextShedTransitionId = transition.id
  let history = addr server.shedHistories[historyIdx]
  if history.cursor < history.transitions.len:
    history.transitions.setLen(history.cursor)
  if history.transitions.len >= MaxShedHistoryTransitions:
    history.transitions.delete(0)
    dec history.cursor
  history.transitions.add(transition)
  history.pendingMove = shmCommit
  history.pendingId = transition.id
  result = (true, "", transitionJson(transition))

proc commitShedAction*(server: var LspServer, uri: string, transitionId: int):
    tuple[ok: bool, why: string, result: JsonNode] =
  let historyIdx = shedHistoryIndex(server, uri)
  if historyIdx < 0:
    return (false, "no action history for this document", nil)
  let history = addr server.shedHistories[historyIdx]
  if history.pendingMove != shmCommit or history.pendingId != transitionId:
    return (false, "unknown or stale transition id", nil)
  if history.transitions.len == 0 or history.cursor >= history.transitions.len:
    return (false, "pending transition is missing from history", nil)
  let transitionIdx = history.transitions.high
  var transition = history.transitions[transitionIdx]
  if uri notin server.documents or not fileExists(uriToPath(uri)):
    return (false, "document is not open or its file is missing", nil)
  let currentDocument = server.documents[uri]
  if readFile(uriToPath(uri)) != currentDocument:
    return (false, "saved document does not match the synchronized editor text", nil)
  if not historyHasSource(uriToPath(uri), transition.afterGenSrc):
    return (false, "compiled document does not match the transition result", nil)
  transition.afterDocument = currentDocument
  transition.afterGoals.setLen(0)
  for shed in readShedSidecar(sidecarPath(uriToPath(uri))):
    if shed.genSrc == transition.afterGenSrc:
      transition.afterGoals.add(ShedGoalSnapshot(shedName: shed.name,
        goal: shed.goal, context: shed.ctx,
        status: shedStatusToStr(shed.status)))
  history.transitions[transitionIdx] = transition
  history.cursor = history.transitions.len
  history.pendingMove = shmNone
  history.pendingId = 0
  (true, "", transitionJson(transition))

proc shedHistoryJson(history: ShedActionHistory): JsonNode =
  result = newJArray()
  for i, transition in history.transitions:
    var entry = transitionJson(transition)
    entry["applied"] = %(i < history.cursor)
    result.add(entry)

proc inspectShedActionHistory*(server: LspServer, uri: string): JsonNode =
  let historyIdx = shedHistoryIndex(server, uri)
  if historyIdx < 0:
    return %*{"cursor": 0, "canUndo": false, "canRedo": false,
               "transitions": []}
  let history = server.shedHistories[historyIdx]
  var canUndo = false
  var canRedo = false
  if uri in server.documents and fileExists(uriToPath(uri)) and
     readFile(uriToPath(uri)) == server.documents[uri] and
     history.pendingMove == shmNone:
    if history.cursor > 0:
      let previous = history.transitions[history.cursor - 1]
      canUndo = server.documents[uri] == previous.afterDocument and
        historyHasSource(uriToPath(uri), previous.afterGenSrc)
    if history.cursor < history.transitions.len:
      let next = history.transitions[history.cursor]
      canRedo = server.documents[uri] == next.beforeDocument and
        historyHasSource(uriToPath(uri), next.beforeGenSrc)
  %*{"cursor": server.shedHistories[historyIdx].cursor,
     "canUndo": canUndo, "canRedo": canRedo,
     "transitions": shedHistoryJson(server.shedHistories[historyIdx])}

proc prepareUndoShedAction*(server: var LspServer, uri: string):
    tuple[ok: bool, why: string, result: JsonNode] =
  let historyIdx = shedHistoryIndex(server, uri)
  if historyIdx < 0 or server.shedHistories[historyIdx].cursor == 0:
    return (false, "there is no committed shed action to undo", nil)
  let history = addr server.shedHistories[historyIdx]
  if history.pendingMove != shmNone:
    return (false, "a shed transition is awaiting client commit", nil)
  let transitionIdx = history.cursor - 1
  let transition = history.transitions[transitionIdx]
  if uri notin server.documents or not fileExists(uriToPath(uri)):
    return (false, "document is not open or its file is missing", nil)
  if server.documents[uri] != transition.afterDocument or
     readFile(uriToPath(uri)) != server.documents[uri]:
    return (false, "cannot undo: document changed since this transition", nil)
  if not historyHasSource(uriToPath(uri), transition.afterGenSrc):
    return (false, "cannot undo: compiled proof state is stale", nil)
  history.pendingMove = shmUndo
  history.pendingId = transition.id
  (true, "", %*{"transitionId": transition.id,
                 "transition": transitionJson(transition)})

proc performRedoShedAction*(server: var LspServer, uri: string):
    tuple[ok: bool, why: string, result: JsonNode] =
  let historyIdx = shedHistoryIndex(server, uri)
  if historyIdx < 0:
    return (false, "there is no committed shed action to redo", nil)
  let history = addr server.shedHistories[historyIdx]
  if history.cursor >= history.transitions.len:
    return (false, "there is no committed shed action to redo", nil)
  if history.pendingMove != shmNone:
    return (false, "a shed transition is awaiting client commit", nil)
  let transitionIdx = history.cursor
  let transition = history.transitions[transitionIdx]
  if uri notin server.documents or not fileExists(uriToPath(uri)) or
     server.documents[uri] != transition.beforeDocument or
     readFile(uriToPath(uri)) != server.documents[uri]:
    return (false, "cannot redo: document changed since this transition was undone", nil)
  if not historyHasSource(uriToPath(uri), transition.beforeGenSrc):
    return (false, "cannot redo: compiled proof state is stale", nil)
  let actionName = actionKindName(transition.kind)
  let replayed = prepareShedAction(server, uri, transition.shedName,
    actionName, transition.term, transition.variable,
    transition.requireComplete)
  if not replayed.ok:
    return replayed
  let newIdx = shedHistoryIndex(server, uri)
  let pendingHistory = addr server.shedHistories[newIdx]
  let replayTransitionIdx = pendingHistory.transitions.high
  var replayTransition = pendingHistory.transitions[replayTransitionIdx]
  if replayTransition.afterGenSrc != transition.afterGenSrc or
     replayTransition.spliceTerm != transition.spliceTerm:
    pendingHistory.transitions.delete(replayTransitionIdx)
    pendingHistory.transitions.insert(transition, pendingHistory.cursor)
    pendingHistory.pendingMove = shmNone
    pendingHistory.pendingId = 0
    return (false, "redo no longer produces the recorded checked transition", nil)
  pendingHistory.transitions.delete(replayTransitionIdx)
  pendingHistory.transitions.insert(transition, pendingHistory.cursor)
  pendingHistory.pendingMove = shmRedo
  pendingHistory.pendingId = transition.id
  replayTransition.id = transition.id
  result = (true, "", transitionJson(replayTransition))

proc commitShedHistoryMove*(server: var LspServer, uri: string,
                            transitionId: int, direction: string):
    tuple[ok: bool, why: string, result: JsonNode] =
  let historyIdx = shedHistoryIndex(server, uri)
  if historyIdx < 0:
    return (false, "no action history for this document", nil)
  let history = addr server.shedHistories[historyIdx]
  let expectedMove = if direction == "undo": shmUndo elif direction == "redo": shmRedo
                     else: shmNone
  if expectedMove == shmNone or history.pendingMove != expectedMove or
     history.pendingId != transitionId:
    return (false, "unknown or stale history move", nil)
  let transitionIdx = if expectedMove == shmUndo: history.cursor - 1
                      else: history.cursor
  if transitionIdx < 0 or transitionIdx >= history.transitions.len:
    return (false, "history cursor is stale", nil)
  let transition = history.transitions[transitionIdx]
  let expectedDocument = if expectedMove == shmUndo: transition.beforeDocument
                         else: transition.afterDocument
  let expectedSource = if expectedMove == shmUndo: transition.beforeGenSrc
                       else: transition.afterGenSrc
  if uri notin server.documents or not fileExists(uriToPath(uri)) or
     server.documents[uri] != expectedDocument or
     readFile(uriToPath(uri)) != server.documents[uri]:
    return (false, "history move did not produce its expected source state", nil)
  if not historyHasSource(uriToPath(uri), expectedSource):
    return (false, "history move did not recompile to its expected proof state", nil)
  if expectedMove == shmUndo: dec history.cursor
  else: inc history.cursor
  history.pendingMove = shmNone
  history.pendingId = 0
  (true, "", inspectShedActionHistory(server, uri))

proc sourceMarkerBounds(document: string, nimLine, nimCol: int,
                        shedName: string): tuple[ok: bool, why: string, first, after: int] =
  let first = sourceOffset(document, nimLine, nimCol)
  if first < 0 or first >= document.len:
    return (false, "shed marker is missing from the selected source state", 0, 0)
  var openIndex = first
  var contentStart = first
  if document[first] == '!' and first + 1 < document.len and document[first + 1] == '[':
    openIndex = first + 1
    contentStart = first + 2
  elif document.len - first >= "shedHole(".len and
       document[first ..< first + "shedHole(".len] == "shedHole(":
    openIndex = first + "shedHole".len
    contentStart = openIndex + 1
  else:
    return (false, "shed marker is missing from the selected source state", 0, 0)

  let openDelimiter = document[openIndex]
  let closeDelimiter = if openDelimiter == '[': ']' else: ')'
  var depth = 0
  var inString = false
  var inChar = false
  var escaped = false
  for i in openIndex ..< document.len:
    let ch = document[i]
    if inString or inChar:
      if escaped: escaped = false
      elif ch == '\\': escaped = true
      elif inString and ch == '"': inString = false
      elif inChar and ch == '\'': inChar = false
      continue
    if ch == '"': inString = true; continue
    if ch == '\'': inChar = true; continue
    if ch == openDelimiter: inc depth
    elif ch == closeDelimiter:
      dec depth
      if depth == 0:
        var markerName = document[contentStart ..< i].strip()
        let comma = markerName.find(',')
        if comma >= 0: markerName = markerName[0 ..< comma].strip()
        if markerName != shedName:
          return (false, "source marker does not match goal '" & shedName & "'", 0, 0)
        return (true, "", first, i + 1)
  (false, "shed marker is unterminated in the selected source state", 0, 0)

proc replaceShedMarker(document: string, nimLine, nimCol: int,
                       shedName, replacement: string): tuple[ok: bool, why: string, text: string, first, after: int] =
  let bounds = sourceMarkerBounds(document, nimLine, nimCol, shedName)
  if not bounds.ok: return (false, bounds.why, "", 0, 0)
  result = (true, "", document[0 ..< bounds.first] & replacement &
    document[bounds.after .. ^1], bounds.first, bounds.after)

proc stableActionArguments(arguments: JsonNode): string =
  if arguments.isNil or arguments.kind != JObject: return ""
  var keys: seq[string] = @[]
  for key in arguments.keys: keys.add(key)
  keys.sort(system.cmp[string])
  for key in keys:
    result.add($key.len & ":" & key & "=" & $arguments[key] & "\n")

proc shedEnvironmentFingerprint(nimFile: string, sheds: seq[ShedInfo]): string =
  var material = "eponym-shed-env-v1\nNim=" & NimVersion &
    "\nNIMFLAGS=" & getEnv("NIMFLAGS") & "\n"
  let sourceDir = parentDir(currentSourcePath())
  for name in ["elab.nim", "unify.nim", "parse_surf.nim", "eponym_init.nim",
               "sheds.nim", "sheds_mac.nim", "shed_state.nim", "lsp.nim"]:
    let path = sourceDir / name
    if fileExists(path):
      material.add("checker-file:" & name & "\n" & sha256Hex(readFile(path)) & "\n")
  var queue: seq[string] = @[]
  for shed in sheds:
    for line in shed.genSrc.splitLines():
      let trimmed = line.strip()
      if not trimmed.startsWith("import "): continue
      let firstQuote = trimmed.find('"')
      let lastQuote = trimmed.rfind('"')
      if firstQuote >= 0 and lastQuote > firstQuote:
        queue.add(parentDir(nimFile) / trimmed[firstQuote + 1 ..< lastQuote])
  var visited = initTable[string, bool]()
  while queue.len > 0:
    let path = queue.pop()
    var canonical = path
    try: canonical = expandFilename(path)
    except OSError: discard
    if visited.hasKey(canonical): continue
    visited[canonical] = true
    if not fileExists(canonical):
      material.add("missing-import:" & canonical & "\n")
      continue
    let contents = readFile(canonical)
    material.add("import:" & canonical & "\n" & sha256Hex(contents) & "\n")
    for line in contents.splitLines():
      let trimmed = line.strip()
      if not trimmed.startsWith("import "): continue
      let firstQuote = trimmed.find('"')
      let lastQuote = trimmed.rfind('"')
      if firstQuote >= 0 and lastQuote > firstQuote:
        queue.add(parentDir(canonical) / trimmed[firstQuote + 1 ..< lastQuote])
  sha256Hex(material)

proc stateGoalName(state: ShedProofState, goalId: string): string =
  for name, id in state.goalIds:
    if id == goalId: return name

proc findStateShed(state: ShedProofState, goalId: string): tuple[found: bool, shed: ShedInfo] =
  let name = state.stateGoalName(goalId)
  if name.len == 0: return
  for shed in state.sheds:
    if shed.name == name: return (true, shed)

proc validateStateForQuery(uri: string, state: var ShedProofState): tuple[ok: bool, why: string] =
  let nimFile = uriToPath(uri)
  let expectedEnv = shedEnvironmentFingerprint(nimFile, state.sheds) &
    "\0document-uri=" & uri
  if state.environment != expectedEnv:
    return (false, "state environment changed; initialize a fresh shed state")
  var checkedSources = initTable[string, MetaStore]()
  for shedIndex in 0 ..< state.sheds.len:
    let shed = state.sheds[shedIndex]
    if shed.status != ssYellow: continue
    if shed.genSrc notin checkedSources:
      try:
        let checked = elabCheckHolesDir(shed.genSrc, parentDir(nimFile))
        if checked.errMsg != "":
          return (false, "state source is not checker-valid: " & checked.errMsg)
        checkedSources[shed.genSrc] = checked.ms
      except ParseError as e:
        return (false, "state source no longer parses: " & e.msg)
    let ms = checkedSources[shed.genSrc]
    var matched = false
    for holeIndex in 0 ..< ms.holes.len:
      let hole = ms.holes[holeIndex]
      if hole.holeLoc.line != shed.holeLine or
         (shed.holeCol > 0 and hole.holeLoc.col != shed.holeCol): continue
      let (goal, ctx, _) = shedGoalAndCtx(ms, hole)
      if goal != shed.goal or ctx != shed.ctx:
        return (false, "goal metadata does not match the checked state")
      # Hole indices are process-local elaboration data, so they are omitted
      # from Merkle nodes and reconstructed only after checking the source.
      state.sheds[shedIndex].holeIdx = holeIndex
      matched = true
      break
    if not matched:
      return (false, "goal '" & shed.name & "' is not present in its state source")
    let marker = sourceMarkerBounds(state.document, shed.nimLine, shed.nimCol, shed.name)
    if not marker.ok:
      return (false, marker.why)
  (true, "")

proc stateActionsForGoal(uri: string, state: ShedProofState, goalId: string):
    tuple[ok: bool, why: string, result: JsonNode] =
  let target = findStateShed(state, goalId)
  if not target.found: return (false, "unknown goal ID in this proof state", nil)
  if target.shed.status != ssYellow:
    return (false, "selected goal is not open", nil)
  let nimFile = uriToPath(uri)
  var actions = newJArray()
  actions.add(actionDescriptor("refine", "refine", "Refine with a term",
    "term", "eponym-term", nil, %*{"kind": "checker-determined"}))
  actions.add(actionDescriptor("give", "give", "Give a complete term",
    "term", "eponym-term", nil, %*{"kind": "complete-proof"}))

  var binderCount = max(0, target.shed.goalPi.len - 1)
  if binderCount == 0:
    try:
      let checked = elabCheckHolesDir(target.shed.genSrc, parentDir(nimFile))
      for hole in checked.ms.holes:
        if hole.holeLoc.line == target.shed.holeLine and
           (target.shed.holeCol <= 0 or hole.holeLoc.col == target.shed.holeCol):
          binderCount = semanticShedState(checked.ms, hole).goalPi.len
          break
    except ParseError: discard
  if binderCount > 0:
    var choices = newJArray()
    for count in 1 .. binderCount: choices.add(%count)
    actions.add(actionDescriptor("intro", "intro", "Introduce binders",
      "count", "positive-integer", choices, %*{"kind": "byChoice"}))

  var splitChoices = newJArray()
  for binding in target.shed.ctx:
    let separator = binding.find(" : ")
    if separator <= 0: continue
    let variable = binding[0 ..< separator]
    var generated = ""
    var after: seq[ShedInfo] = @[]
    let split = caseSplitShedDetailedPlan(nimFile, target.shed.name,
      variable, state.sheds, generated, after)
    if split.ok and split.subSheds.len > 0: splitChoices.add(%variable)
  if splitChoices.len > 0:
    actions.add(actionDescriptor("caseSplit", "caseSplit", "Case-split",
      "variable", "local-variable", splitChoices, %*{"kind": "branches"}))

  var ignored: seq[ShedInfo] = @[]
  let constructors = refineConstructorsShedPlan(nimFile, target.shed.name, "",
    state.sheds, "", ignored)
  if constructors.ok and constructors.constructors.len > 0:
    var choices = newJArray()
    for item in constructors.constructors: choices.add(%item)
    actions.add(actionDescriptor("construct", "construct", "Construct a value",
      "constructor", "feasible-constructor", choices, %*{"kind": "byChoice"}))
  let applications = refineFromContextShedPlan(nimFile, target.shed.name, "",
    state.sheds, "", ignored)
  if applications.ok and applications.candidates.len > 0:
    var choices = newJArray()
    for item in applications.candidates: choices.add(%item)
    actions.add(actionDescriptor("apply", "apply", "Apply a local hypothesis",
      "candidate", "feasible-application", choices, %*{"kind": "byChoice"}))
  let rewrites = refineEqualityShedPlan(nimFile, target.shed.name, "",
    state.sheds, "", ignored)
  if rewrites.ok and rewrites.candidates.len > 0:
    var choices = newJArray()
    for item in rewrites.candidates: choices.add(%item)
    actions.add(actionDescriptor("rewrite", "rewrite", "Rewrite using an equality",
      "rewrite", "checked-equality-rewrite", choices, %*{"kind": "one-residual-goal"}))
  (true, "", %*{"stateId": idText(state.id), "goalId": goalId,
                 "goal": target.shed.goal, "context": target.shed.ctx,
                 "actions": actions})

proc spliceDocumentState(state: ShedProofState, target: ShedInfo, term: string):
    tuple[ok: bool, why: string, document: string, rangeStart, rangeEnd: int] =
  let bounds = sourceMarkerBounds(state.document, target.nimLine,
                                  target.nimCol, target.name)
  if not bounds.ok: return (false, bounds.why, "", 0, 0)
  (true, "", state.document[0 ..< bounds.first] & term &
    state.document[bounds.after .. ^1], bounds.first, bounds.after)

proc handleStateNodes(server: var LspServer, params: JsonNode, root: NodeId):
    tuple[ok: bool, why: string, missing: seq[NodeId]] =
  try:
    if "nodes" in params:
      for nodeJson in params["nodes"]:
        let node = nodeFromJson(nodeJson)
        server.stateNodeCache.put(node.id, node.node)
    result.missing = server.stateNodeCache.missingClosure([root])
    result.ok = true
  except CatchableError as e:
    return (false, $e.name & ": " & e.msg, @[])

proc queryShedStateActions(server: var LspServer, uri, stateId, goalId: string,
                           nodeParams: JsonNode):
    tuple[ok: bool, why: string, result: JsonNode] =
  let root = NodeId(stateId)
  let imported = handleStateNodes(server, nodeParams, root)
  if not imported.ok: return (false, imported.why, nil)
  if imported.missing.len > 0:
    var missing = newJArray()
    for id in imported.missing: missing.add(%idText(id))
    return (true, "", %*{"needsNodes": missing, "stateId": stateId})
  var state: ShedProofState
  try: state = restoreShedProofState(server.stateNodeCache, root)
  except CatchableError as e: return (false, "invalid proof state: " & e.msg, nil)
  let validity = validateStateForQuery(uri, state)
  if not validity.ok: return (false, validity.why, nil)
  stateActionsForGoal(uri, state, goalId)

proc queryShedStateLayout(server: var LspServer, uri, stateId, goalId: string,
                          nodeParams: JsonNode):
    tuple[ok: bool, why: string, result: JsonNode] =
  let root = NodeId(stateId)
  let imported = handleStateNodes(server, nodeParams, root)
  if not imported.ok: return (false, imported.why, nil)
  if imported.missing.len > 0:
    var missing = newJArray()
    for id in imported.missing: missing.add(%idText(id))
    return (true, "", %*{"needsNodes": missing, "stateId": stateId})
  var state: ShedProofState
  try: state = restoreShedProofState(server.stateNodeCache, root)
  except CatchableError as e: return (false, "invalid proof state: " & e.msg, nil)
  let validity = validateStateForQuery(uri, state)
  if not validity.ok: return (false, validity.why, nil)
  let target = findStateShed(state, goalId)
  if not target.found: return (false, "unknown goal ID in this proof state", nil)
  (true, "", %*{"stateId": stateId, "goalId": goalId,
                 "name": target.shed.name,
                 "box": boxToJson(layoutShed(target.shed))})

proc bootstrapShedState(server: var LspServer, uri: string):
    tuple[ok: bool, why: string, result: JsonNode] =
  if uri notin server.documents:
    return (false, "unknown document; open it before initializing shed state", nil)
  let nimFile = uriToPath(uri)
  if not fileExists(nimFile): return (false, "document file does not exist", nil)
  if readFile(nimFile) != server.documents[uri]:
    return (false, "save or synchronize the Nim document before initializing shed state", nil)
  let sidecar = sidecarPath(nimFile)
  if not fileExists(sidecar): return (false, "no sheds sidecar; compile the document first", nil)
  let (sheds, _) = readShedSidecarEx(sidecar)
  let env = shedEnvironmentFingerprint(nimFile, sheds)
  let state = buildShedProofState(server.documents[uri], sheds, env, uri,
    initTable[string, string]())
  for (nodeId, node) in state.nodes: server.stateNodeCache.put(nodeId, node)
  var goals = newJArray()
  for shed in state.sheds:
    goals.add(%*{"goalId": state.goalIds[shed.name], "name": shed.name,
      "goal": shed.goal, "context": shed.ctx,
      "status": shedStatusToStr(shed.status),
      "nimLine": shed.nimLine, "nimCol": shed.nimCol})
  (true, "", %*{"stateId": idText(state.id), "nodes": nodesToJson(state.nodes),
                 "goals": goals, "environment": state.environment})

proc evaluateStateAction(server: var LspServer, uri, stateId, goalId,
                         actionId: string, arguments, nodeParams: JsonNode):
    tuple[ok: bool, why: string, result: JsonNode] =
  let root = NodeId(stateId)
  let imported = handleStateNodes(server, nodeParams, root)
  if not imported.ok: return (false, imported.why, nil)
  if imported.missing.len > 0:
    var missing = newJArray()
    for id in imported.missing: missing.add(%idText(id))
    return (true, "", %*{"needsNodes": missing, "stateId": stateId})
  var state: ShedProofState
  try: state = restoreShedProofState(server.stateNodeCache, root)
  except CatchableError as e: return (false, "invalid proof state: " & e.msg, nil)
  let validity = validateStateForQuery(uri, state)
  if not validity.ok: return (false, validity.why, nil)
  let available = stateActionsForGoal(uri, state, goalId)
  if not available.ok: return (false, available.why, nil)
  var descriptor: JsonNode
  for item in available.result["actions"]:
    if item["id"].getStr() == actionId: descriptor = item; break
  if descriptor.isNil: return (false, "action is not available for this state and goal", nil)
  if not argumentOffered(descriptor, arguments):
    return (false, "action arguments do not match the state affordance", nil)
  let target = findStateShed(state, goalId).shed
  let nimFile = uriToPath(uri)
  let kind = descriptor["kind"].getStr()
  var updated: seq[ShedInfo] = @[]
  var term = ""
  var nimLine = target.nimLine
  var nimCol = target.nimCol
  var status = "yellow"
  var yellowCount = 0
  var subSheds: seq[string] = @[]
  case kind
  of "refine", "give":
    let candidate = arguments["term"].getStr()
    let plan = refineShedPlan(nimFile, target.name, candidate, state.sheds,
      "", updated, requireComplete = kind == "give")
    if not plan.ok: return (false, plan.why, nil)
    term = plan.term; nimLine = plan.nimLine; nimCol = plan.nimCol
    status = plan.status; yellowCount = plan.yellowCount
  of "intro":
    let plan = introShedPlan(nimFile, target.name, arguments["count"].getInt(),
      state.sheds, "", updated)
    if not plan.ok: return (false, plan.why, nil)
    term = plan.term; nimLine = plan.nimLine; nimCol = plan.nimCol
    status = plan.status; yellowCount = plan.yellowCount
  of "construct":
    let plan = refineConstructorsShedPlan(nimFile, target.name,
      arguments["constructor"].getStr(), state.sheds, "", updated)
    if not plan.ok: return (false, plan.why, nil)
    term = plan.term; nimLine = plan.nimLine; nimCol = plan.nimCol
    status = plan.status; yellowCount = plan.yellowCount
  of "apply":
    let plan = refineFromContextShedPlan(nimFile, target.name,
      arguments["candidate"].getStr(), state.sheds, "", updated)
    if not plan.ok: return (false, plan.why, nil)
    term = plan.term; nimLine = plan.nimLine; nimCol = plan.nimCol
    status = plan.status; yellowCount = plan.yellowCount
  of "rewrite":
    let plan = refineEqualityShedPlan(nimFile, target.name,
      arguments["rewrite"].getStr(), state.sheds, "", updated)
    if not plan.ok: return (false, plan.why, nil)
    term = plan.term; nimLine = plan.nimLine; nimCol = plan.nimCol
    status = plan.status; yellowCount = plan.yellowCount
  of "caseSplit":
    var generated = ""
    let plan = caseSplitShedDetailedPlan(nimFile, target.name,
      arguments["variable"].getStr(), state.sheds, generated, updated)
    if not plan.ok: return (false, plan.why, nil)
    term = plan.term; nimLine = plan.nimLine; nimCol = plan.nimCol
    subSheds = plan.subSheds; status = "yellow"; yellowCount = subSheds.len
  else: return (false, "unknown shed action kind", nil)

  let splice = spliceDocumentState(state, target, term)
  if not splice.ok: return (false, splice.why, nil)
  let delta = term.len - (splice.rangeEnd - splice.rangeStart)
  for shed in updated.mitems:
    if shed.name == target.name: continue
    for oldShed in state.sheds:
      if oldShed.name != shed.name: continue
      let oldOffset = sourceOffset(state.document, oldShed.nimLine, oldShed.nimCol)
      if oldOffset >= splice.rangeEnd:
        let newPos = sourcePosition(splice.document, oldOffset + delta)
        shed.nimLine = newPos.line; shed.nimCol = newPos.col
      break
  var successors = buildShedProofState(splice.document, updated,
    shedEnvironmentFingerprint(nimFile, updated), uri, state.goalIds,
    stateId, kind, goalId)
  var changedNodes: seq[tuple[id: NodeId, node: MerkleNode]] = @[]
  for (id, node) in successors.nodes:
    if not server.stateNodeCache.contains(id): changedNodes.add((id, node))
    server.stateNodeCache.put(id, node)
  let transitionNode = transition(root, kind, goalId,
    stableActionArguments(arguments), successors.id, "eponym-checker-v1")
  let transitionId = nodeId(transitionNode)
  if not server.stateNodeCache.contains(transitionId):
    changedNodes.add((transitionId, transitionNode))
  server.stateNodeCache.put(transitionId, transitionNode)
  var goals = newJArray()
  for shed in successors.sheds:
    goals.add(%*{"goalId": successors.goalIds[shed.name], "name": shed.name,
      "goal": shed.goal, "context": shed.ctx,
      "status": shedStatusToStr(shed.status),
      "nimLine": shed.nimLine, "nimCol": shed.nimCol})
  (true, "", %*{"stateId": stateId, "goalId": goalId,
    "successorStateId": idText(successors.id),
    "transitionId": idText(transitionId), "nodes": nodesToJson(changedNodes),
    "edit": {"term": term, "nimLine": nimLine, "nimCol": nimCol},
    "documentText": splice.document, "goals": goals,
    "validation": {"accepted": true, "status": status,
                   "yellowCount": yellowCount}, "subSheds": subSheds})


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
    bumpDocumentRevision(server, uri)
    invalidateShedActionVersions(server, uri)
    return publishDiagnostics(server, uri)
  of "textDocument/didChange":
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let text = msg["params"]["contentChanges"][0]["text"].getStr()
    server.documents[uri] = text
    bumpDocumentRevision(server, uri)
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
  of "eponym/createShedState":
    let id = msg["id"]
    if "textDocument" notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
        "error": {"code": -32602, "message": "createShedState needs textDocument.uri"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let state = bootstrapShedState(server, uri)
    if not state.ok:
      return %*{"jsonrpc": "2.0", "id": id,
        "error": {"code": -32602, "message": state.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": state.result}
  of "eponym/queryShedStateActions":
    let id = msg["id"]
    let params = msg["params"]
    for key in ["textDocument", "stateId", "goalId"]:
      if key notin params:
        return %*{"jsonrpc": "2.0", "id": id,
          "error": {"code": -32602, "message": "queryShedStateActions needs textDocument, stateId, and goalId"}}
    let nodes = if "nodes" in params: params else: newJObject()
    let r = queryShedStateActions(server,
      params["textDocument"]["uri"].getStr(), params["stateId"].getStr(),
      params["goalId"].getStr(), nodes)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
        "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/transitionShedState":
    let id = msg["id"]
    let params = msg["params"]
    for key in ["textDocument", "stateId", "goalId", "action"]:
      if key notin params:
        return %*{"jsonrpc": "2.0", "id": id,
          "error": {"code": -32602, "message": "transitionShedState needs textDocument, stateId, goalId, and action"}}
    let action = params["action"]
    if "id" notin action or "arguments" notin action:
      return %*{"jsonrpc": "2.0", "id": id,
        "error": {"code": -32602, "message": "action needs id and arguments"}}
    let nodes = if "nodes" in params: params else: newJObject()
    let r = evaluateStateAction(server,
      params["textDocument"]["uri"].getStr(), params["stateId"].getStr(),
      params["goalId"].getStr(), action["id"].getStr(), action["arguments"], nodes)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
        "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/shedStateLayout":
    let id = msg["id"]
    let params = msg["params"]
    for key in ["textDocument", "stateId", "goalId"]:
      if key notin params:
        return %*{"jsonrpc": "2.0", "id": id,
          "error": {"code": -32602, "message": "shedStateLayout needs textDocument, stateId, and goalId"}}
    let nodes = if "nodes" in params: params else: newJObject()
    let r = queryShedStateLayout(server,
      params["textDocument"]["uri"].getStr(), params["stateId"].getStr(),
      params["goalId"].getStr(), nodes)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
        "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/availableShedActions":
    let id = msg["id"]
    let params = msg["params"]
    if "textDocument" notin params or "shedName" notin params:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "availableShedActions needs textDocument.uri and shedName"}}
    let uri = params["textDocument"]["uri"].getStr()
    let r = availableShedActions(server, uri, params["shedName"].getStr())
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/submitShedAction":
    let id = msg["id"]
    let params = msg["params"]
    if "textDocument" notin params or "shedName" notin params or
       "stateVersion" notin params or "action" notin params or
       "id" notin params["action"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "submitShedAction needs textDocument.uri, shedName, stateVersion, and action.id"}}
    let uri = params["textDocument"]["uri"].getStr()
    let action = params["action"]
    let arguments = if "arguments" in action: action["arguments"] else: newJObject()
    let r = submitShedAction(server, uri, params["shedName"].getStr(),
      params["stateVersion"].getInt(), action["id"].getStr(), arguments)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/performShedAction":
    let id = msg["id"]
    let params = msg["params"]
    if "textDocument" notin params or "action" notin params or
       "kind" notin params["action"] or "target" notin params["action"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "performShedAction needs textDocument.uri and action.kind/target"}}
    let uri = params["textDocument"]["uri"].getStr()
    let action = params["action"]
    let arguments = if "arguments" in action: action["arguments"] else: newJObject()
    let term = if "term" in arguments: arguments["term"].getStr() else: ""
    let variable = if "variable" in arguments:
                     arguments["variable"].getStr()
                   else: ""
    let requireComplete = "requireComplete" in arguments and
      arguments["requireComplete"].getBool()
    let r = prepareShedAction(server, uri, action["target"].getStr(),
      action["kind"].getStr(), term, variable, requireComplete)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/commitShedAction":
    let id = msg["id"]
    let params = msg["params"]
    if "textDocument" notin params or "transitionId" notin params:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "commitShedAction needs textDocument.uri and transitionId"}}
    let r = commitShedAction(server,
      params["textDocument"]["uri"].getStr(), params["transitionId"].getInt())
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/shedActionHistory":
    let id = msg["id"]
    if "textDocument" notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "shedActionHistory needs textDocument.uri"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    return %*{"jsonrpc": "2.0", "id": id,
              "result": inspectShedActionHistory(server, uri)}
  of "eponym/undoShedAction":
    let id = msg["id"]
    if "textDocument"notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "undoShedAction needs textDocument.uri"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let r = prepareUndoShedAction(server, uri)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/redoShedAction":
    let id = msg["id"]
    if "textDocument"notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "redoShedAction needs textDocument.uri"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let r = performRedoShedAction(server, uri)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
  of "eponym/commitShedHistoryMove":
    let id = msg["id"]
    let params = msg["params"]
    if "textDocument"notin params or "transitionId"notin params or
       "direction" notin params:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "commitShedHistoryMove needs textDocument.uri, transitionId and direction"}}
    let r = commitShedHistoryMove(server,
      params["textDocument"]["uri"].getStr(), params["transitionId"].getInt(),
      params["direction"].getStr())
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id, "result": r.result}
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
  of "eponym/introShed":
    let id = msg["id"]
    if "textDocument" notin msg["params"] or "shedName" notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "eponym/introShed needs " &
                            "textDocument.uri and shedName"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let shedName = msg["params"]["shedName"].getStr()
    let count = if "count" in msg["params"]:
                  msg["params"]["count"].getInt()
                else: 1
    let r = introShed(uriToPath(uri), shedName, count)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    return %*{"jsonrpc": "2.0", "id": id,
              "result": {"shedName": shedName, "term": r.term,
                         "nimLine": r.nimLine, "nimCol": r.nimCol,
                         "status": r.status, "yellowCount": r.yellowCount}}
  of "eponym/refineConstructorsShed":
    let id = msg["id"]
    if "textDocument" notin msg["params"] or "shedName" notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "eponym/refineConstructorsShed needs " &
                            "textDocument.uri and shedName"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let shedName = msg["params"]["shedName"].getStr()
    let selected = if "constructor" in msg["params"]:
                     msg["params"]["constructor"].getStr()
                   else: ""
    let r = refineConstructorsShed(uriToPath(uri), shedName, selected)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    var payload = %*{"shedName": shedName, "constructors": r.constructors,
                     "term": r.term, "nimLine": r.nimLine, "nimCol": r.nimCol,
                     "status": r.status, "yellowCount": r.yellowCount}
    if r.why != "": payload["message"] = %r.why
    return %*{"jsonrpc": "2.0", "id": id, "result": payload}
  of "eponym/refineFromContextShed":
    let id = msg["id"]
    if "textDocument" notin msg["params"] or "shedName" notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "eponym/refineFromContextShed needs " &
                            "textDocument.uri and shedName"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let shedName = msg["params"]["shedName"].getStr()
    let selected = if "candidate" in msg["params"]:
                     msg["params"]["candidate"].getStr()
                   else: ""
    let r = refineFromContextShed(uriToPath(uri), shedName, selected)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    var payload = %*{"shedName": shedName, "candidates": r.candidates,
                     "term": r.term, "nimLine": r.nimLine, "nimCol": r.nimCol,
                     "status": r.status, "yellowCount": r.yellowCount}
    if r.why != "": payload["message"] = %r.why
    return %*{"jsonrpc": "2.0", "id": id, "result": payload}
  of "eponym/refineEqualityShed":
    let id = msg["id"]
    if "textDocument" notin msg["params"] or "shedName" notin msg["params"]:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602,
                          "message": "eponym/refineEqualityShed needs " &
                            "textDocument.uri and shedName"}}
    let uri = msg["params"]["textDocument"]["uri"].getStr()
    let shedName = msg["params"]["shedName"].getStr()
    let selected = if "rewrite" in msg["params"]:
                     msg["params"]["rewrite"].getStr()
                   else: ""
    let r = refineEqualityShed(uriToPath(uri), shedName, selected)
    if not r.ok:
      return %*{"jsonrpc": "2.0", "id": id,
                "error": {"code": -32602, "message": r.why}}
    var payload = %*{"shedName": shedName, "candidates": r.candidates,
                     "term": r.term, "nimLine": r.nimLine, "nimCol": r.nimCol,
                     "status": r.status, "yellowCount": r.yellowCount}
    if r.why != "": payload["message"] = %r.why
    return %*{"jsonrpc": "2.0", "id": id, "result": payload}
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
  var server = LspServer(documents: initTable[string, string](),
    stateNodeCache: initNodeCache(MaxShedStateNodes))
  while true:
    let msg = readMessage()
    if msg.isNil:
      break
    let resp = handleMessage(server, msg)
    if not resp.isNil:
      writeMessage(resp)
    if not msg.isNil and "method" in msg and msg["method"].getStr() == "exit":
      quit(0)
