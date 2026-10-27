# sheds.nim -- Shed metadata for the sheds line (issues #133-#137).
#
# Issue #134: each shed carries an elaboration *status* following Epigram's
# colour scheme (McBride 2005 §1.5) -- white (elaborated successfully),
# yellow (stuck: open holes, constraints not yet solvable but possibly
# later), brown (definitely bad: elaboration failed before a goal was
# established). The status is computed by `assignShedStatuses` (shared by
# the shedsBlock macro at macro time and by `refreshShedStatuses` for the
# LSP/editor loop, e.g. after holes are filled via the #58 refine/give
# actions) and serialized in the sidecar JSON, which the LSP server
# (lsp.nim) turns into diagnostics: yellow -> Warning, brown -> Error,
# white -> no diagnostic. The LSP re-reads the sidecar on every
# textDocument/didOpen and didChange, so status updates as the Nim
# compiler re-runs the macro (and, in the #137 loop, as holes are filled).
#
# A *shed* is an Epigram-style unchecked region: "the typechecker is
# forbidden to tread" there (Altenkirch, McBride & McKinna 2005). In the
# linearized Nim-friendly syntax accepted by the shedsBlock macro
# (sheds_mac.nim), a shed is written:
#
#   proc plus(x: Nat, y: Nat): Nat = ![ plusBody ]            # named shed
#   proc quad(n: Nat): Nat = ![ quadBody, double (double n) ] # with draft
#   proc id(A: Univ): A = lam(x: A) => shedHole(inner)         # nested shed
#
# (A proc whose body is a shed *is* the Epigram shape: the declaration
# exists with its type, and the shed is the incomplete right-hand side --
# selecting it shows what's in scope and what must be built. A shed marker
# at top level, outside any proc body, is an error.)
# source
# (reusing the #58 hole infrastructure) and records where the shed sits:
# its Nim source line/col (for editor/LSP targeting) and the generated-
# source line of its hole (for matching against MetaStore.holes after
# hole-tolerant elaboration). The metadata is written to a sidecar JSON
# file `<nimfile>.sheds.json` next to the calling Nim file; the LSP server
# (issues #134 status, #135 layout) reads it via readShedSidecar.
#
# Note on the draft: inside a Nim macro block the draft must be valid Nim
# syntax (whatever it means) -- it is captured with `repr` as user-owned
# scratch text and never reaches the elaborator. The true Epigram document
# syntax (`![...]!` regions) lives on the LSP/webview side (#136); the
# macro receives the linearized form.

import macros  # NimNode, lineInfo, repr (macro-side rewriting)
import json
import os
import strutils
import sequtils
import elab  # elabCheckHolesDir (issue #134: refreshShedStatuses)
import parse_surf  # ParseError (issue #134: refreshShedStatuses)
import eponym_init  # Term, Quantity (issue #377: semantic shed state)
import unify  # MetaStore, HoleInfo, zonk (issue #377)
import preterm  # Qty / toQty

type
  ShedSemanticBinder* = object
    ## A binder in the in-process semantic snapshot. `ty` is zonked in the
    ## hole's context; `qty` preserves the elaborator's quantity annotation.
    name*: string
    ty*: Term
    qty*: Qty

  ShedPiBinder* = object
    ## One binder in the Pi spine of a hole goal, with its domain as a Term
    ## rather than the old rendered "name : type" string.
    name*: string
    domain*: Term
    qty*: Quantity
    implicit*: bool
    erased*: bool

  ShedSemanticState* = object
    ## Transient, elaborator-backed view of a shed hole. The `hole` term is
    ## the typed metavariable and its spine; goal/context terms are zonked
    ## against the supplied MetaStore. Do not persist these Term refs without
    ## also serializing a stable term algebra and metavariable environment.
    hole*: Term  # original typed metavariable reference and its context spine
    goal*: Term
    context*: seq[ShedSemanticBinder]  # innermost-first
    goalPi*: seq[ShedPiBinder]         # outermost-first
    residualGoal*: Term

proc semanticShedState*(ms: MetaStore, h: HoleInfo): ShedSemanticState =
  ## Build the editor's semantic view from a live elaboration result. This is
  ## the source for LSP behavior; strings in ShedInfo/sidecars are projections
  ## for display and backward-compatible cross-process transport.
  result.hole = h.holeTerm
  result.goal = zonk(ms, h.holeGoal)
  for b in h.holeCtx:
    result.context.add(ShedSemanticBinder(name: b.name,
      ty: zonk(ms, b.ty), qty: b.qty))

  var g = result.goal
  while g.kind == tPi:
    let nm = g.scope.adv
    let dom = zonk(ms, g.dom)
    result.goalPi.add(ShedPiBinder(name: nm, domain: dom, qty: g.qty,
      implicit: g.impl, erased: g.erased))
    g = zonk(ms, g.scope.bdy)
  result.residualGoal = g

proc semanticContext*(state: ShedSemanticState): Ctx =
  ## Adapt the structured context for the existing name-aware term printer.
  for b in state.context:
    result.add(CtxEntry(name: b.name, ty: b.ty, qty: b.qty))

proc renderShedGoalCtx*(ms: MetaStore, state: ShedSemanticState):
    tuple[goal: string, ctx: seq[string], goalPi: seq[string]] =
  ## Legacy text projection used by the sidecar and current 2D layout.
  let ctx = semanticContext(state)
  result.goal = prettyTerm(state.goal, ctx, ms.refNames, ms.recordFields)
  for b in state.context:
    result.ctx.add(b.name & " : " & prettyTerm(b.ty, ctx,
      ms.refNames, ms.recordFields))
  var pc = ctx
  for b in state.goalPi:
    result.goalPi.add(b.name & " : " & prettyTerm(b.domain, pc,
      ms.refNames, ms.recordFields))
    pc = @[CtxEntry(name: b.name, ty: b.domain, qty: toQty(b.qty))] & pc
  if state.goalPi.len > 0:
    result.goalPi.add(prettyTerm(state.residualGoal, pc,
      ms.refNames, ms.recordFields))

proc renderShedHover*(ms: MetaStore, state: ShedSemanticState): string =
  ## LSP hover projection. Keeping this over the semantic state prevents a
  ## second, subtly different interpretation of hole contexts and goals.
  let ctx = semanticContext(state)
  var lines: seq[string] = @[
    "```",
    "goal : " & prettyTerm(state.goal, ctx, ms.refNames, ms.recordFields),
    "```"]
  if state.context.len > 0:
    lines.add("**context**")
    for b in state.context:
      lines.add("- `" & b.name & " : " &
        prettyTerm(b.ty, ctx, ms.refNames, ms.recordFields) & "`")
  lines.join("\n")

type
  ShedStatus* = enum
    ## Epigram's status colours (McBride 2005 §1.5), tracked per shed.
    ssWhite   ## elaborated successfully: no open holes, no errors
    ssYellow  ## stuck: open hole(s); constraints not yet solvable, possibly later
    ssBrown   ## definitely bad: elaboration failed before a goal was established

  ShedInfo* = object
    ## Metadata for one shed (see module doc).
    name*: string      # shed name, from `![ name ... ]`
    draft*: string     # user-owned scratch text (`repr` of the draft node);
                       # the elaborator never sees this
    nimLine*: int      # 1-based line of `![...]` in the calling Nim file
    nimCol*: int       # 1-based column of `![...]` in the calling Nim file
    holeLine*: int     # 1-based line of the `?` in the generated Eponym source
    holeIdx*: int      # index into MetaStore.holes after elaboration
                       # (-1 = not matched)
    holeCol*: int      # 1-based column of the `?` in the generated source
                       # (0 = unknown; re-matched by refreshShedStatuses)
    genSrc*: string     # issue #137: the block's generated Eponym source at
                       # macro time, so the LSP server can run the #58
                       # refine action for real `.nim` documents
                       # ("" = sidecar predates #137: recompile)
    goal*: string      # display projection; semantic state owns Term
    ctx*: seq[string]  # display projection ("name : type")
    goalPi*: seq[string]  # issue #192: Pi spine of the goal, outermost first:
                          # binder strings and residual goal, projected from
                          # ShedSemanticState for the sidecar/layout
    status*: ShedStatus  # issue #134: white/yellow/brown elaboration status

proc isShedNode*(n: NimNode): bool =
  ## `![ ... ]`: prefix `!` applied to a bracket.
  n.kind == nnkPrefix and n.len == 2 and
    n[0].kind == nnkIdent and $n[0] == "!" and
    n[1].kind == nnkBracket

proc isShedHoleCall*(n: NimNode): bool =
  ## `shedHole(name)`: call-form marker for a residual shed nested in
  ## Nim command syntax, where the prefix form `![name]` cannot parse.
  ## Inside `lam(x: T) => ...`, Nim attaches the binder to the call head and
  ## parses this as `Call(DotExpr(x, shedHole), name)`.
  if n.kind != nnkCall or n.len != 2 or n[1].kind != nnkIdent:
    return false
  (n[0].kind == nnkIdent and $n[0] == "shedHole") or
    (n[0].kind == nnkDotExpr and n[0].len == 2 and
     n[0][1].kind == nnkIdent and $n[0][1] == "shedHole")

proc parseShedParts*(n: NimNode): tuple[name: string, draft: NimNode,
                                       hasDraft: bool] =
  ## Split `![ name ]` / `![ name, draft ]`. Errors with a helpful message
  ## on any other shape. (Comma, not `|`, separates name from draft: `|`
  ## binds tighter than `+` in Nim, so `![ n | a + a ]` would misparse.)
  assert isShedNode(n), "parseShedParts on non-shed node"
  let br = n[1]
  if br.len == 1 and br[0].kind == nnkIdent:
    return ($br[0], nil, false)
  if br.len == 2 and br[0].kind == nnkIdent:
    return ($br[0], br[1], true)
  error("shedsBlock: shed expects `![ name ]` or `![ name, draft ]` " &
    "(name first, optional draft after a comma)", n)

proc shedPlaceholder*(i: int): string =
  ## Stand-in ident emitted for shed `i` during Nim->Eponym conversion;
  ## resolveShedPlaceholders replaces it with `_` before parsing.
  "__eponym_shed_" & $i & "__"

proc parseLineInfo*(li: string): tuple[line, col: int] =
  ## `lineInfo` has the form `/abs/path/file.nim(line, col)`; Nim's line
  ## is 1-based but its column is 0-based. Sidecar/LSP positions are
  ## 1-based for both, so normalize the column here.
  let p = li.rfind('(')
  doAssert p >= 0, "cannot parse lineInfo: " & li
  let inner = li[p + 1 .. ^2]  # drop "(" ... ")"
  let parts = inner.split(',')
  (parseInt(parts[0].strip()), parseInt(parts[1].strip()) + 1)

proc callerFileOf*(body: NimNode): string =
  ## Absolute path of the Nim file containing the macro call.
  let li = lineInfo(body)
  let p = li.rfind('(')
  if p < 0:
    error("shedsBlock: cannot determine calling file", body)
  li[0 ..< p]

proc rewriteSheds*(body: NimNode, sheds: var seq[ShedInfo]) =
  ## In-place rewrite of the macro argument: every `![...]` or
  ## `shedHole(name)` marker becomes a
  ## placeholder ident (`shedPlaceholder i`), and `sheds` accumulates the
  ## metadata. Shed contents are never descended into -- the typechecker
  ## is forbidden to tread there, and neither is the converter.
  ##
  ## A shed marker at top level (outside any proc body) is an error: write a
  ## proc whose body is the shed instead -- that is the Epigram shape
  ## (declaration with its type; the shed is the incomplete RHS).
  if body.kind == nnkStmtList:
    for i in 0 ..< body.len:
      if isShedNode(body[i]) or isShedHoleCall(body[i]):
        error("shedsBlock: a shed must sit inside a proc body, e.g. " &
          "proc plus(x: Nat, y: Nat): Nat = ![ plusBody ] -- " &
          "a bare top-level ![...] has no expected type to check against.", body[i])
  proc walk(n: NimNode, acc: var seq[ShedInfo]) =
    for i in 0 ..< n.len:
      let c = n[i]
      if isShedNode(c) or isShedHoleCall(c):
        var name: string
        var draft: NimNode
        var hasDraft = false
        var markerLoc = c
        var replacement: NimNode
        if isShedNode(c):
          (name, draft, hasDraft) = parseShedParts(c)
          replacement = ident(shedPlaceholder(acc.len))
        else:
          name = $c[1]
          if c[0].kind == nnkDotExpr:
            markerLoc = c[0][1]
            replacement = newNimNode(nnkDotExpr)
            replacement.add(c[0][0])
            replacement.add(ident(shedPlaceholder(acc.len)))
          else:
            markerLoc = c[0]
            replacement = ident(shedPlaceholder(acc.len))
        let (ln, co) = parseLineInfo(lineInfo(markerLoc))
        acc.add(ShedInfo(name: name,
                         draft: if hasDraft: repr(draft) else: "",
                         nimLine: ln, nimCol: co,
                         holeLine: 0, holeIdx: -1,
                         status: ssYellow))  # issue #134: not yet elaborated
        copyLineInfo(replacement, c)
        n[i] = replacement
      else:
        walk(c, acc)
  walk(body, sheds)

proc resolveShedPlaceholders*(src: var string, sheds: var seq[ShedInfo]) =
  ## Replace each placeholder with `_` (a #58 hole), recording the
  ## 1-based generated-source line *and column* so the macro can match
  ## sheds to MetaStore.holes after elaboration (and so issue #137's
  ## `eponym/refineShed` can target the hole exactly).
  for i in 0 ..< sheds.len:
    let ph = shedPlaceholder(i)
    let pos = src.find(ph)
    if pos < 0:
      raise newException(ValueError, "shed '" & sheds[i].name &
        "': placeholder vanished during conversion (internal error)")
    var line = 1
    var lineStart = -1
    for k in 0 ..< pos:
      if src[k] == '\n':
        inc line
        lineStart = k
    sheds[i].holeLine = line
    sheds[i].holeCol = pos - lineStart  # 1-based column of the `_`
    src = src[0 ..< pos] & "_" & src[pos + ph.len .. ^1]

# --- sidecar JSON: the bridge to the LSP server (issues #134/#135) --------

proc shedStatusToStr*(s: ShedStatus): string =
  ## Issue #134: readable status in the sidecar (debuggable by hand).
  case s
  of ssWhite: "white"
  of ssYellow: "yellow"
  of ssBrown: "brown"

proc shedStatusFromStr*(s: string): ShedStatus =
  ## Unknown or missing strings map to yellow (stuck) -- the safe state:
  ## a shed whose status we cannot establish is not known-good.
  case s
  of "white": ssWhite
  of "brown": ssBrown
  else: ssYellow

proc shedToJson*(s: ShedInfo): JsonNode =
  %*{"name": s.name, "draft": s.draft,
      "nimLine": s.nimLine, "nimCol": s.nimCol,
      "holeLine": s.holeLine, "holeIdx": s.holeIdx, "holeCol": s.holeCol,
      "genSrc": s.genSrc,
      "goal": s.goal, "ctx": s.ctx,
      "goalPi": s.goalPi,
      "status": shedStatusToStr(s.status)}

proc shedFromJson*(j: JsonNode): ShedInfo =
  ShedInfo(name: j["name"].getStr, draft: j["draft"].getStr,
           nimLine: j["nimLine"].getInt, nimCol: j["nimCol"].getInt,
           holeLine: j["holeLine"].getInt, holeIdx: j["holeIdx"].getInt,
           holeCol: if j.hasKey("holeCol"): j["holeCol"].getInt else: 0,
           genSrc: if j.hasKey("genSrc"): j["genSrc"].getStr else: "",
           goal: j["goal"].getStr,
           ctx: j["ctx"].elems.mapIt(it.getStr),
           goalPi: if j.hasKey("goalPi"): j["goalPi"].elems.mapIt(it.getStr)
                   else: @[],  # pre-#192 sidecars: flat hole box as before
           status: if j.hasKey("status"): shedStatusFromStr(j["status"].getStr)
                   else: ssYellow)  # pre-#134 sidecars: stuck is the safe default

proc shedsToJson*(sheds: seq[ShedInfo]): JsonNode =
  result = newJArray()
  for s in sheds: result.add(shedToJson(s))

proc shedsFromJson*(j: JsonNode): seq[ShedInfo] =
  for e in j.elems: result.add(shedFromJson(e))

proc sidecarPath*(nimFile: string): string =
  ## `<dir>/<base>.sheds.json` -- the metadata file the LSP server reads.
  let (dir, base, _) = splitFile(nimFile)
  dir / (base & ".sheds.json")

# --- per-compilation sidecar reset (issue #221 follow-up) -------------------
# The sidecar must reflect EXACTLY the sheds in the current compilation.
# The old unconditional read-merge-write kept stale entries -- sheds
# deleted or renamed in the source lingered as ghosts (e.g. a case-split's
# `isZeroBody_zero` surviving after the source went back to `isZeroBody`,
# or suffixed duplicates like `isZeroBody_zero1`).
#
# Reset rule: the first `shedsBlock` expansion for a given file in a
# compilation starts fresh, ignoring any stale sidecar on disk; later
# expansions for the same file in the SAME compilation merge by name.
# Tracked in a {.compileTime.} var: it persists across macro expansions
# within one `nim c` and resets on every fresh compiler invocation.
# No file mtimes are consulted: `stat`/`getLastModificationTime` cannot
# run in the Nim VM at macro-expansion time (regression: it crashed every
# `nim c` of a sheds file once a sidecar existed).
#
# Multiple `shedsBlock` expansions in one file still accumulate within a
# compilation; each fresh `nim c` after an edit starts clean.

var sidecarResetDone {.compileTime.}: seq[string] = @[]

proc writeShedSidecar*(nimFile: string, sheds: seq[ShedInfo],
                       errMsg = "") =
  ## Write the sidecar for the LSP server (see reset rule above).
  ## `errMsg` (issue #134): the elaboration failure, if any, so the LSP
  ## server can show *why* a brown shed is brown.
  let path = sidecarPath(nimFile)
  var old: seq[ShedInfo] = @[]
  if path in sidecarResetDone:
    # Later shedsBlock expansion for this file in the same compilation:
    # merge with what earlier expansions wrote.
    try:
      let j = parseJson(readFile(path))
      if j.hasKey("sheds"):
        old = shedsFromJson(j["sheds"])
    except JsonParsingError, IOError:
      discard
  else:
    # First expansion for this file in this compilation: reset, ignoring
    # any stale sidecar left behind by a previous compilation.
    sidecarResetDone.add(path)
  # Merge by name: current sheds replace same-name old entries; old
  # entries for sheds no longer in the source are dropped on reset.
  let here = sheds.mapIt(it.name)
  var merged: seq[ShedInfo] = @[]
  for s in old:
    if s.name notin here:
      merged.add(s)
  for s in sheds:
    var replaced = false
    for i in 0 ..< merged.len:
      if merged[i].name == s.name:
        merged[i] = s
        replaced = true
        break
    if not replaced:
      merged.add(s)
  writeFile(path, pretty(%*{"file": nimFile, "errMsg": errMsg,
                            "sheds": shedsToJson(merged)}))

proc readShedSidecarEx*(path: string): tuple[sheds: seq[ShedInfo], errMsg: string] =
  ## Read a sidecar file plus the document-level elaboration failure
  ## ("" when the last compile succeeded). LSP server side, issue #134.
  let j = parseJson(readFile(path))
  let errMsg = if j.hasKey("errMsg"): j["errMsg"].getStr else: ""
  (shedsFromJson(j["sheds"]), errMsg)

proc readShedSidecar*(path: string): seq[ShedInfo] =
  ## Read a sidecar file (LSP server side, issues #134/#135).
  readShedSidecarEx(path).sheds

# --- issue #134: shed status tracking (white/yellow/brown) ----------------

proc assignShedStatuses*(sheds: var seq[ShedInfo], errMsg: string,
                         onlyGenSrc = "") =
  ## The #134 status rule, shared by the shedsBlock macro (macro-time) and
  ## refreshShedStatuses (LSP/editor-loop time). `holeIdx >= 0` means the
  ## shed was matched to an open hole in MetaStore.holes:
  ## - matched to an open hole -> yellow (stuck, possibly solvable later);
  ## - no goal after a failed elaboration -> brown (definitely bad: the
  ##   shed's own declaration never elaborated, so refinement cannot help
  ##   until the surrounding code is fixed);
  ## - no open hole after a clean elaboration -> white (done).
  ## `onlyGenSrc` (issue #137): when non-empty, only sheds whose recorded
  ## generated source equals it are re-assigned -- a sidecar can hold
  ## sheds from several shedsBlock expansions, and re-elaborating one
  ## block's source must not touch another block's sheds.
  for i in 0 ..< sheds.len:
    if onlyGenSrc != "" and sheds[i].genSrc != onlyGenSrc: continue
    if sheds[i].holeIdx >= 0:
      sheds[i].status = ssYellow
    elif errMsg != "":
      sheds[i].status = ssBrown
    else:
      sheds[i].status = ssWhite

proc refreshShedStatuses*(sheds: var seq[ShedInfo], genSrc: string,
                         baseDir: string, onlyGenSrc = "") =
  ## Recompute per-shed status from the (possibly edited) generated Eponym
  ## source -- the #137 editor loop, headless: after holes are filled via
  ## the #58 refine/give actions, re-elaborate hole-tolerantly, re-match
  ## sheds to holes by generated-source line and column, and re-apply the status
  ## rule. A document that no longer parses marks every shed brown.
  ## `onlyGenSrc` (issue #137): restrict re-matching to sheds belonging
  ## to the elaborated block (see assignShedStatuses); other sheds keep
  ## their status, holeIdx, and holeCol untouched.
  ## The #137 `eponym/refineShed` adjusts generated-source positions before
  ## calling here, so multiple holes on one line remain distinct.
  var errMsg = ""
  var holesOk = false
  try:
    let r = elabCheckHolesDir(genSrc, baseDir)
    errMsg = r.errMsg
    for i in 0 ..< sheds.len:
      if onlyGenSrc != "" and sheds[i].genSrc != onlyGenSrc: continue
      sheds[i].holeIdx = -1
      for j in 0 ..< r.ms.holes.len:
        if r.ms.holes[j].holeLoc.line != sheds[i].holeLine: continue
        if sheds[i].holeCol > 0:
          if r.ms.holes[j].holeLoc.col == sheds[i].holeCol:
            sheds[i].holeIdx = j
            break
        elif sheds[i].holeIdx < 0:
          sheds[i].holeIdx = j  # legacy sidecar has no recorded column
      if sheds[i].holeIdx >= 0:
        sheds[i].holeCol = r.ms.holes[sheds[i].holeIdx].holeLoc.col
    holesOk = true
  except ParseError:
    discard
  if not holesOk:
    for i in 0 ..< sheds.len:
      if onlyGenSrc != "" and sheds[i].genSrc != onlyGenSrc: continue
      sheds[i].status = ssBrown
    return
  assignShedStatuses(sheds, errMsg, onlyGenSrc)

macro runShedSmoke(): untyped =
  ## Compile-time smoke test: shed rewriting + placeholder resolution
  ## (quote needs a compile-time context).
  var sheds: seq[ShedInfo] = @[]
  let blk = quote do:
    proc plus(x: int, y: int): int = ![ plusBody ]
    proc quad(n: int): int = ![ quadBody, n + n ]
  rewriteSheds(blk, sheds)
  doAssert sheds.len == 2
  doAssert sheds[0].name == "plusBody" and sheds[0].draft == ""
  doAssert sheds[1].name == "quadBody" and sheds[1].draft.len > 0
  doAssert sheds[0].nimLine > 0 and sheds[0].nimCol > 0
  var src = "proc plus (x : int) (y : int) : int = " & shedPlaceholder(0) & "\n" &
            "proc quad (n : int) : int = " & shedPlaceholder(1) & "\n"
  resolveShedPlaceholders(src, sheds)
  doAssert sheds[0].holeLine == 1 and sheds[1].holeLine == 2
  doAssert "__eponym_shed_" notin src
  # JSON round-trip (the sidecar format the LSP server reads)
  let rt = shedsFromJson(shedsToJson(sheds))
  doAssert rt.len == 2 and rt[1].name == "quadBody" and rt[1].holeLine == 2
  quote do:
    echo "ok: sheds rewrite/resolve smoke test"

when isMainModule:
  runShedSmoke()
