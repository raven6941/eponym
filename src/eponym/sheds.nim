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
#   proc plus(x: Nat, y: Nat): Nat = ![ plusBody ]          # named shed
#   proc quad(n: Nat): Nat = ![ quadBody, double (double n) ] # with draft
#
# (A proc whose body is a shed *is* the Epigram shape: the declaration
# exists with its type, and the shed is the incomplete right-hand side --
# selecting it shows what's in scope and what must be built. A `![...]`
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
import times  # Time comparison for the sidecar reset rule
import strutils
import sequtils
import elab  # elabCheckHolesDir (issue #134: refreshShedStatuses)
import parse_surf  # ParseError (issue #134: refreshShedStatuses)

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
    holeLine*: int     # 1-based line of the `_` in the generated Eponym source
    holeIdx*: int      # index into MetaStore.holes after elaboration
                       # (-1 = not matched)
    holeCol*: int      # 1-based column of the `_` in the generated source
                       # (0 = unknown; re-matched by refreshShedStatuses)
    genSrc*: string     # issue #137: the block's generated Eponym source at
                       # macro time, so the LSP server can run the #58
                       # refine action for real `.nim` documents
                       # ("" = sidecar predates #137: recompile)
    goal*: string      # zonked, pretty-printed goal type at the hole
    ctx*: seq[string]  # zonked, pretty-printed binder context ("name : type")
    goalPi*: seq[string]  # issue #192: Pi spine of the goal, outermost first:
                          # binder strings ("f : A"), then the residual goal
                          # as the last element (empty = goal is not a Pi, the
                          # layout renders one flat hole box as before)
    status*: ShedStatus  # issue #134: white/yellow/brown elaboration status

proc isShedNode*(n: NimNode): bool =
  ## `![ ... ]`: prefix `!` applied to a bracket.
  n.kind == nnkPrefix and n.len == 2 and
    n[0].kind == nnkIdent and $n[0] == "!" and
    n[1].kind == nnkBracket

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
  ## `lineInfo` has the form `/abs/path/file.nim(line, col)`.
  let p = li.rfind('(')
  doAssert p >= 0, "cannot parse lineInfo: " & li
  let inner = li[p + 1 .. ^2]  # drop "(" ... ")"
  let parts = inner.split(',')
  (parseInt(parts[0].strip()), parseInt(parts[1].strip()))

proc callerFileOf*(body: NimNode): string =
  ## Absolute path of the Nim file containing the macro call.
  let li = lineInfo(body)
  let p = li.rfind('(')
  if p < 0:
    error("shedsBlock: cannot determine calling file", body)
  li[0 ..< p]

proc rewriteSheds*(body: NimNode, sheds: var seq[ShedInfo]) =
  ## In-place rewrite of the macro argument: every shed node becomes a
  ## placeholder ident (`shedPlaceholder i`), and `sheds` accumulates the
  ## metadata. Shed contents are never descended into -- the typechecker
  ## is forbidden to tread there, and neither is the converter.
  ##
  ## A `![...]` at top level (outside any proc body) is an error: write a
  ## proc whose body is the shed instead -- that is the Epigram shape
  ## (declaration with its type; the shed is the incomplete RHS).
  if body.kind == nnkStmtList:
    for i in 0 ..< body.len:
      if isShedNode(body[i]):
        error("shedsBlock: a shed must sit inside a proc body, e.g. " &
          "proc plus(x: Nat, y: Nat): Nat = ![ plusBody ] -- " &
          "a bare top-level ![...] has no expected type to check against.", body[i])
  proc walk(n: NimNode, acc: var seq[ShedInfo]) =
    for i in 0 ..< n.len:
      let c = n[i]
      if isShedNode(c):
        let (name, draft, hasDraft) = parseShedParts(c)
        let (ln, co) = parseLineInfo(lineInfo(c))
        acc.add(ShedInfo(name: name,
                         draft: if hasDraft: repr(draft) else: "",
                         nimLine: ln, nimCol: co,
                         holeLine: 0, holeIdx: -1,
                         status: ssYellow))  # issue #134: not yet elaborated
        let ph = ident(shedPlaceholder(acc.len - 1))
        copyLineInfo(ph, c)
        n[i] = ph
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
# Reset rule: if the sidecar on disk is OLDER than the source file, it's
# from a previous compilation -- start fresh. If it's NEWER, it's from an
# earlier `shedsBlock` expansion in THIS compilation -- merge by name.
# (A module-level accumulator var would be cleaner, but the Nim VM cannot
# evaluate globals at compile time, so the reset is keyed on mtimes,
# which are plain file I/O.)
#
# Multiple `shedsBlock` expansions in one file still accumulate within a
# compilation; each fresh `nim c` after an edit starts clean.

proc writeShedSidecar*(nimFile: string, sheds: seq[ShedInfo],
                       errMsg = "") =
  ## Write the sidecar for the LSP server (see reset rule above).
  ## `errMsg` (issue #134): the elaboration failure, if any, so the LSP
  ## server can show *why* a brown shed is brown.
  let path = sidecarPath(nimFile)
  var old: seq[ShedInfo] = @[]
  var fresh = true
  if fileExists(path):
    try:
      # Sidecar older than source => previous compilation => reset.
      fresh = getLastModificationTime(path) < getLastModificationTime(nimFile)
    except OSError:
      discard
  if not fresh:
    try:
      let j = parseJson(readFile(path))
      if j.hasKey("sheds"):
        old = shedsFromJson(j["sheds"])
    except JsonParsingError, IOError:
      discard
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
  ## sheds to holes by generated-source line, and re-apply the status
  ## rule. A document that no longer parses marks every shed brown.
  ## `onlyGenSrc` (issue #137): restrict re-matching to sheds belonging
  ## to the elaborated block (see assignShedStatuses); other sheds keep
  ## their status, holeIdx, and holeCol untouched.
  ## Limitation: matching is by generated-source line, so a multi-line
  ## hole fill shifts later sheds' lines and unmatches them (they read as
  ## white/brown instead of yellow); single-line fills are exact. The
  ## #137 `eponym/refineShed` adjusts holeLine for the shift before
  ## calling here.
  var errMsg = ""
  var holesOk = false
  try:
    let r = elabCheckHolesDir(genSrc, baseDir)
    errMsg = r.errMsg
    for i in 0 ..< sheds.len:
      if onlyGenSrc != "" and sheds[i].genSrc != onlyGenSrc: continue
      sheds[i].holeIdx = -1
      for j in 0 ..< r.ms.holes.len:
        if r.ms.holes[j].holeLoc.line == sheds[i].holeLine:
          sheds[i].holeIdx = j
          sheds[i].holeCol = r.ms.holes[j].holeLoc.col  # self-healing
          break
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
