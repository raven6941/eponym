# sheds.nim -- Shed metadata for the sheds line (issues #133-#137).
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
import strutils
import sequtils

type
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
    goal*: string      # zonked, pretty-printed goal type at the hole
    ctx*: seq[string]  # zonked, pretty-printed binder context ("name : type")

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
                         holeLine: 0, holeIdx: -1))
        let ph = ident(shedPlaceholder(acc.len - 1))
        copyLineInfo(ph, c)
        n[i] = ph
      else:
        walk(c, acc)
  walk(body, sheds)

proc resolveShedPlaceholders*(src: var string, sheds: var seq[ShedInfo]) =
  ## Replace each placeholder with `_` (a #58 hole), recording the
  ## 1-based generated-source line so the macro can match sheds to
  ## MetaStore.holes after elaboration.
  for i in 0 ..< sheds.len:
    let ph = shedPlaceholder(i)
    let pos = src.find(ph)
    if pos < 0:
      raise newException(ValueError, "shed '" & sheds[i].name &
        "': placeholder vanished during conversion (internal error)")
    var line = 1
    for ch in src[0 ..< pos]:
      if ch == '\n': inc line
    sheds[i].holeLine = line
    src = src[0 ..< pos] & "_" & src[pos + ph.len .. ^1]

# --- sidecar JSON: the bridge to the LSP server (issues #134/#135) --------

proc shedToJson*(s: ShedInfo): JsonNode =
  %*{"name": s.name, "draft": s.draft,
      "nimLine": s.nimLine, "nimCol": s.nimCol,
      "holeLine": s.holeLine, "holeIdx": s.holeIdx,
      "goal": s.goal, "ctx": s.ctx}

proc shedFromJson*(j: JsonNode): ShedInfo =
  ShedInfo(name: j["name"].getStr, draft: j["draft"].getStr,
           nimLine: j["nimLine"].getInt, nimCol: j["nimCol"].getInt,
           holeLine: j["holeLine"].getInt, holeIdx: j["holeIdx"].getInt,
           goal: j["goal"].getStr,
           ctx: j["ctx"].elems.mapIt(it.getStr))

proc shedsToJson*(sheds: seq[ShedInfo]): JsonNode =
  result = newJArray()
  for s in sheds: result.add(shedToJson(s))

proc shedsFromJson*(j: JsonNode): seq[ShedInfo] =
  for e in j.elems: result.add(shedFromJson(e))

proc sidecarPath*(nimFile: string): string =
  ## `<dir>/<base>.sheds.json` -- the metadata file the LSP server reads.
  let (dir, base, _) = splitFile(nimFile)
  dir / (base & ".sheds.json")

proc writeShedSidecar*(nimFile: string, sheds: seq[ShedInfo]) =
  ## Write the sidecar for the LSP server. Read-merge-write keyed by shed
  ## *name* (names should be unique per file -- the LSP server targets
  ## sheds by position, and a name identifies the shed across edits that
  ## shift line numbers), so several shedsBlock expansions in one file
  ## accumulate and a recompiled shed overwrites its earlier entry.
  ## Known limitation: entries for sheds deleted from the source linger
  ## until the sidecar is removed by hand.
  let path = sidecarPath(nimFile)
  var old: seq[ShedInfo] = @[]
  if fileExists(path):
    try:
      let j = parseJson(readFile(path))
      if j.hasKey("sheds"):
        old = shedsFromJson(j["sheds"])
    except JsonParsingError, IOError:
      discard
  let here = sheds.mapIt(it.name)
  var merged: seq[ShedInfo] = @[]
  for s in old:
    if s.name notin here:
      merged.add(s)
  for s in sheds:
    merged.add(s)
  writeFile(path, pretty(%*{"file": nimFile, "sheds": shedsToJson(merged)}))

proc readShedSidecar*(path: string): seq[ShedInfo] =
  ## Read a sidecar file (LSP server side, issues #134/#135).
  let j = parseJson(readFile(path))
  shedsFromJson(j["sheds"])

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
