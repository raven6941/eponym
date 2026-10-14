# sheds_mac.nim -- the `shedsBlock` macro (issue #133).
#
# Deliberately thin, like eponym_mac.nim (see decisions.org on Nimony/Nim 3):
# the Nim->Eponym conversion is plain Nim code (eponym_mac.blockToEponym,
# after sheds.rewriteSheds replaces shed nodes with placeholders); the
# macro only feeds the elaborator a string and turns failures into
# compiler errors.
#
# Each `![ name ]` / `![ name, draft ]` shed becomes a `_` hole in the
# generated Eponym source, elaborated hole-tolerantly
# (elab.elabCheckHolesDir: #58 semantics + #131 import support). Sheds
# that remain holes are matched back to MetaStore.holes by generated-
# source line, and their metadata (Nim source position, goal type,
# context, draft) is written to `<nimfile>.sheds.json` for the LSP
# server (issues #134/#135).
#
# Generated code: like eponymBlock, each hole-free `def` gets a wrapper
# proc callable from normal Nim code (via the hole-tolerant runtime
# elaboration in eponym_embed). Defs mentioning shed holes get no wrapper --
# a hole is not callable -- but their shed metadata is still emitted.
#
# Issue #134: each shed's elaboration status (white/yellow/brown) is
# computed at macro time and written to the sidecar; on elaboration
# failure the sidecar is written before the compile error so the editor
# can show brown.

import macros
import os  # parentDir (issue #131, via eponym_mac.callerDir)
import elab  # elabCheckHolesDir, ElabError, ElabDef, MetaStore
import parse_surf  # ParseError
import eponym_mac  # blockToEponym, callerDir
import eponym_embed  # callIntFuncHolesDir (issue #133)
import sheds  # ShedInfo, rewriteSheds, resolveShedPlaceholders, sidecar IO,
              # assignShedStatuses (issue #134)
import usage_check  # hasUnresolvedMetas
import unify  # zonk
import preterm  # qOmega (issue #191: hole-context Ctx, like lsp.nim's hover)

proc shedGoalAndCtx*(ms: MetaStore, h: HoleInfo): tuple[goal: string, ctx: seq[string]] =
  ## Issue #191: name-resolving goal/context rendering for a shed's hole.
  ## Uses #139's `prettyTerm` over `ms.refNames` (populated by the
  ## elaborator when `postulate`/`elim`/data register globals), so
  ## `postulate(Int, Univ)` shows as `Int` instead of `R134`. Binder names
  ## come from the hole context (innermost-first, matching Ctx).
  ## refIds with no registered name keep the `R<n>` fallback (never empty).
  var ctx: Ctx = @[]
  for (nm, ty) in h.holeCtx:
    ctx.add(CtxEntry(name: nm, ty: zonk(ms, ty), qty: qOmega))
  let goal = prettyTerm(zonk(ms, h.holeGoal), ctx, ms.refNames, ms.recordFields)
  var c: seq[string] = @[]
  for (nm, ty) in h.holeCtx:
    c.add(nm & " : " & prettyTerm(zonk(ms, ty), ctx, ms.refNames,
                                 ms.recordFields))
  (goal, c)

macro shedsBlock*(body: untyped): untyped =
  ## Elaborate a block of Nim-syntax Eponym definitions containing
  ## Epigram-style sheds (`![ name ]` or `![ name, draft ]` in a proc
  ## body). Shed bodies are unchecked scratch; surrounding code typechecks
  ## normally. `import "path.ep"` works as in eponymBlock (issue #131),
  ## resolved relative to the calling Nim file.
  var sheds: seq[ShedInfo] = @[]
  rewriteSheds(body, sheds)
  var src = blockToEponym(body)
  resolveShedPlaceholders(src, sheds)
  # Issue #137: record the generated source per shed so the LSP server's
  # `eponym/refineShed` can run the #58 refine action for real `.nim`
  # documents without the client holding the source.
  for i in 0 ..< sheds.len:
    sheds[i].genSrc = src
  let nimFile = callerFileOf(body)
  let baseDir = parentDir(nimFile)
  var defs: seq[ElabDef]
  var ms: MetaStore
  var elabErr = ""
  try:
    let r = elabCheckHolesDir(src, baseDir)
    defs = r.defs
    ms = r.ms
    elabErr = r.errMsg
  except ParseError as e:
    error("shedsBlock parse error: " & e.msg, body)

  # Match each shed to its hole by generated-source line; record the
  # (zonked) goal type and binder context for the LSP server.
  for i in 0 ..< sheds.len:
    for j in 0 ..< ms.holes.len:
      if ms.holes[j].holeLoc.line == sheds[i].holeLine:
        sheds[i].holeIdx = j
        let (g, c) = shedGoalAndCtx(ms, ms.holes[j])
        sheds[i].goal = g
        sheds[i].ctx = c
        break

  # Issue #134: per-shed status (white/yellow/brown). On failure the
  # sidecar is written *before* raising the compile error, so the LSP
  # server can show brown at the shed's source position; sheds that did
  # get a goal stay yellow (stuck, possibly refinable once the
  # surrounding code is fixed).
  assignShedStatuses(sheds, elabErr)
  if elabErr != "":
    writeShedSidecar(nimFile, sheds, elabErr)
    error("shedsBlock elaboration error: " & elabErr, body)

  writeShedSidecar(nimFile, sheds)

  result = newStmtList()
  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  for d in defs:
    if hasUnresolvedMetas(d.tmTm):
      continue  # mentions a shed hole: not callable, no wrapper
    let procName = ident(d.name)
    let nameLit = newLit(d.name)
    result.add(quote do:
      proc `procName`*(args: varargs[int]): int =
        callIntFuncHolesDir(`dirLit`, `srcLit`, `nameLit`, @args))

when isMainModule:
  echo "ok: sheds_mac compiles"
