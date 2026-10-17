# sheds_mac.nim -- the `shedsBlock` macro (issue #133).
#
# Deliberately thin, like eponym_mac.nim (see decisions.org on Nimony/Nim 3):
# the Nim->Eponym conversion is plain Nim code (eponym_mac.blockToEponym,
# after sheds.rewriteSheds replaces shed nodes with placeholders); the
# macro only feeds the elaborator a string and turns failures into
# compiler errors.
#
# Each `![ name ]` / `![ name, draft ]` or nested `shedHole(name)` shed
# becomes a `?` hole in the generated Eponym source, elaborated hole-tolerantly
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
import eponym_init  # tPi (issue #192: Pi-spine walk of the shed goal)
import elab  # elabCheckHolesDir, ElabError, ElabDef, MetaStore
import parse_surf  # ParseError
import eponym_mac  # blockToEponym, callerDir
import eponym_embed  # callIntFuncHolesDir (issue #133)
import sheds  # ShedInfo, rewriteSheds, resolveShedPlaceholders, sidecar IO,
              # assignShedStatuses (issue #134)
import usage_check  # hasUnresolvedMetas
import unify  # zonk
import preterm  # qOmega (issue #191: hole-context Ctx, like lsp.nim's hover)

proc shedGoalAndCtx*(ms: MetaStore, h: HoleInfo): tuple[goal: string, ctx: seq[string], goalPi: seq[string]] =
  ## Issue #191: name-resolving goal/context rendering for a shed's hole.
  ## Uses #139's `prettyTerm` over `ms.refNames` (populated by the
  ## elaborator when `postulate`/`elim`/data register globals), so
  ## `postulate(Int, Univ)` shows as `Int` instead of `R134`. Binder names
  ## come from the hole context (innermost-first, matching Ctx).
  ## refIds with no registered name keep the `R<n>` fallback (never empty).
  ##
  ## Issue #192: also returns the goal's Pi spine as strings, outermost
  ## first -- one "name : dom" entry per Pi binder, then the residual goal
  ## as the last element (empty when the goal is not a Pi). The 2D layout
  ## nests one box per binder, so a shed over a multi-binder function type
  ## shows real nesting instead of one flat hole box.
  var ctx: Ctx = @[]
  for (nm, ty) in h.holeCtx:
    ctx.add(CtxEntry(name: nm, ty: zonk(ms, ty), qty: qOmega))
  let goal = prettyTerm(zonk(ms, h.holeGoal), ctx, ms.refNames, ms.recordFields)
  var c: seq[string] = @[]
  for (nm, ty) in h.holeCtx:
    c.add(nm & " : " & prettyTerm(zonk(ms, ty), ctx, ms.refNames,
                                 ms.recordFields))
  var pi: seq[string] = @[]
  var g = zonk(ms, h.holeGoal)
  var pc = ctx
  while g.kind == tPi:
    let nm = g.scope.adv
    let dom = zonk(ms, g.dom)
    pi.add(nm & " : " & prettyTerm(dom, pc, ms.refNames, ms.recordFields))
    # Ctx is innermost-first (prettyTerm indexes tV 0 at ctx[0]), so the
    # binder just descended under goes at the front, as prettyTerm itself
    # does when it walks binders.
    pc = @[CtxEntry(name: nm, ty: dom, qty: qOmega)] & pc
    g = zonk(ms, g.scope.bdy)
  if pi.len > 0:
    pi.add(prettyTerm(g, pc, ms.refNames, ms.recordFields))
  (goal, c, pi)

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
  # Match each shed to its hole by generated-source line *and column*
  # (issue #209: case-split produces multiple sheds on one line, so
  # line-only matching misattributes goals -- cf. refineShed's matcher
  # in lsp.nim, which already does line+column).
  for i in 0 ..< sheds.len:
    var best = -1
    for j in 0 ..< ms.holes.len:
      if ms.holes[j].holeLoc.line != sheds[i].holeLine: continue
      if best < 0: best = j  # first line match: the fallback
      if sheds[i].holeCol > 0 and ms.holes[j].holeLoc.col == sheds[i].holeCol:
        best = j
        break  # exact match wins
    if best >= 0:
      sheds[i].holeIdx = best
      let (g, c, pi) = shedGoalAndCtx(ms, ms.holes[best])
      sheds[i].goal = g
      sheds[i].ctx = c
      sheds[i].goalPi = pi

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
