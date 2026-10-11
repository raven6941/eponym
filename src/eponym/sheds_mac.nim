# sheds_mac.nim -- the `shedsBlock` macro (issue #133).
#
# Deliberately thin, like ett_mac.nim (see decisions.org on Nimony/Nim 3):
# the Nim->Eponym conversion is plain Nim code (ett_mac.blockToEponym,
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
# Generated code: like ettBlock, each hole-free `def` gets a wrapper
# proc callable from normal Nim code (via the hole-tolerant runtime
# elaboration in ett_embed). Defs mentioning shed holes get no wrapper --
# a hole is not callable -- but their shed metadata is still emitted.

import macros
import os  # parentDir (issue #131, via ett_mac.callerDir)
import elab  # elabCheckHolesDir, ElabError, ElabDef, MetaStore
import parse_surf  # ParseError
import ett_mac  # blockToEponym, callerDir
import ett_embed  # callIntFuncHolesDir (issue #133)
import sheds  # ShedInfo, rewriteSheds, resolveShedPlaceholders, sidecar IO
import usage_check  # hasUnresolvedMetas
import unify  # zonk
import ett_init  # `$` for Term (goal pretty-printing, issue #58)

macro shedsBlock*(body: untyped): untyped =
  ## Elaborate a block of Nim-syntax Eponym definitions containing
  ## Epigram-style sheds (`![ name ]` or `![ name, draft ]` in a proc
  ## body). Shed bodies are unchecked scratch; surrounding code typechecks
  ## normally. `import "path.ep"` works as in ettBlock (issue #131),
  ## resolved relative to the calling Nim file.
  var sheds: seq[ShedInfo] = @[]
  rewriteSheds(body, sheds)
  var src = blockToEponym(body)
  resolveShedPlaceholders(src, sheds)
  let nimFile = callerFileOf(body)
  let baseDir = parentDir(nimFile)
  var defs: seq[ElabDef]
  var ms: MetaStore
  try:
    let r = elabCheckHolesDir(src, baseDir)
    if r.errMsg != "":
      error("shedsBlock elaboration error: " & r.errMsg, body)
    defs = r.defs
    ms = r.ms
  except ParseError as e:
    error("shedsBlock parse error: " & e.msg, body)

  # Match each shed to its hole by generated-source line; record the
  # (zonked) goal type and binder context for the LSP server.
  for i in 0 ..< sheds.len:
    for j in 0 ..< ms.holes.len:
      if ms.holes[j].holeLoc.line == sheds[i].holeLine:
        sheds[i].holeIdx = j
        sheds[i].goal = $(zonk(ms, ms.holes[j].holeGoal))
        for (nm, ty) in ms.holes[j].holeCtx:
          sheds[i].ctx.add(nm & " : " & $(zonk(ms, ty)))
        break

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
