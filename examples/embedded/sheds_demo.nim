# Sheds demo (Issue #133): Epigram-style unchecked regions, embedded.
#
# A *shed* (`![ name ]` / `![ name, draft ]`) is a region "the typechecker
# is forbidden to tread" (Altenkirch, McBride & McKinna 2005): the macro
# turns it into a hole, elaborates the surrounding program
# hole-tolerantly, and records shed metadata (source position, goal type,
# context, draft) to `<thisfile>.sheds.json` for the LSP server
# (issues #134/#135).
#
# The draft below is deliberately ill-typed as Eponym (`++++` is not an
# Eponym operator): it is valid Nim syntax so the macro can receive it,
# but if the elaborator ever looked inside the shed, this file would not
# compile. The shed is scratch; only the signature is checked.

import sheds_mac
import sheds
import os  # currentSourcePath, absolutePath
import strutils  # `in` on strings

shedsBlock:
  # Prelude import (issue #131) composes with sheds.
  import "../../lib/nat.ep"

  postulate(Int, Univ)

  # Complete definition over primitive Int: callable from normal Nim code.
  proc double(x: Int): Int = addInt(x, x)

  # Complete definition over Nat from the prelude: elaborates (proves the
  # import works alongside sheds) but gets no callable wrapper use here.
  proc addTwo(n: Nat): Nat = add(n, 2)

  # The shed: body is unchecked scratch with goal Int and `n : Int` in
  # scope. `quad` still elaborates (hole-tolerantly); `double` still runs.
  proc quad(n: Int): Int = ![ quadBody, n ++++ n ]

# --- Normal Nim program ------------------------------------------------
# Plain Nim from here. The checked `double` is called like any Nim proc;
# the shed metadata is read from the sidecar exactly as the LSP server
# will read it.

proc main() =
  echo "sheds_demo: Epigram-style sheds, embedded (Issue #133)."
  let v = double(21)
  echo "  double(21) = ", v, " (checked def, called from normal Nim)"
  doAssert v == 42

  let me = absolutePath(currentSourcePath())
  let path = sidecarPath(me)
  doAssert fileExists(path), "sidecar not written: " & path
  let ss = readShedSidecar(path)
  doAssert ss.len == 1, "expected 1 shed, got " & $ss.len
  let sh = ss[0]
  doAssert sh.name == "quadBody"
  # Goal/context render with the elaborator's `$` (rigid `R<n>` for the
  # postulated Int -- the same rendering LSP hover uses today; resolving
  # rigid names is a follow-up). What matters: the goal is Int and the
  # context carries `n` at that same type.
  doAssert sh.goal.startsWith("R"), "goal was: " & sh.goal
  doAssert sh.ctx == @["n : " & sh.goal], "ctx was: " & $sh.ctx
  doAssert "++++" in sh.draft, "draft was: " & sh.draft
  doAssert sh.holeIdx == 0
  # Issue #134: the open shed is yellow (stuck, refinable); it would go
  # white once its hole is filled and brown if elaboration failed.
  doAssert sh.status == ssYellow, "status was: " & $sh.status
  echo "  shed '", sh.name, "' at ", me, ":", sh.nimLine, ":", sh.nimCol
  echo "    goal: ", sh.goal
  echo "    ctx:  ", sh.ctx
  echo "    draft (never elaborated): ", sh.draft
  echo "  surrounding code typechecked; shed stayed a hole."
  echo "  status: ", sh.status, " (yellow = stuck, refinable)."

when isMainModule:
  main()
