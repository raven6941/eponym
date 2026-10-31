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

import eponym_mac
import sheds
import shed_layout  # Issue #135: 2D deduction-style layout of shed proof states
import os  # currentSourcePath, absolutePath
import strutils  # `in` on strings

eponymBlock:
  # Prelude import (issue #131) composes with sheds.
  import "../../lib/nat.ep"

  postulate(Int, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)

  # Complete definition over primitive Int: callable from normal Nim code.
  proc double(x: Int): Int = addInt(x, x)

  # Current bracket syntax for explicit Eponym generic parameters and calls.
  proc checkedIdentity[A: Univ](value: A): A = value
  proc checkedIdentityInt(value: Int): Int = checkedIdentity[Int](value)

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
  doAssert checkedIdentityInt(17) == 17

  let me = absolutePath(currentSourcePath())
  let path = sidecarPath(me)
  doAssert fileExists(path), "sidecar not written: " & path
  let ss = readShedSidecar(path)
  doAssert ss.len == 1, "expected 1 shed, got " & $ss.len
  let sh = ss[0]
  doAssert sh.name == "quadBody"
  # Goal/context render with name-resolving pretty-printing (issue #191):
  # the postulated Int renders as "Int", not rigid `R<n>`. What matters:
  # the goal is Int and the context carries `n` at that same type.
  doAssert sh.goal == "Int", "goal was: " & sh.goal
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
  # Issue #135: the shed's proof state as an Epigram-style 2D deduction
  # (context above the rule, the hole below it), exactly what the LSP
  # method `eponym/shedLayout` returns.
  let lay = layoutShed(sh)
  doAssert allHoleIds(lay) == @[sh.holeIdx], "hole id wiring"
  echo "  layout (Issue #135, Epigram deduction style):"
  for line in renderBox(lay).splitLines():
    echo "    ", line

when isMainModule:
  main()
