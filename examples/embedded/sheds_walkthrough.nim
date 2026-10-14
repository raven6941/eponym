# Shed walkthrough demo: Epigram-style interactive development, embedded.
#
# Open this file in VSCode with the Eponym Sheds extension, then run
# "Eponym: Show shed layout" and pick a shed name. Each `![name]` /
# `![name, draft]` is an unchecked region -- "the typechecker is forbidden
# to tread" (Altenkirch, McBride & McKinna 2005): the signature is checked,
# the body is the programmer's scratch. Click a hole (?n) to see its goal
# type and context; try refine / give / case-split and watch the shed go
# from yellow (stuck) to white (done).
#
# The three sheds are at three stages of development:
#   quadBody     -- sketched: the programmer knows the answer, draft is the plan
#   addThreeBody -- developing: draft is real scratch, with a wrong turn in it
#   shuffleBody  -- greenfield: no draft at all, just a hole and a goal
#
# The draft is captured as text and never reaches the elaborator, so it can
# contain wrong turns, Nim-isms, or pseudocode. Only the signature is
# checked; `double` below is complete (white, no shed) and callable from
# normal Nim code.

import sheds_mac
import sheds
import shed_layout  # 2D deduction-style layout of shed proof states
import os  # currentSourcePath, absolutePath
import strutils  # `in` on strings

shedsBlock:
  # Prelude import composes with sheds (issue #131).
  import "../../lib/nat.ep"

  postulate(Int, Univ)

  # Complete definition: elaborates fully, gets a callable wrapper.
  # No shed here -- this one is white from the start.
  proc double(x: Int): Int = addInt(x, x)

  # Shed 1 -- sketched. The draft is the plan; refining the hole with the
  # draft text should close it.
  proc quad(n: Int): Int = ![quadBody, double (double n)]

  # Shed 2 -- developing. The draft is honest scratch: the programmer tried
  # threading the addition through `double` and hasn't decided. (Deliberate
  # wrong turn, and it typechecks as a draft because drafts are never
  # elaborated: `double` is over the postulated Int, but the goal here is
  # Nat -- the draft is allowed to be wrong; that's what sheds are for.)
  proc addThree(n: Nat): Nat = ![addThreeBody, double (add n 3)]

  # Shed 3 -- greenfield. No draft; just a hole, a goal type (Int), and `x`
  # in context. A good first click in the webview.
  proc shuffle(x: Int): Int = ![shuffleBody]

# --- Normal Nim program ------------------------------------------------
# Plain Nim from here. The checked `double` is called like any Nim proc;
# the shed metadata is read from the sidecar exactly as the LSP server
# reads it.

proc main() =
  echo "sheds_walkthrough: multi-shed interactive development demo."
  let v = double(21)
  echo "  double(21) = ", v, " (checked def, called from normal Nim)"
  doAssert v == 42

  let me = absolutePath(currentSourcePath())
  let path = sidecarPath(me)
  doAssert fileExists(path), "sidecar not written: " & path
  let ss = readShedSidecar(path)
  doAssert ss.len == 3, "expected 3 sheds, got " & $ss.len
  for sh in ss:
    echo "  shed '", sh.name, "' at ", me, ":", sh.nimLine, ":", sh.nimCol
    echo "    goal: ", sh.goal
    echo "    ctx:  ", sh.ctx
    echo "    draft: ", sh.draft
    echo "    status: ", sh.status, " (yellow = stuck, refinable)"
    doAssert sh.status == ssYellow, "expected yellow, got " & $sh.status
  # The 2D deduction layout for the greenfield shed, as the webview renders it.
  let lay = layoutShed(ss[2])
  echo "  layout for 'shuffleBody' (Epigram deduction style):"
  for line in renderBox(lay).splitLines():
    echo "    ", line

when isMainModule:
  main()
