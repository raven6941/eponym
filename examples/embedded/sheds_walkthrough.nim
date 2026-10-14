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
# The six sheds cover the three hole actions and the layout engine:
#   quadBody     -- sketched: the programmer knows the answer, draft is the plan
#   addThreeBody -- developing: draft is real scratch, with a wrong turn in it
#   shuffleBody  -- greenfield: no draft at all, just a hole and a goal
#   constABody   -- give: the goal is exactly `x`, in scope; one step, no holes
#   isZeroBody   -- case-split: `n : Nat` is the first explicit argument, so
#                   the natural move is case-split on `n` (rewrites this proc
#                   into clause form, one clause per constructor)
#   constEndoBody-- deep nesting: the hole's goal is a Pi type with two
#                   binders, so the 2D layout nests one box per binder around
#                   the hole -- three nested boxes, real Epigram-style depth
#
# What to try per shed (webview: "Eponym: Show shed layout", pick the name):
#   quadBody:      click the hole, refine with the draft text `double (double n)`
#   addThreeBody:  click the hole, refine with the draft (it is deliberately
#                  wrong-typed -- drafts are never elaborated, so this is the
#                  moment to notice and fix it by hand)
#   shuffleBody:   click the hole, refine with `x`
#   constABody:    click the hole and choose "give x" (not refine -- the term
#                  is complete, no holes left behind)
#   isZeroBody:    click the hole, case-split on `n`; fill the two clause
#                  holes (`false` for zero, `true` for suc)
#   constEndoBody: click the hole, refine with `lam (f : A). lam (g : A). f`;
#                  watch the nested binder boxes collapse as binders discharge
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
  import "../../lib/bool.ep"

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

  # Shed 4 -- give. The goal is exactly `x`, already in scope: the natural
  # completion is a single `give`, no refinement steps. (In the webview both
  # "refine hole" and "give x" are offered -- give is the one that promises
  # no holes are left behind.)
  proc constA(A: Univ, x: A): A = ![constABody, x]

  # Shed 5 -- case-split. `n` is the first explicit argument and has an
  # inductive type (Nat from the prelude), so the natural move is
  # case-split on `n`: the webview rewrites this proc into clause form
  # with one clause per constructor, each RHS a fresh hole.
  proc isZero(n: Nat): Bool = ![isZeroBody]

  # Shed 6 -- deep nesting. The hole's goal is a Pi type with two binders
  # (a function with multiple binders), so the 2D layout nests one box per
  # binder around the hole: context above the rule, `f : A`, `g : A`, then
  # the hole with the residual goal `A` innermost. The draft is the plan
  # in surface syntax (drafts are text; they are never elaborated).
  proc constEndo(A: Univ): Pi(f: A, g: A, A) =
    ![constEndoBody, "lam (f : A). lam (g : A). f"]

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
  doAssert ss.len == 6, "expected 6 sheds, got " & $ss.len
  for sh in ss:
    echo "  shed '", sh.name, "' at ", me, ":", sh.nimLine, ":", sh.nimCol
    echo "    goal: ", sh.goal
    echo "    ctx:  ", sh.ctx
    echo "    draft: ", sh.draft
    echo "    status: ", sh.status, " (yellow = stuck, refinable)"
    doAssert sh.status == ssYellow, "expected yellow, got " & $sh.status
  # The deep-nesting shed (issue #192): the hole's Pi goal renders one box
  # per binder around the hole.
  doAssert ss[5].name == "constEndoBody"
  doAssert ss[5].goalPi == @["f : A", "g : A", "A"],
    "expected Pi spine, got: " & $ss[5].goalPi
  let deep = layoutShed(ss[5])
  echo "  layout for 'constEndoBody' (nested binder boxes):"
  for line in renderBox(deep).splitLines():
    echo "    ", line
  # The 2D deduction layout for the greenfield shed, as the webview renders it.
  let lay = layoutShed(ss[2])
  echo "  layout for 'shuffleBody' (Epigram deduction style):"
  for line in renderBox(lay).splitLines():
    echo "    ", line

when isMainModule:
  main()
