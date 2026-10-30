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
# The walkthrough includes six focused sheds plus a two-goal branching demo:
#   quadBody     -- sketched: the programmer knows the answer, draft is the plan
#   addThreeBody -- developing: draft is real scratch, with a wrong turn in it
#   shuffleBody  -- greenfield: no draft at all, just a hole and a goal
#   constABody   -- give: the goal is exactly `x`, in scope; one step, no holes
#   isZeroBody   -- case-split: `n : Nat` is in scope, so split on `n` and
#                   fill the generated Nat eliminator's zero/successor methods
#   constEndoBody-- deep nesting: the hole's goal is a Pi type with two
#                   binders, so the 2D layout nests one box per binder around
#                   the hole -- three nested boxes, real Epigram-style depth
#   branchLeft and branchRight -- two open goals in one proof state; refine
#                   either one, switch goals, and use History / Undo / Redo
#                   to move between the locally known state branches
#
# What to try per shed (webview: "Eponym: Show shed layout", pick the name):
#   quadBody:      click the hole, refine with the draft text `double (double n)`
#   addThreeBody:  click the hole, refine with the draft (it is deliberately
#                  wrong-typed -- drafts are never elaborated, so this is the
#                  moment to notice and fix it by hand)
#   shuffleBody:   click the hole, refine with `x`
#   constABody:    click the hole and choose "give x" (not refine -- the term
#                  is complete, no holes left behind)
#   isZeroBody:    click the hole, case-split on `n`; fill the zero method
#                  with `false` and the successor method with a function
#   constEndoBody: click the hole, refine with `lam(f: A, g: A) => f`;
#                  watch the nested binder boxes collapse as binders discharge
#   branchLeft:    refine with `add ( ? ) ( ? )`; the residual goals and
#                  branchRight remain independently addressable in one state
#   branchRight:   switch from the branchLeft residual, give `n`, then use
#                  Undo / Redo or History to select a locally known root
#
# The draft is captured as text and never reaches the elaborator, so it can
# contain wrong turns, Nim-isms, or pseudocode. Only the signature is
# checked; `double` below is complete (white, no shed) and callable from
# normal Nim code.

import eponym_mac
import sheds
import shed_layout  # 2D deduction-style layout of shed proof states
import os  # currentSourcePath, absolutePath
import strutils  # `in` on strings

eponymBlock:
  # Prelude import composes with sheds (issue #131).
  import "../../lib/nat.ep"
  import "../../lib/bool.ep"

  postulate(Int, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeType(Bool, int)

  # Polymorphic proof examples are intentionally available only to the
  # elaborator; the walkthrough exposes `double` to Nim as its runtime API.
  compileTimeOnly(constA)
  compileTimeOnly(constEndo)

  # Complete definition: elaborates fully, gets a callable wrapper.
  # No shed here -- this one is white from the start.
  proc double(x: Int): Int = addInt(x, x)

  # Shed 1 -- sketched. The draft is the plan; refining the hole with the
  # draft text should close it.
  # Ways you might complete this shed with the VSCode editor:
  # 1. Directly:
  #  a. Press Ctrl+Shift+S (or run "Eponym: Expand inline shed view" from
  #     the command palette). A diagram appears beneath the line with the shed.
  #  b. Press `g` for give; focus moves to the command bar.
  #  c. Enter `double (double n)` and press Enter. The shed is replaced with
  #     this complete expression.
  # 2. Refinement:
  #  a. Expand the inline shed as above, then press `r` for refine.
  #  b. Enter `double ( ? )` and press Enter. The extension wraps the new
  #     hole in `double` and gives it a fresh name.
  #  c. Click the new hole and refine it with `double n` to finish.
  proc quad(n: Int): Int = double ( shedHole(quadBody) )

  # Shed 2 -- developing. The draft is honest scratch: the programmer tried
  # threading the addition through `double` and hasn't decided. (Deliberate
  # wrong turn, and it typechecks as a draft because drafts are never
  # elaborated: `double` is over the postulated Int, but the goal here is
  # Nat -- the draft is allowed to be wrong; that's what sheds are for.)
  # Ways you might complete this shed with the VSCode editor:
  # 1. Replace the draft with a complete term:
  #  a. Expand the inline shed with Ctrl+Shift+S, then click its hole.
  #  b. Press `r` for refine and enter `add (add n 3) 3`.
  #  c. Press Enter. The extension replaces the shed with that term; the
  #     wrong-typed draft is just scratch and does not constrain the repair.
  proc addThree(n: Nat): Nat = ![addThreeBody, double (add n 3)]

  # Shed 3 -- greenfield. No draft; just a hole, a goal type (Int), and `x`
  # in context. A good first click in the webview.
  # Ways you might complete this shed with the VSCode editor:
  # 1. Refine directly from the context:
  #  a. Expand the inline shed with Ctrl+Shift+S, then click its hole to
  #     inspect the goal and context.
  #  b. Press `r` for refine and enter `x`.
  #  c. Press Enter. The hole is replaced with `x` from the context.
  proc shuffle(x: Int): Int = ![shuffleBody]

  # Shed 4 -- give. The goal is exactly `x`, already in scope: the natural
  # completion is a single `give`, no refinement steps. (In the webview both
  # "refine hole" and "give x" are offered -- give is the one that promises
  # no holes are left behind.)
  # Ways you might complete this shed with the VSCode editor:
  # 1. Give the complete term:
  #  a. Expand the inline shed with Ctrl+Shift+S, then click its hole.
  #  b. Press `g` for give and enter `x`.
  #  c. Press Enter. Give installs the complete term directly, with no
  #     smaller hole left to solve.
  proc constA(A: Univ, x: A): A = ![constABody, x]

  # Shed 5 -- case-split. `n` is the first explicit argument and has an
  # inductive type (Nat from the prelude), so split on `n`. The action
  # replaces the hole with a Nat eliminator and creates a fresh shed for
  # each constructor method.
  # Ways you might complete this shed with the VSCode editor:
  # 1. Split on `n`, then give each case:
  #  a. Expand the inline shed with Ctrl+Shift+S, then click its hole.
  #  b. Press `c` for case-split and enter `n`. The extension replaces the
  #     hole with a Nat eliminator and creates a fresh shed for each method.
  #  c. Click the zero-case hole, press `g`, and enter `false`.
  #  d. Click the successor-case hole, press `g`, and enter
  #     `lam(n: Nat, b: Bool) => true`. Nat case-split uses the
  #     induction eliminator: the successor method receives the predecessor
  #     `n` and the induction result `b : Bool`, so bare `true` does not
  #     inhabit that method goal. The diagnostics should clear after both
  #     methods are filled.
  proc isZero(n: Nat): Bool = ![isZeroBody]

  # Shed 6 -- deep nesting. The hole's goal is a Pi type with two binders
  # (a function with multiple binders), so the 2D layout nests one box per
  # binder around the hole: context above the rule, `f : A`, `g : A`, then
  # the hole with the residual goal `A` innermost. The draft is the plan
  # in surface syntax (drafts are text; they are never elaborated).
  # Ways you might complete this shed with the vscode editor:
  # 1. Step by step:
  #  a. Ctrl+Shift+S to expand the inline shed, then click the innermost hole
  #     to inspect its goal and the `f`/`g` context.
  #  b. Press `r` for refine and enter `lam(f: A) => _`; this introduces `f`
  #     and leaves a smaller hole with `g` in context.
  #  c. Click that hole, press `r` again, and enter `lam(g: A) => _`.
  #  d. In the resulting hole, refine with `f` or `g` to complete the proof.
  #     `f` ignores `g`, while `g` returns it.
  # 2. All at once:
  #  a. Expand the inline shed as above and press `r` for refine.
  #  b. Enter `lam(f: A, g: A) => f`; the nested binder boxes collapse
  #     as the proof becomes complete.
  proc constEndo(A: Univ): Pi(f: A, g: A, A) =
    ![constEndoBody, "lam(f: A, g: A) => f"]

  # Two independent goals make branch selection visible in the walkthrough.
  # Refine either marker while preserving its sibling, then select another
  # known proof-state root from the History button without an LSP commit.
  proc branchDemo(n: Nat): Nat = add ( ![branchLeft] ) ( ![branchRight] )

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
  doAssert ss.len == 8, "expected 8 sheds, got " & $ss.len
  for sh in ss:
    echo "  shed '", sh.name, "' at ", me, ":", sh.nimLine, ":", sh.nimCol
    echo "    goal: ", sh.goal
    echo "    ctx:  ", sh.ctx
    echo "    draft: ", sh.draft
    echo "    status: ", sh.status, " (yellow = stuck, refinable; white = filled)"
    # Issue #478: a valid draft fills its shed at compile time, so
    # constABody (draft `x`, the complete proof) is white; the rest
    # stay yellow — addThreeBody's draft is ill-typed (Int `double`
    # for a Nat goal), constEndoBody's is a string note, and the
    # others have no draft.
    let want = if sh.name == "constABody": ssWhite else: ssYellow
    doAssert sh.status == want, "shed '" & sh.name & "': expected " &
      $want & ", got " & $sh.status
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
