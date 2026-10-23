# Working with sheds in VS Code

This guide covers the Eponym Sheds extension for Nim files that use
`shedsBlock`. A shed is a named incomplete expression, written in source as
`![name]` (or `![name, draft]`). The declaration around it supplies the type
the shed must eventually prove.

## Open a shed

Put the cursor on the `![name]` marker and run **Eponym: Expand inline shed
view** from the Command Palette. The default shortcut is **Ctrl+Shift+S**.
You can also use the `shed name : goal` CodeLens above a marker; clicking it
opens that specific shed without relying on cursor position. The 2D display
is rendered as virtual CodeLens rows above the marker, so it stays in the
editor without changing the Nim document. Press **Escape** to collapse it.

The extension compiles a `shedsBlock` file with Nim to generate or refresh
its `.sheds.json` sidecar. This is how it learns the current goals and
contexts. If the editor has unsaved changes, Eponym saves them first because
Nim compiles the file on disk. Compilation errors appear in the **Eponym** Output channel and in
an error notification. Configure `eponym.nimPath` if VS Code cannot find
your Nim executable.

While it is expanded, press **i** to introduce a function binder, **r** to
refine, **g** to give, or **c** to case-split. Use the **Apply**, **Construct**,
and **Rewrite** buttons in the inline view to choose a checked candidate from
a filterable list. Refine, Give, and Case-split open an input prompt for a term
or variable name.

## Read the 2D view

The view is a proof state, read from top to bottom:

- The top premise shows the variables currently in scope, with their types.
  For example, `n : Nat` means you may use `n` in a term for this goal.
- A horizontal rule separates those assumptions from the goal.
- The bottom box is the expression that still needs to be supplied. A label
  such as `?0 : Bool` means the open hole has type `Bool`.
- For a function goal, nested boxes show the arguments you can introduce.
  For `Pi(f: A, g: A, A)`, the view shows `f : A`, then `g : A`, and finally
  the remaining goal `A`. A term such as `lam f. lam g. f` supplies those
  arguments and returns the first one.
- `?n` is an internal hole ID printed by the view. It is not a variable to
  type into the editor or a source marker name. Each remaining goal has a
  named shed marker; use that marker or its CodeLens to open the goal you
  want to work on.

Context entries and nested binder boxes show the names the elaborator has
for variables in scope or available to introduce. Names from the source are
normally preserved. Generated names such as `ih0` are introduced by
elaboration; in an induction case, `ih0` is the induction hypothesis for the
recursive argument. Its displayed type tells you what it proves; after you
introduce it, it is available as a variable in the remaining goal. A
fallback name like `R134` is an internal reference whose source-level name
is unavailable; use the displayed type and surrounding goal to understand
its role.

## Choose an action

### Refine

Use **Refine** when you want to advance the proof but may leave smaller goals
behind. Enter an Eponym term, not Nim implementation syntax. The term must
type-check against the selected hole. `?` creates a new goal, which remains
available after the source is saved and recompiled.

For example, with goal `Pi(f: A, g: A, A)`, refine with:

```text
lam f. lam g. ?
```

This introduces both arguments and leaves a goal of type `A` in the context
`f : A`, `g : A`. That residual goal is written in Nim using the internal
`shedHole(name)` encoding because Nim cannot parse `![name]` in every nested
expression position. It is still a named shed: the extension can reopen it,
and the macro records its goal like any `![name]` shed.

### Intro

Use **Intro** when the goal is a function type. It introduces the first
function binder with its goal-provided name and type, then leaves the
dependent codomain as the new goal. The operation checks the generated lambda
against the current goal and preserves any dependency on the introduced
variable. Repeat Intro to introduce further binders. For example, a goal
`Pi(f: A, g: A, A)` becomes a goal `Pi(g: A, A)` in the context `f : A`.
Intro reports a useful error when the goal is not a function type.

### Apply

Use **Apply** to search local hypotheses for terms that can produce the
current goal. Its filterable picker displays applications accepted by the
checker. Arguments determined by the expected dependent result are filled in;
remaining arguments stay as named sheds. For example, with
`f : Pi(x: A, B x)`, `a : A`, and goal `B a`, the picker offers `f a`. If a
candidate still needs an argument, applying it creates a shed with that
argument's type after substituting the inferred values. Apply searches local
hypotheses; named global definitions are not searched.

### Give

Use **Give** when the term is the complete answer. Give checks both that the
term has the required type and that it leaves no holes. If it fails, the
source and sidecar are left unchanged. For the inner goal above, `f` is a
valid Give because `f : A` is already in scope and the goal is `A`.

Refine can also accept `f`, but Give communicates the stronger intention:
finish this shed completely.

### Case-split

Use **Case-split** when the goal depends on a variable whose constructors
suggest separate cases. Enter the variable name, for example `n` when the
context contains `n : Nat`. The extension replaces the selected shed with an
eliminator and creates one named shed per constructor. For `Nat`, that means
a zero branch and a successor branch. Open each branch and solve its goal
with Refine or Give; recursive cases may include an induction hypothesis
such as `ih0`.

Case-split supports parameterized and indexed datatypes, including
`List[Nat]`, generic `List[A]`, and `Vec[Nat, n]`. It reuses the parameters,
generalizes the motive over the family indices, and carries direct index
variable dependencies into branch goals. A dependent target using a compound
index expression is generalized when the target contains that exact
expression; other uses of context variables remain intact. Eponym rechecks the
generated eliminator before returning the splice. If a type expression is
outside the supported Nim shed syntax, the extension reports why it rejected
the split.

### Rewrite

Use **Rewrite** when an equality proof in the local context relates a term in
the goal to another term. The picker names the proof, direction, and matching
occurrence. `e forward occurrence 1` uses `e : Eq A x y` to replace the first
exact occurrence of `x` by `y`; the generated equality eliminator transports
the remaining proof goal back to the original target. Reverse choices use the
symmetric equality. Each selected occurrence is checked before it is spliced.

Rewrite currently matches structurally identical endpoint terms. It needs the
`Eq` family and its `eqElim`/`sym` definitions in scope, for example through
`lib/eq.ep`. If no checked choice can be generated, the action reports why it
could not offer a rewrite and leaves the source unchanged.

## After an action

Intro, Apply, Construct, Rewrite, Refine, Give, and Case-split splice their
result into the Nim source and
save the document. The extension recompiles the `shedsBlock`, refreshing the
sidecar and CodeLens goals. A remaining open goal stays yellow and gets its
own marker; a completed shed is white and has no open goal. If a newly
created marker does not appear in the extension, check the **Eponym** Output
channel for a Nim compile error and make sure the installed extension was
rebuilt from the current source.

The CodeLens and `shedsBlock` source marker are the durable navigation
points. The 2D view is virtual editor content, not proof source, and does not
dirty the document or interfere with manual or automatic saves.
