# Experiment: a pure Nim subset inside `eponymBlock`

**Status:** `let`, unary minus, `+`, `-`, and `*` for Eponym `Int`, plus a
single-condition `if/else` expression for imported `Bool`, lower to checked
Eponym terms. Chained `elif`, effects, and other operators remain unsupported.

## Motivation

`eponymBlock` uses Nim-shaped syntax, but its body is translated into
Eponym source. Nim statements, library calls, and arbitrary host expressions
do not run inside it. This phase boundary is sound and simple, but can make
an embedded definition feel less natural to a Nim programmer.

Explore a small, explicit subset of *pure expression syntax* that reads like
Nim and translates into Eponym terms. The supported expressions remain
subject to Eponym's parser, type checker, usage checker, and runtime wrapper
limits. The experiment must not execute arbitrary Nim code while claiming
that it was checked by Eponym.

## Initial scope to prototype

The implemented slice covers familiar expressions whose semantics can be
represented directly in the current core:

- local `let` bindings;
- unary minus and `+`, `-`, `*`, lowered to `subInt`, `addInt`, `subInt`, and
  `mulInt` respectively (only when Eponym checks the expression as `Int`).
  Overflow follows the existing primitive implementation; this syntax adds
  no overflow proof or checked arithmetic guarantee.
- `if condition: thenExpr else: elseExpr`, lowered to the polymorphic
  `ifThenElse` definition from `lib/bool.ep`; the condition must check as
  `Bool` and each branch must be one expression.

Potential next forms include:

- chained `elif` branches and broader statement forms;
- integer arithmetic/comparison operators, only where corresponding Eponym
  operations and types exist;
- parentheses and ordinary function application.

Keep declarations, type syntax, imports, IO, mutation, loops, exceptions,
closures over host values, macros, templates, and arbitrary Nim procedure
calls outside the initial subset. Do not silently fall back to Nim
evaluation for an unrecognized expression.

## First vertical slice

The boundary, integer operators, and single-condition `if/else` are
implemented and documented. Property tests compare arithmetic wrappers with
Nim for bounded values; both Boolean branches run through the checked Bool
eliminator. Compile-fail fixtures cover unsupported integer division and
chained `elif`.

Continue with additional pure syntax only when the matching Eponym term and
runtime behavior already exist or can be added with separate soundness review.

## Questions to settle

- Should the accepted form be Nim's statement-shaped `if` or an expression
  helper such as `ifThenElse`?
- What is the smallest Boolean type / eliminator setup required?
- Which integer operators are already present as checked primitives, and
  how are overflow and division semantics specified?
- Should pure expression syntax be identical in `eponymBlock`, `shedsBlock`,
  and standalone `.ep` files, or remain a Nim embedding convenience?
- How should the site and editor communicate which syntax is Eponym-checked?

## Acceptance bar

The prototype is useful if it:

- feels recognizable to a Nim user;
- translates deterministically to checked Eponym terms;
- never executes arbitrary host code inside the checked fragment;
- preserves useful source locations in errors;
- remains small enough to explain in the syntax reference.
