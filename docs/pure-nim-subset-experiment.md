# Experiment: a pure Nim subset inside `eponymBlock`

**Status:** the `let` form plus unary minus and `+`, `-`, `*` for Eponym
`Int` now lower to checked primitive terms. Pure `if`, booleans, and other
operators remain proposals.

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

The implemented first slice covers familiar expressions whose semantics can
be represented directly in the current core:

- local `let` bindings;
- unary minus and `+`, `-`, `*`, lowered to `subInt`, `addInt`, `subInt`, and
  `mulInt` respectively (only when Eponym checks the expression as `Int`).
  Overflow follows the existing primitive implementation; this syntax adds
  no overflow proof or checked arithmetic guarantee.

Potential next forms include:

- integer and boolean literals (after checking how the existing Eponym
  literal forms elaborate);
- `if condition: thenExpr else: elseExpr`, translated to a Boolean
  eliminator or a core conditional;
- integer arithmetic/comparison operators, only where corresponding Eponym
  operations and types exist;
- parentheses and ordinary function application.

Keep declarations, type syntax, imports, IO, mutation, loops, exceptions,
closures over host values, macros, templates, and arbitrary Nim procedure
calls outside the initial subset. Do not silently fall back to Nim
evaluation for an unrecognized expression.

## First vertical slice

1. Document the current boundary in the surface-syntax reference.
2. Add one expression form—preferably a pure `if` expression—to the AST
   converter with a specific diagnostic for unsupported branches.
3. Desugar it to existing Eponym syntax if possible; otherwise add a
   primitive only with its typing, reduction, and soundness implications
   documented.
4. Add positive and negative examples demonstrating both compilation-time
   checking and the restriction against host effects.
5. Compare the syntax and error messages with normal Nim expectations, and
   decide whether the ergonomic gain justifies the additional DSL surface.

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
