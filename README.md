# eponym

A dependently-typed **embedded DSL for Nim**: surface syntax
elaborates at compile time (via Nim macros) to an Epigram-style
QTT core (Chapman, Altenkirch & McBride, "Epigram Reloaded",
TYPES 2006, plus 0/1/ω quantities in the judgments — see
issues #64, #66).

The interesting part is the **elaborator** — the pipeline from
surface syntax to checked core terms. The two ETT encodings
(`ett.nim`, `ett_init.nim`) were the starting point; the elaborator
is where the research lives.

## Why embedded

Eponym is deliberately *not* a standalone language. There's no
compiler, stdlib, package manager, or community to maintain and
market — just an elaborator macro and a prelude, hosted in Nim's
compile time. The maintenance gap is roughly an order of magnitude,
and the adoption friction is far lower: the dependent reasoning
lives in library methods, so users get the safety through a
normal-looking API without writing dependent types themselves.

That encapsulation is the design constraint. The dependent part
belongs in the library; the user's code stays ordinary Nim. The
target case is a session-type library — protocol violations
rejected at compile time through plain `send`/`recv` calls
(issue #28; more motivating cases welcome). Deliberate-embedding
prior art: SynQ, Turnstile/Turnstile+ (the architectural ancestor —
dependent type systems as macros), Liquid Haskell. The honest case
survey lives in the shared notes:
[dep-types-motivating-cases.org](https://github.com/raven6941/notes/blob/main/dep-types-motivating-cases.org).

## The elaborator pipeline

Surface text → `PreTerm` (named) → de Bruijn core terms → elaborated
`Term` with metavariables solved → checked against the QTT core.

- **`parse_surf.nim`** — hand-written surface parser.
- **`mac_surf.nim`** — Nim-AST front end (alternative surface).
- **`preterm.nim`** — named preterm AST, the common interchange.
- **`unify.nim`** — Miller pattern unification for metavariables.
- **`elab.nim`** — bidirectional elaborator: `inferTm`/`checkTm`,
  implicit insertion, `data` desugaring, conversion checking.

## Experiments (see `plan.org`, `decisions.org`)

1. **Surface syntax** — string parser and Nim-AST macro converge on
   `PreTerm`. Chose thin string-literal macro.
2. **De Bruijn core** — named → de Bruijn, compile-time `ett"..."`.
3. **Metavariables** — Miller-pattern unification, holes, bidirectional
   elaboration, implicit insertion. (`unify.nim`)
4. **Extensible reduction** — `postulate`/`elim`/`red`; reduction rules
   stored in `wRed` values. Bool and Nat eliminators compute.
5. **Indexed families** — `data` declarations desugar to
   postulate/elim/red. `Vec` with length indices works.
5b. **Conversion** — `checkTm` uses full conversion (not just
   unification), so `Vec append` with `add` in indices elaborates.
6. **Tactics** — basic `refl`/`assumption`; custom tactic API (in progress).
7. **LSP** — diagnostics via Language Server Protocol; holes/goals/actions (in progress).
8. **Staging** — tagless string generation for residual code (basic; full pipeline in progress).
9. **Erasure** — QTT-lite 0-quantity erased binders (superseded by #66:
   QTT is now the core type theory, not a post-pass).
10. **Conversion cache** — exact equality-query memoization (not yet a true e-graph).
11. **Primitive types** — machine `Int` via `wRed`; Nat literal overloading (`3` instead of `suc` chains).
12. **Propositional equality** — `Eq`/`refl`/`J`; `plusReducesZ` proof works.
13. *(future)* **Polynomial functors** — functorial datatypes (Topos PolyTT).
14. **QTT core** — quantities 0/1/ω in the judgments: quantity-aware
    conversion, in-judgment enforcement at lambda/application sites,
    quantity polymorphism (#66; builds on the #64 prototype).
15. **Constructor disjointness** — `noConfusion`/`noCycle` as named
    disequality facts in unification; impossible clauses rejected
    early (#80).

## Writing eponym in Nim code

The `ettBlock` macro lets you write Eponym directly in Nim:
```nim
import ett_mac
ettBlock:
  postulate(Int, Univ)
  data(Nat, Univ):
    proc zero(): Nat
    proc suc(n: Nat): Nat
  proc add(a, b: Nat): Nat = ...
```
- `Univ` is `?` (universe); `vecnil` for `nil` (Nim keyword).
- Integer literals overload to `Nat` via `checkTm` (or primitive `Int`).
- See `examples/sensor_fusion.nim` for a complete example.

## Track C: Relational × staged interpreters

One relational spec of a small language, many tools
(inference, checking, synthesis) via staging.

- **`src/minikanren.nim`** — independent µKanren-style engine
  (no elaborator deps): S-expr terms, unification with occurs
  check, explicit `Stream` tree (no call-stack recursion),
  FIFO worklist (fair search — backward `typeo` now enumerates
  all results), `=/=` disequality with a constraint store,
  `setEqo` global set-equality constraint, and
  most-constrained-first branching over constraint-derived
  domains (4×4 Sudoku in ~20ms; was a 30s timeout).
- **`src/rel_elab.nim`** — `typeo` relation for STLC+Nat, plus
  a `Vec` length-indexed branch.
- **Staged tools** — each direction of the relation staged to
  direct code: inference with zero search; synthesis pruned
  by expected type (~17000x); evaluation as direct recursion
  (61x); a language-specialized engine on top (546x over the
  generic staged version).
- **`src/lms_staging.nim`** — LMS-style: one `prog` polymorphic
  over `R`; `R = int` executes, `R = Rep` builds IR which
  constant-folds at staging time. No hand-written staged duplicate.
- **`src/synth_staged.nim`** — `evalo` run backwards (static
  language rules, dynamic target value), staged to a direct
  recursive search (6860x), witnesses verified.

Status: the relational path stays experimental until it can be
compared head-to-head against `elab.nim` (the real elaborator).
See `docs/staging-design.md` for the staging architecture.

## Building

Requires Nim 2.x (built with 2.2.12 via
[choosenim](https://github.com/dom96/choosenim)).

```sh
export PATH=$HOME/.nimble/bin:$PATH
nim c -r --path:src src/elab.nim        # elaborator: all suites
nim c -r --path:src tests/run_examples.nim # 11 documented example programs
nim c -r --path:src src/ett.nim         # finally-tagless ETT: 16 tests
nim c -r --path:src src/ett_init.nim    # initial-encoding ETT: 16 tests
```

## Examples

See `examples/` — documented `.ep` programs with header
comments, from basic `twice` through indexed `Vec` with `append`.
They're the regression suite (`run_examples.nim`) and the
documentation of what the system can do. Shared definitions live in
`lib/` (Issue #114) and are pulled into examples with `# import`
header directives.

## Layout

- `elab.nim`, `unify.nim`, `preterm.nim`, `parse_surf.nim`,
  `mac_surf.nim` — the elaborator.
- `ett.nim` — finally-tagless ETT (evaluator, printer, checker).
- `ett_init.nim` — initial-encoding ETT (de Bruijn AST, evaluator,
  `infer`/`check`/`areEqual`). The elaborator's target.
- `plan.org` — experiment plan and research tracks.
- `decisions.org` — design decision log.
- `research.org` — the driving question.
