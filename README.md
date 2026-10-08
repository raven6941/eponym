# eponym

A dependently-typed language under construction: surface syntax
elaborates to an Epigram-style ETT core (Chapman, Altenkirch &
McBride, "Epigram Reloaded", TYPES 2006).

The interesting part is the **elaborator** — the pipeline from
surface syntax to checked core terms. The two ETT encodings
(`ett.nim`, `ett_init.nim`) were the starting point; the elaborator
is where the research lives.

## The elaborator pipeline

Surface text → `PreTerm` (named) → de Bruijn core terms → elaborated
`Term` with metavariables solved → checked against the ETT core.

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
9. **Erasure** — QTT-lite 0-quantity erased binders (metadata; full checking in progress).
10. **Conversion cache** — exact equality-query memoization (not yet a true e-graph).
11. **Primitive types** — machine `Int` via `wRed`; Nat literal overloading (`3` instead of `suc` chains).
12. **Propositional equality** — `Eq`/`refl`/`J`; `plusReducesZ` proof works.
13. *(future)* **Polynomial functors** — functorial datatypes (Topos PolyTT).

## Embedding in Nim

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

## Track C: Relational programming

`src/minikanren.nim` — independent relational engine (no elaborator deps):
- S-expr terms, unification with occurs check
- Explicit `Stream` tree (no call-stack recursion)
- `typeo` relation for STLC+Nat (`src/rel_elab.nim`)
- Staged `synthNat`: 17,500x speedup via branch pruning (issue #14)
- Leftist heap for best-first search (`src/heap.nim`, issue #13)

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

See `examples/` — 11 self-contained `.ep` programs with header
comments, from basic `twice` through indexed `Vec` with `append`.
They're the regression suite (`run_examples.nim`) and the
documentation of what the system can do.

## Layout

- `elab.nim`, `unify.nim`, `preterm.nim`, `parse_surf.nim`,
  `mac_surf.nim` — the elaborator.
- `ett.nim` — finally-tagless ETT (evaluator, printer, checker).
- `ett_init.nim` — initial-encoding ETT (de Bruijn AST, evaluator,
  `infer`/`check`/`areEqual`). The elaborator's target.
- `plan.org` — experiment plan and research tracks.
- `decisions.org` — design decision log.
- `research.org` — the driving question.
