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
11. *(proposed)* **Primitive types** — machine integers via `wRed`,
   avoiding unary `s(s(z))` at the surface.

## Building

Requires Nim 2.x (built with 2.2.12 via
[choosenim](https://github.com/dom96/choosenim)).

```sh
export PATH=$HOME/.nimble/bin:$PATH
nim c -r elab.nim       # elaborator: all suites
nim c -r ett.nim        # finally-tagless ETT: 16 tests
nim c -r ett_init.nim   # initial-encoding ETT: 16 tests
```

## Layout

- `elab.nim`, `unify.nim`, `preterm.nim`, `parse_surf.nim`,
  `mac_surf.nim` — the elaborator.
- `ett.nim` — finally-tagless ETT (evaluator, printer, checker).
- `ett_init.nim` — initial-encoding ETT (de Bruijn AST, evaluator,
  `infer`/`check`/`areEqual`). The elaborator's target.
- `plan.org` — experiment plan and research tracks.
- `decisions.org` — design decision log.
- `research.org` — the driving question.
