# Eponym — Project Plan and Architecture

> **Maintenance contract:** this file lives on `main` and describes the
> *expected* architecture — where the project is heading, not just where it
> is. When a merged branch changes the architecture (new layer, new pipeline
> stage, new core), update this file in the same merge. If reality drifts
> from the plan, either change the plan or file an issue; never let them
> silently diverge.

## The idea

Eponym is a dependently-typed language **embedded in Nim**. It is
deliberately not a standalone language: no compiler, stdlib, package
manager, or community to maintain and market. The dependent reasoning
lives in library code; users get the safety through a normal-looking API
without writing dependent types themselves.

The thesis: twenty years of dependently-typed languages (Epigram, Agda,
Idris) stalled on the adoption problem — each asked programmers to buy a
whole new ecosystem. A library in a language people already use is a much
easier sell. The target case is a session-type library: protocol
violations rejected at compile time through plain `send`/`recv` calls
(issue #28). Deliberate-embedding prior art: Turnstile/Turnstile+ (the
architectural ancestor — dependent type systems as macros), SynQ, Liquid
Haskell.

## Architecture overview

Three views of the same system: the **embedding pipeline** (what happens
at compile time), the **layer stack** (dependency discipline), and the
**Track C vision** (where the elaborator is heading).

### 1. The embedding pipeline

User code is ordinary Nim. Eponym surface syntax appears inside a macro;
the macro elaborates it at compile time and splices ordinary Nim code
back. The dependent types evaporate — zero runtime cost.

```
┌──────────────────────────────────────────────────────────────┐
│  Nim source: ordinary Nim + ett"..." / ettBlock surface      │
└──────────────────────────┬───────────────────────────────────┘
                           │ macro expansion (compile time)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Surface syntax                                              │
│  parse_surf.nim (string parser)  ·  mac_surf.nim (Nim AST)    │
└──────────────────────────┬───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  PreTerm — named preterm AST, the common interchange          │
│  preterm.nim                                                 │
└──────────────────────────┬───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Elaborator — bidirectional inferTm/checkTm                  │
│  elab.nim                                                    │
│    · metavariables + Miller-pattern unification (unify.nim)   │
│    · implicit insertion                                      │
│    · conversion checking (not just unification)              │
│    · data desugaring → postulate/elim/red                    │
│    · clause compilation → eliminators (issue #32)            │
│    · termination checking (issue #36)                        │
│    · equality as overridable effect: handler stack,          │
│      coreValid vs extending handlers (issue #41)             │
│    · positivity checking (issue #33, planned)                │
│    · constructor disjointness: noConfusion, noCycle (#80)    │
└──────────────────────────┬───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  QTT core — small trusted kernel, quantities in judgments    │
│  ett.nim (finally-tagless)  ·  ett_init.nim (initial enc.)    │
│  postulate / elim / red declarations; wRed values            │
└──────────────────────────┬───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Ordinary Nim — residual code, compiled as usual              │
│  ett_mac.nim / ett_embed.nim                                 │
└──────────────────────────────────────────────────────────────┘
```

Design rule: the core never learns pattern matching, coverage, or
termination. The elaborator compiles all of that down to eliminator
applications and reduction rules. The trusted core stays small; the
elaborator does the work once.

### 2. The layer stack

Three layers, strict dependency discipline — each independently useful,
upper layers depend on lower ones, never the reverse. (See
`docs/layers.md` for the full contract.)

```
┌──────────────────────────────────────────────────────────────┐
│  Layer 3: Eponym — the dependently-typed language            │
│  elab.nim, ett.nim/ett_init.nim, unify.nim, surface syntax,   │
│  ett_mac.nim, ett_embed.nim, egraph.nim, lsp.nim              │
│  May use Layers 1–2 for staging/relations, but the core       │
│  must work without them.                                     │
└──────────────────────────┬───────────────────────────────────┘
                           │ uses (never depends on)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Layer 2: Relational programming — miniKanren engine         │
│  minikanren.nim (fair FIFO search, =/=, setEqo, constraints)  │
│  rel_elab.nim (typeo), rel_interp.nim (evalo) — toy clients   │
│  May use Layer 1 for staging; must not import Layer 3.       │
└──────────────────────────┬───────────────────────────────────┘
                           │ uses (never depends on)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Layer 1: Staging — general infrastructure, DSL-agnostic      │
│  lms_staging.nim (LMS-style Rep), staged_codegen.nim,         │
│  staged_macro.nim                                            │
│  Depends on nothing.                                         │
└──────────────────────────────────────────────────────────────┘
```

Cross-layer research files (staged_synth, synth_staged,
specialized_engine, unified_driver, sudoku_*) explore the interplay;
they are experiments, not infrastructure.

### 3. The Track C vision — where the elaborator is heading

The long-term bet: write the language spec **once, relationally**, and
derive efficient tools (inference, checking, synthesis) for each
*direction* via staging. The relational elaborator must then be compared
head-to-head against the direct elaborator (issue #26). The relational
path stays experimental until that comparison happens.

```
┌──────────────────────────────────────────────────────────────┐
│  Relational spec — ONE definition, many directions           │
│  typeo(tm, ty, ctx): infer / check / synth modes              │
│  evalo(tm, val): forward eval / backward synthesis            │
│  (slow, general — the source of truth)                        │
└──────────────────────────┬───────────────────────────────────┘
                           │ stage by mode (what's known at
                           │ compile time?)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Staged tools — one efficient procedure per mode              │
│  inferType, checkType (term static)                          │
│  synthNat, synthArr (type static)                            │
│  stageEval (term static)                                      │
│  measured: 61x–17,000x over interpretive; correct            │
└──────────────────────────┬───────────────────────────────────┘
                           │ specialize the engine itself
                           │ (2nd Futamura projection)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Specialized engine — dedicated reps, no generic dispatch     │
│  546x over staged; ~9Mx over naive                           │
└──────────────────────────────────────────────────────────────┘
```

Current status: demonstrated on toy STLC+Nat+Vec (`typeo`/`evalo`).
The real target is staging *elab.nim itself* — metavariables,
implicits, conversion and all.

## Roadmap

Completed experiments (see `plan.org`, `decisions.org`):

| # | Experiment | Result |
|---|-----------|--------|
| 1 | Surface syntax (string parser + Nim-AST macro) | Thin string-literal macro chosen |
| 2 | Compile-time elaboration via macros | Hybrid: string literal through macro |
| 3 | Metavariables, Miller unification, implicits | Bidirectional infer/check works |
| 4 | Extensible reduction (`postulate`/`elim`/`red`) | Bool/Nat eliminators compute |
| 5/5b | Indexed families + conversion in checkTm | `Vec`, `append` with `add` in indices |
| 6 | Tactics and reflection | `refl`/`assumption`; API in progress |
| 7 | LSP tooling | Diagnostics; holes/goals in progress |
| 8 | Staged ETT evaluator | Tagless-final staging works |
| 17 | ETT staging rules (Phase 2 validation) | Sym[SVal] with staging-time beta-reduction; twice/const/pairSwap staged == unstaged; 15.8x hoisting speedup, 0.67x on pure dispatch (negative) |
| 9 | Erasure (QTT-lite) | Superseded by #66: QTT is the core now, not a post-pass |
| 10 | Conversion cache | Exact memoization; e-graph future |
| 11 | Primitive Int | Machine int via wRed; literal overloading |
| 12 | Propositional equality | `Eq`/`refl`/`J`; `plusReducesZ` proven |
| 19/35 | Staged typeo benchmark + residual compiler | 1.90x vs compiled unstaged; 9/9 correct |
| 27 | Mode inference for relational staging | Inferred modes reproduce manual ones |
| 26 | Staged relational elaborator vs direct | REOPENED 2026-10-09: checker parity + negative staging result closed it early; finishing requires #59 (elabo with output terms) + #57 (direct-style codegen) |
| 60 | Compiled defunctionalized code pointers (compileD) | 1.9x→~1.4–1.7x gap vs baseline; closure-call indirection left to #72 |
| 64 | QTT prototype (ETT + linear binders) | Post-elaboration usage checker; feasibility step for #66 |
| 66 | QTT as the core type theory | Quantities in the judgments: in-judgment enforcement, quantity-aware conversion, quantity polymorphism, subject-side checking-mode tracking |
| 80 | Constructor disjointness | noConfusion/noCycle as named disequality facts; fail-fast unification, early impossible-clause rejection |

In flight (ordered):

1. **#26 — finish the staged relational elaborator** (reopened 2026-10-09):
   what shipped was a relational *checker* plus incomplete staging
   (specialized interpreter, 11–87x slower). Per Aaron these are not
   follow-ups but the remainder of #26 itself:
   - #59: `elabo(tm, ty, ctx, etm)` — relational elaboration producing
     elaborated terms, differential-tested against `checkTermElab` output
   - #57: residual direct-style codegen (no Goal/Stream layer),
     head-to-head wall-clock verdict vs the direct elaborator
   #26 stays open until both land and the comparison is end-to-end.

Completed: **#41 — equality as overridable effect** (Andromeda-style;
merged d4c4ceb: `convElab` effect site, `ConvHandler={decide,coreValid}`,
`cacheConvHandler` at 1.04–1.08x, `natArithHandler` as `by arith` tactic);
**#36 — termination checking** (structural recursion for
`red` rules and clause definitions; 10-accepted/8-rejected corpus);
**#32 — clause-style definitions** (MVP + indexed families; `vappend`
elaborates and computes);
**#60 — compiled defunctionalized code pointers** (`compileD`: dfLam compiles
DForm bodies to host closures once; gap 1.9x→~1.4–1.7x, remainder to #72);
**#64 — QTT prototype** (ETT + linear binders, post-elaboration usage checker;
feasibility step for #66);
**#66 — QTT as the core type theory** (quantities in the judgments:
quantity-aware conversion, application-site enforcement, quantity
polymorphism, subject-side checking-mode tracking);
**#80 — constructor disjointness** (`noConfusion`/`noCycle` as named
disequality facts in unification; impossible clauses rejected early).

Then: #33 positivity, #34 error snapshots, #37 records, #38 elaboration
adequacy tests, #28 session-type library demo (the motivating case),
DCP/convexity case (no issue yet — strong second demo).

## Building

Requires Nim 2.x (built with 2.2.12 via choosenim):

```sh
export PATH=$HOME/.nimble/bin:$PATH
```

Full local CI matrix before merging to main (mirrors
`.github/workflows/ci.yml`): build and run `ett`, `ett_init`,
`preterm`, `parse_surf`, `mac_surf`, `elab`, `ett_mac`, `egraph`,
`ett_embed`, plus `tests/run_examples.nim`. `lsp.nim` is built but not
executed (it's a server loop, not a test). Keep the build warning-clean.

## References

- `plan.org` — experiment plan and research questions
- `decisions.org` — decision log (what worked, what didn't, and why)
- `research.org` — the motivating question
- `docs/layers.md` — layer dependency contract
- `docs/staging-*.md`, `docs/pipeline-architecture.org` — Track C design
- Shared zettelkasten: https://github.com/raven6941/notes
