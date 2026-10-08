# Layer Architecture: Staging / Relational / Eponym

Following the abeppu model (scala3-lms as general infrastructure,
staged-minikanren as a client), Eponym's codebase separates into three
layers. Each layer is independently useful; upper layers depend on lower
ones, never the reverse.

## Layer 1: Staging (general infrastructure)

**Purpose**: General-purpose staging machinery, usable for any DSL — not
tied to relations or dependent types. This is the "LMS" of our stack.

**Files**:
- `src/lms_staging.nim` — LMS-style: `ArithSym[R]` with `R=int` (execute)
  vs `R=Rep` (build IR). The pattern for type-driven staging.
- `src/staged_codegen.nim` — macro that generates specialized code from
  relation patterns.
- `src/staged_macro.nim` — compile-time branch pruning macro.

**Dependency rule**: This layer depends on nothing. It provides staging
abstractions (Rep types, smart constructors, codegen macros) that any
client can use. It must not import from kanren/ or eponym/.

**Status**: Demos, not a system. Each staging technique is demonstrated
but there's no unified framework (no annotation-driven stager).

## Layer 2: Relational programming (miniKanren engine)

**Purpose**: General-purpose relational programming — the miniKanren
engine with fair search, constraints, and global propagation. Usable
independently of staging or Eponym.

**Files**:
- `src/minikanren.nim` — the engine: `State` (subst + diseqs + seteqs),
  `Stream`, `Goal`, `==`, `=/=`, `setEqo`, `branchMostConstrained`,
  fair FIFO search, `run`.
- `src/heap.nim` — leftist heap (for best-first search; not yet integrated).
- `src/rel_elab.nim` — `typeo` relation for STLC+Nat+Vec (toy language).
- `src/rel_interp.nim` — `evalo` relation for Nat arithmetic (toy language).

**Dependency rule**: May use Layer 1 (staging) to stage relations, but
the engine itself must work without staging. Must not import from eponym/.
The toy relations (`rel_elab`, `rel_interp`) are *clients* of the engine,
demonstrating it — they are not the engine itself.

**Status**: Engine works (fair search, `=/=`, `setEqo` with naked-single
propagation, fail-first via `branchMostConstrained`). Solves 4x4 Sudoku
in 19.7ms. No CLP(FD) domain stores; search heuristics are basic.

## Layer 3: Eponym (dependently typed language)

**Purpose**: The actual dependently typed language — ETT core, elaborator,
surface syntax. This is the end goal; Layers 1 and 2 are infrastructure
to make it better.

**Files**:
- `src/ett.nim`, `src/ett_init.nim` — ETT core (finally-tagless and initial).
- `src/elab.nim` — the real elaborator (bidirectional, metavariables,
  implicits, conversion).
- `src/unify.nim` — Miller pattern unification for the elaborator.
- `src/preterm.nim`, `src/parse_surf.nim`, `src/mac_surf.nim` — surface syntax.
- `src/ett_mac.nim`, `src/ett_embed.nim` — macro embedding.
- `src/egraph.nim` — e-graph conversion cache (Exp 10).
- `src/lsp.nim` — LSP tooling (Exp 7).

**Dependency rule**: May use Layer 1 (to stage the elaborator) and Layer 2
(for relational elaboration/synthesis). The core language must not depend
on staging or relations to *function* — they are optimizations and tools,
not requirements.

**Status**: Working elaborator (Exps 1-5b). Not yet staged. The relational
elaboration path is experimental (toy only).

## Cross-layer research (not infrastructure)

These files *use* multiple layers to explore the interplay. They are
research artifacts, not layer infrastructure:

- `src/staged_synth.nim`, `staged_arr.nim`, `staged_var.nim`, `staged_vec.nim`
  — hand-staged `typeo` synthesis (Layer 1 technique applied to Layer 2 relation)
- `src/staged_eval.nim` — hand-staged `evalo` (ditto)
- `src/staged_fwd.nim` — hand-staged inference (ditto)
- `src/synth_staged.nim` — staged program synthesis
- `src/sudoku_*.nim` — Sudoku via relations, then staged
- `src/specialized_engine.nim` — engine specialization (2nd Futamura demo)
- `src/unified_driver.nim` — mode-dispatching driver

**Rule**: Research files may import from any layer, but must not be
imported *by* layer infrastructure. If a technique proves general, promote
it down into the appropriate layer.

## Why separate?

1. **Staging is general**: LMS-style staging works for any DSL, not just
   relations. Keeping it separate means we can stage the Eponym elaborator
   directly without going through relations.
2. **Relations are general**: The miniKanren engine is useful independently
   (Sudoku, synthesis, etc.). It shouldn't be tangled with Eponym's types.
3. **Eponym is the goal**: The language should be cleanly separable from
   the tools used to build/optimize it. If staging or relations prove
   unhelpful, Eponym still stands alone.

This mirrors abeppu/scala3-lms (general) vs abeppu/staged-minikanren
(relational client). Our Layer 1 is nascent compared to their LMS; our
Layer 2 is more complete than their relational side (we have `setEqo`
and fail-first; they're stuck on the 2nd projection).
