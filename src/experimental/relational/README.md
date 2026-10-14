# Relational programming framework (`src/relational/`)

miniKanren engine and relational interpreters. Potentially an independent
library. Used by Track C (relational × staged interpreters): the idea that
relationally-defined interpreters, run in different directions, can be
staged into efficient tools (evaluation, type checking, synthesis).

## Files

- `minikanren.nim` — the miniKanren engine: substitutions, logic variables,
  `==` unification, `conde` disjunction, interleaving search. Includes
  disequality (`=/=`), `setEqo` global constraints, and finite-domain
  propagation (the Sudoku work).
- `unify.nim` — first-order unification with occurs check; `zonk` (substitute
  solved metas) and `zonkHead`; `renameAt` (capture-avoiding renaming).
  Note: `zonk` operates on Eponym `Term`s and must preserve binder
  quantities (Issue #64 fix).
- `rel_elab.nim`, `rel_elab_dep.nim`, `rel_elab_out.nim` — the elaborator
  specified as a relation (`elabo`), run forwards for checking and
  backwards for synthesis. The subject of Issue #26 (staging the relational
  elaborator) and Issue #57 (direct codegen alternative).
- `rel_interp.nim` — relational interpreter (`evalo`): run forwards to
  evaluate, backwards to synthesize programs.
- `specialized_engine.nim` — a specialized search engine for the elaborator
  relation (alternative to the general miniKanren search).

## Design notes

- **Fair search**: the engine uses interleaving (not DFS) so that
  disjunctive branches don't starve — this fixed the backward `typeo`
  starvation in Track C.
- **Staging target**: these relations are what `src/staging/` specializes.
  The relational definitions stay clean and declarative; performance comes
  from staging, not from hand-optimizing the relations.
- **Eponym dependency**: `unify.nim`'s `zonk` works on Eponym `Term`s.
  If this becomes an independent library, that coupling needs an interface
  (e.g., a `TermLike` concept or moving `zonk` to the eponym side).
