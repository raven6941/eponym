# Staging framework (`src/staging/`)

Multi-stage programming for the relational engine. Potentially an independent
library. Implements the "towers collapse" idea: a relationally-defined
interpreter, specialized to a given direction and mode, collapses into
direct-style code without the miniKanren overhead.

## Files

- `framework.nim` — the staging framework core: binding-time annotations,
  `Rep[T]` for staged values, `genlet` (let-insertion via delimited
  continuations, Issue #61).
- `relcompile.nim` — compiles relations to staged code: takes a `RelGoal`
  and produces a specialized procedure.
- `relgoal.nim`, `stagegoal.nim` — goal representations: `RelGoal` for
  the unstaged relation, `StageGoal` for the staged residual.
- `modes.nim` — mode analysis: determines which arguments are ground vs.
  logic variables at staging time, guiding specialization.

## Design notes

- **Why staging, not hand-optimization** (Issue #26 lesson): the first
  attempt at staging the relational elaborator via partial deduction was
  11–87x *slower* — it specialized without generating code, producing a
  specialized interpreter rather than a compiler. Aaron's verdict:
  "not evidence against staging, just not complete staging." Issue #57
  (direct codegen) is the response: the residual must be direct-style Nim
  with no `Goal`/`Stream`/unification at runtime.
- **Phase discipline**: the stager runs at compile time (macro expansion);
  the residual is ordinary Nim. This mirrors the Eponym architecture:
  relational/spec work at elaboration time, non-relational IR out.
- **Demos live in `tests/`**: `stage_evalo`, `stage_typeo`, `staged_defun`,
  etc. are demonstrations of the framework, not the framework itself.
- **Eponym dependency**: the framework is generic, but the primary client
  is the relational elaborator in `src/relational/`. If split into an
  independent library, the interface would be `RelGoal` + modes.
