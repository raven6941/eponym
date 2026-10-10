# Staging framework (`src/staging/`)

Multi-stage programming for Nim, in the style of BER MetaOCaml and LMS.
Potentially an independent library. The aspiration is a general staging
capability — binding-time annotations, `Rep[T]` for staged values,
`genlet` for let-insertion — of which staged relational programming is
one application (and the staged relational elaborator is one case of that).

## Files

- `framework.nim` — the staging framework core: binding-time annotations,
  `Rep[T]` for staged values, `genlet` (let-insertion via delimited
  continuations, Issue #61).
- `relcompile.nim` — compiles relations to staged code: takes a `RelGoal`
  and produces a specialized procedure. (Relational staging as a client
  of the general framework.)
- `relgoal.nim`, `stagegoal.nim` — goal representations for the relational
  client: `RelGoal` for the unstaged relation, `StageGoal` for the staged
  residual.
- `modes.nim` — mode analysis for the relational client: determines which
  arguments are ground vs. logic variables at staging time, guiding
  specialization.

## Design notes

- **General first, relational second**: like MetaOCaml and LMS, the
  framework should stand on its own as a staging system. Staging a
  relational interpreter is the motivating application (Track C), not the
  definition of the framework. New clients (e.g., staging the ETT
  evaluator directly, Issue #8) should be expressible without touching
  the core.
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
  today is the relational elaborator in `src/relational/`. If split into an
  independent library, the interface would be the staging core (`Rep`,
  `genlet`, binding-time machinery), with relational support as an
  extension.
- **Branching-resolution policy** (Issue #89; Ballantyne et al.
  gather/fallback/later): when staging-time search branches (or returns
  non-ground answers) but the residual must be a single direct-style
  program, each site gets a named policy. `gather` emits one specialized
  residual per staging-time branch; `fallback` gives up specializing and
  emits dynamic code that searches at runtime (`dynElabo` in
  `gen_elabo_full.nim`); `later` residualizes a subgoal opaquely as a
  recursive call instead of inlining it. Current policy table (emitted as
  comments in the generated residual): appRedex = gather + fallback escape,
  consIndex = later, inferD = ground-answer restriction kept by design
  (fallback unsound without an expected type). Measured on the elabo
  fragment: gather explosion factor 1x (ground elaboration is type-unique),
  fallback enables `app(lam,nil)`-style cases at parity with dynamic search.
  Composes with #31 (fallback sites = boundary undecidable statically) and
  #61 (genlet shares code across gathered branches when they multiply).
