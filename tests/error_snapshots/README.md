# Error-message snapshot corpus (issue #34)

Error messages are the user interface of a typechecker. This corpus pins
down the messages for the common failure modes so regressions in message
quality fail CI like any other regression.

## Layout

- `cases/` — new ill-typed fixtures, one per failure mode not already
  covered by the `*-neg.ep` files under `examples/ep/` (which this suite
  reuses in place; they are also exercised by `tests/run_examples.nim`).
- `snapshots/<stem>.txt` — the blessed expected message for each case,
  with the repo-root absolute path normalized to `<root>`.
- `../error_snapshots.nim` — the runner (lives in `tests/`, next to the
  other suite runners).

## What the suite checks per case

1. The program is actually rejected (an `ElabError` is raised).
2. The message carries a source location (`line L, col C: ...`).
3. The message leaks no elaborator internals: no raw `R123`/`V6`
   refIds or de Bruijn indices, no kernel `:$` application syntax, no
   raw `P0` projection indices.
4. The message matches the blessed snapshot byte-for-byte, so any
   wording change fails CI until deliberately re-blessed.

## Failure modes covered (28 cases)

| Area | Modes |
|---|---|
| Scope | unbound variable |
| Application | too many arguments; `refl` on unequal terms |
| Conversion | dimension/constructor confusion (`noConfusion`), neutral mismatch, DCP, session-type, vector/matrix |
| Metavariables | unsolved hole |
| `red` rules | unknown eliminator in pattern |
| `data` | constructor return not the family; non-strictly-positive domain |
| Tactics | unknown tactic name (lists known tactics); `assumption` with no matching hypothesis (names the goal); `refl` on a non-equality goal (names the goal) |
| Quantities | linear used twice / dropped; erased used |
| Clauses | redundant, nested overlap, missing case |
| Modules | missing import (path normalized) |

## Adding a case

1. Write a `*-neg.ep` fixture that fails for exactly one reason. Keep it
   minimal; one failure mode per file. New fixtures go in `cases/`;
   existing `examples/ep/*-neg.ep` files can be referenced in the
   `cases` table in `tests/error_snapshots.nim` instead of copied.
2. Add a row to the `cases` table with a short failure-mode label.
3. Run from the repo root:
   `nim c -r --hints:off --path:src --path:src/eponym tests/error_snapshots.nim -- --bless`
4. Inspect the new snapshot: the message must have a location, name-aware
   types (no `R123`/`V6`/`P0`/` :$ `), and read as actionable to a new
   user. If it doesn't, fix the message in `src/eponym/` first (see
   `sanitizeKernelMsg` in `elab.nim` for the kernel-leak class), then
   re-bless.
5. Commit the fixture, the snapshot, and the table row together.

## Re-blessing

Run the same `--bless` command after a deliberate message change and
review the diff before committing: a snapshot update is a UX decision,
not a rubber stamp. Never bless to make CI green without reading what
changed.
