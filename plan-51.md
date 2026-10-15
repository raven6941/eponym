# Issue #51: `by smt` handler — plan (WIP, branch exp51-by-smt)

## Design (from notes/solver-backed-elaboration.org + #41 pattern)

`by smt` is a ConvHandler installed with dynamic scope, following the
natArithHandler shape: serialize open Nat goals to SMT-LIB v2, shell out
to a solver binary, `unsat` => discharge (trusted, F*-style), anything
else => decline. `coreValid = false`: the handler extends trust to the
external solver — the bought failure mode is solver brittleness
(timeouts, version sensitivity), documented in trust-model.md.

## Key decisions

1. **Optional dependency, mock seam for tests.** z3 is NOT installed on
   this VM and CI must not require it. The handler takes `solverCmd`
   (default "z3") and `timeoutMs` (default 5000); tests inject a fake
   solver script. Solver failure / timeout / non-unsat => `cvDeclined`,
   never a hang. Env override `EPONYM_SMT_SOLVER` for manual runs.
2. **Translation scope.** Equalities AND inequalities over
   zero/suc/add, plus mul where the translation is sound. Nat maps to
   SMT Int with `(>= x 0)` per variable; `suc n` => `(+ n 1)`.
   Soundness note: nonlinear Int arithmetic is undecidable in general;
   we pass the goal as-is and let the solver decide — a "sat" or
   "unknown" is a decline, never a discharge. Discharge only on
   literal `unsat`.
3. **Goal shape.** Reuse `isEqSpineGoal(a, b, eqId)` for Eq goals.
   Inequalities (`add n m >= n`) need a surface form — INVESTIGATE:
   is there a `NatLe`/`<=` in the prelude or Bool-valued goals? Check
   lib/nat.ep and how `by arith` tests express inequalities. If no
   surface form exists, the inequality half may need a small prelude
   addition or be deferred with a documented boundary.

## Steps

1. Investigate inequality surface syntax (lib/nat.ep, existing `by
   arith` corpus).
2. Implement `smtLibOfGoal(a, b, ...)` serializer: collect free vars
   from the goal spine, emit declarations + nonneg asserts + negated
   goal.
3. Implement `smtHandler(globals, s, solverCmd, timeoutMs)`:
   osproc with timeout, parse first line of stdout, map to
   cvDischarged/cvDeclined.
4. Corpus: >= 3 goals `by arith` declines but the solver proves
   (nonlinear distributivity like `add (mul n m) (mul n k)` vs
   `mul n (add m k)`; inequalities), negative tests (false goals =>
   clean elaboration error), wall-clock per goal recorded.
5. decisions.org entry + trust-model.md note (solver brittleness).

## Status

Claimed in-progress 2026-10-15; branch exp51-by-smt. No code yet —
next run starts at step 1.
