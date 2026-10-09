# Differential soundness fuzzing for staged relations (issue #29)

`src/staging/fuzz_soundness.nim` is the standing net for the `stageGoal`
partial evaluator: a seeded generator produces goals, each goal runs
against (a) the unstaged relational engine and (b) the `stageGoal`-derived
residual, and the reified answer sets must agree (order-insensitive,
logic-var ids canonicalized). Staging is exactly the transformation that
silently changes semantics — a wrong pruning rule is a *wrong-code* bug,
not a crash — so the suite asserts answer-set agreement, not just
success/failure.

## Usage

Fixed-seed suite (CI pins seed 424242, 1000 goals):

```
nim c -r --path:src src/staging/fuzz_soundness.nim -- --seed 424242 -n 1000
```

Fresh-seed fuzzing (local exploration):

```
nim c -r --path:src src/staging/fuzz_soundness.nim -- --seed random -n 5000
```

Exit 0: all compared goals agree. Exit 1: a divergence was found (or a
fixed regression goal failed) — the report includes the goal shape, the
unstaged vs staged answers, a shrunk minimal case, and the seed/iteration
to reproduce.

## What it covers

Five goal shapes, picked per-iteration by the seeded RNG:

1. **typeo-check**: random STLC+Nat term + context, `typeo(tm, nat, ctx)` —
   unstaged `rel_elab.typeo` vs the `stageGoal`-specialized checker
   (ty=nat static, mirroring `bench_typeo`).
2. **typeo-synth**: same, but the type is a logic var — compares reified
   type answer sets against the fully-dynamic staged synthesis variant.
3. **typeo-partial**: `typeo(app(lam(0), q), nat, ctx)` with `q` ranging
   over a small finite domain (one candidate ill-typed) — a logic var in a
   checkable position flowing through the staged app/lam branches.
4. **evalo**: random zero/suc/add term — unstaged `rel_interp.evalo` vs the
   staged evaluator (with `addo` in the relation environment).
5. **rule-level**: small generated `RelGoal`s over the staging rules —
   head-constructor unifications, nested bindings, recursive calls through
   helper relations, `=/=`, `setEqo`, `branch`, disjunction reification,
   and `rgFresh` binder scoping (including sequential same-name binders).

Before the random suite, a fixed regression set runs: the divergences the
fuzzer has found so far, pinned as deterministic goals (see below).

## Reading the output

- `compared`: goals where both sides fully enumerated their answers.
- `capped (inconclusive)`: a side hit the answer cap before enumerating —
  not agreement, not divergence. (Iterative deepening mints fresh var ids
  per depth, so the harness canonicalizes `?v<id>` and dedups *after*
  canonicalization; `capped` now means "genuinely many distinct answers".)
- `divergences`: staged/unstaged answer sets differ — always a bug (or a
  wrong expectation in the harness).

On divergence the goal is shrunk by greedy delta debugging (structural
term shrinking, context shrinking, subgoal elimination for rule goals) and
the minimal case is printed with a `--seed`/`iter` reproducer.

## Bugs found

1. **2026-10-09 — `rgFresh` env pollution** (`src/staging/stagegoal.nim`):
   the binder's placeholder is staging-local, but `stageGoal` staged the
   body in the *shared* env, so the inner binding leaked to siblings —
   `(fresh u. u==zero) ∧ (fresh u. u==suc(zero))` staged to `Fail` although
   satisfiable. Fix: hide any outer binding for the binder's name while the
   body is staged; drop the body's binding for it afterwards. Outer
   bindings learned inside the body still propagate.
2. **2026-10-09 — disjunction commit dropped runtime answers**
   (`src/staging/stagegoal.nim`, `rgDisj` case): when one branch staged to
   `Done` with no observable bindings, the stager returned `Done`,
   discarding the other branch — but `disj(isZero(y), true)` must still
   yield `y=zero` at runtime. Fix: keep `disj(succeed, other-residual)`
   (both-`Done` still collapses to `Done`). This is the same bug class as
   the earlier "no unsound disjunction commit" fix (d248c91), one step
   further: even a binding-free `Done` branch may not commit, because the
   *other* branch contributes answers.

Both are pinned in the fixed regression set (`seq-binders`,
`nested-shadow`, `disj-keep-both`, `fresh-propagates-outer`).

## Limitations

- The staged `evalo` covers zero/suc/add only (`evaloData` on main has no
  `mul` branch); the generator covers exactly the staged fragment.
- Per-goal cost is bounded by search depth/answer cap rather than a
  wall-clock timeout; every goal terminates, but a pathological goal could
  still be slow (the suite reports ms/goal).
- The legacy hand-staged prototypes (`staged_synth`, `staged_codegen`,
  `staged_fwd`) are different relations, not `stageGoal` residuals, and
  are out of scope for this suite.
