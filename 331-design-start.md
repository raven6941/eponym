# #331 design start (Phase 3: linearity-exploiting backend / DPS)

Claimed 2026-10-22 ~02:49 UTC. Worktree: `~/workspace/eponym-331-dps`,
branch `331-phase3-dps` off main @ 33de28a (post-#330 Phase 2 v3 merge).

## Starting facts

- **Quantities reach codegen.** `src/eponym/codegen.nim` already imports
  `Quantity` from `preterm` and threads `piQuantities: seq[Quantity]`
  (line 91, 153, 1606) through `compileDefProcRepr` / per-eliminator
  compilation. q0 binders are erased before codegen (`eraseQ0Arguments`),
  but quantity-1 survives on Pi types — so the "which binders are linear"
  signal is available without new plumbing.
- **Phase 2 v3 landed the collection tier** this run can build on:
  `repSeq` (`Vec`/`List` as `seq[int]`), `repOption` (`Option[int]`),
  right-to-left folds for `vecElim`/`listElim`, entry length checks for
  `Vec A n` params.
- **#67 reversal trigger (2)** is the standing tripwire: if DPS needs a
  CPS or ANF normal form that `Term` cannot express, introduce a
  *stage-local* IR at the erasure→codegen boundary — do not re-layer
  elaboration. First design task is to decide whether the trigger fires.
- **#248** (the "parked prototype" this issue implements) is design text
  only — no prototype code exists in the repo (no DPS branches, no code
  behind the issue). Treat it as motivation, not as something to revive.

## Candidate first targets (to validate next run)

1. `vappend`/`lappend` chains where the accumulator is quantity-1:
   destination-passing concat (`result = a; result.add(b)` in place)
   instead of `@[x] & xs` allocation per cons.
2. Single-use `seq` threads through `vmap`/`lmap`: reuse the input buffer
   as the destination when the input binding is linear and dead after.
3. `Option` is probably not worth DPS (already 264x; allocation is one
   word) — leave it.

## Open design questions

- Does destination-passing need ANF? The Phase 2 eliminator compilers
  emit nested Nim expressions inline; threading a destination through
  them may need let-binding of intermediate results — check whether that
  is expressible as emitted Nim AST without a new term IR (likely yes:
  the "IR" is the Nim AST itself, which codegen already builds).
- Soundness hook: linearity is *checked* (usage_check), so reuse is
  justified by the quantity annotation — but the repr boundary must
  confirm the quantity the *type* claims matches the *term* compiled
  (same discipline as the wrapper identity boundary in Phase 2 v3).
- Benchmark framing stays #19: Phase 3 vs Phase 2 compiled output, never
  vs the interpreter.

## Next step

Prototype DPS on `vappend` in the worktree: hand-compile the
quantity-1 accumulator case, differential-test against interpreter +
Phase 2 twin, and only then decide the trigger question.
