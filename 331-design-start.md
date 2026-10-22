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

---

## Run 2 (2026-10-22 ~03:30 UTC): DPS folds implemented

**Mechanism (refines the "quantity-1 accumulator" plan above).**
`cgReprVecElim`/`cgReprListElim` now recognize the cons-rebuild shape —
cons-case body `cons A idx xHead ih` (Vec) / `cons A xHead ih` (List)
with the tail exactly the accumulator (`ih`, de Bruijn 0) and the head
not mentioning `ih`/`tl` (scope-aware check `termUsesInnerBinder`) —
and compile it to a single preallocated destination (`cgDpsFoldBlock`):
one `newSeq[int](xs.len + acc0.len)`, copy of the initial accumulator
into the tail, then per-iteration `dst[k] = head`. This replaces per-step
`@[x] & acc` allocation: O(n) single allocation + O(n) writes instead of
O(n) allocations + O(n^2) copies. Everything else keeps the old fold.

**Key finding: the transform is quantity-independent.** The destination
is freshly allocated and the initial accumulator is only read, never
mutated, so it is sound for any `ih` quantity — it is NOT gated on q1.
The design note's "quantity-1 accumulator case" assumption was wrong;
the mechanism is better than assumed. The genuinely linearity-gated
refinements (in-place accumulator mutation, input-buffer reuse as the
destination, move instead of copy for the acc0 tail) are follow-ups:
they need the wrapper-boundary aliasing story (a Nim caller can alias a
`seq` passed for a q1 parameter; checked linearity governs Eponym
variables, not Nim refs — the issue's own honest-scope note).

**#67 trigger (2): does NOT fire.** No ANF/CPS IR was needed. The
destination is threaded through emitted Nim AST statements (a block with
`let`/`var`/`for`), which codegen already builds directly; the shape
check is a syntactic predicate on `Term`. The "IR" for DPS is the Nim
AST itself.

**Quantity elaboration findings.**
- Explicit `(1 ih : ...)` on an eliminator case binder is REJECTED:
  `lambda binder quantity q1 does not match the expected quantity
  qOmega from the function type` — no quantity subsumption at the case
  lambda. So case binders cannot be annotated; whatever quantity the
  eliminator's registered type declares is what codegen sees.
- Proc-telescope `(1 xs : Vec Int n)` elaborates fine and composes with
  the DPS emission (`vmapLin` in the test).
- Unannotated single-use binders infer their quantity from uses (#66/#84
  machinery), so the common cons-rebuild cases likely already carry q1
  — but the transform doesn't consult it.

**Differential results** (`tests/test_codegen_phase3_dps_vec.nim`,
`tests/test_codegen_phase3_dps_list.nim`): repr vs interpreter vs
Phase-1 twin agree on all cases, including `vappendDps` (acc0-copy path:
nilC = `ys`), `vmapLin` (explicit q1), `vlenDps` (non-rebuild fallback),
`ldoubleCons` (tail-not-ih fallback). Benchmarks (#19 framing, Phase 3
vs Phase 1 compiled): `vmapDps` 2076.6x (n=50), `vappendDps` 18831.1x
(n=50; Phase-1 side dominated by Value-level `natAdd` per cons step —
the index the repr tier skips as type-level), `lmapDps` (see test).

**Old-vs-new (Phase 3 vs Phase 2 fold emission):** no flag was added —
the DPS emission strictly replaces the old one for the cons-rebuild
shape (same values, better complexity; the old emission stays live as
the fallback for other shapes). The marginal number was measured once
dev-time via `git stash` of the codegen change, same machine, n=200:
`vmapDps` 8.170s → 0.044s per 20k iters (**~186x**); `vappendDps`
1.406s → 0.009s per 2k iters (**~156x**). Consistent with O(n^2)
allocating → O(n) single-allocation.

## Follow-ups (still #331)

- q1-gated in-place refinements: input-buffer reuse for map-like folds,
  move-semantics for the acc0 tail copy. Needs the wrapper-boundary
  copy/aliasing discipline first (Nim-side aliasing vs Eponym q1).
- Conditional-cons folds (filter-like): result length unknown statically;
  `newSeqOfCap(xs.len)` upper-bound destination — sound for any quantity.
- `docs/known-limitations.md` sync per the standing rule (tier/coverage
  facts changed: cons-rebuild folds now compile to DPS).
