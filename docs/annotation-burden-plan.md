# Issue #103: annotation-burden measurement — corpus selection plan

## Corpus (to port)
A small STLC fragment, self-contained, exercising Pi/Sigma/Id + data decls:
1. `corpus103/stlc_syntax.ep` — untyped lambda-calculus terms (Var/Nat lit/App/Lam)
   over de Bruijn indices; exercises data declarations + Vec/Fin-style indices.
2. `corpus103/stlc_types.ep` — types (TNat, TArr); simple, checks Pi/Sigma usage.
3. `corpus103/typing.ep` — the typing judgement as an inductive family
   `HasType : Ctx -> Tm -> Ty -> ?` (exercises indexed families + Id for context
   lookups).
4. `corpus103/metatheory.ep` — 2-3 lemmas (weakening or substitution lemma
   statement + proof skeleton); this is where annotation burden bites.
5. Existing `lib/nat.ep` + `lib/list.ep` as the prelude (not counted in the
   burden — shared infrastructure).

3-5 new files, hand-checkable. Deliberately NOT porting SF verbatim: the deltas
(idiomatic Agda/Lean style → Eponym style) are themselves the finding (#103
step 2), so record each delta in this file as encountered.

## Measurement protocol
- Total tokens vs annotation tokens, per file:
  - annotation tokens = explicit type ascriptions, quantity annotations,
    explicit implicit applications/args, and `the`-style casts.
  - counted with a small script (tokenizer on surface syntax), not by hand.
- Count elaboration failure sites that required human repair (record each).
- Baseline discipline: Dunfield & Krishnaswami "annotations only at redexes"
  is the reference — every annotation NOT at a redex is a candidate elaboration
  improvement (feeds #56 pre-unification / #84 qty inference follow-ups).

## Status (2026-10-15)

Corpus ported: `examples/ep/corpus103/` (4 files, all elaborate end-to-end).
Placed under `examples/ep/` rather than repo-root `corpus103/`;
`tests/run_examples.nim` uses non-recursive `walkDir`, so the corpus does
not enter the CI matrix — the measurement runner is the documented script
(`tools/annotation_burden.py`), per the acceptance criteria.

### Baseline measurement

`python3 tools/annotation_burden.py examples/ep/corpus103/`:

| file | total | annot | ratio |
|---|---|---|---|
| stlc_syntax.ep | 48 | 0 | 0.000 |
| stlc_types.ep | 25 | 0 | 0.000 |
| typing.ep | 257 | 0 | 0.000 |
| metatheory.ep | 618 | 49 | 0.079 |
| TOTAL | 948 | 49 | 0.052 |

All 49 annotation tokens are `proc` return-type ascriptions (16+11+10+10
across the four procs, counted by the script as `:` plus the return-type
tokens). Zero term ascriptions, zero quantity annotations, zero `the`
casts. The two weakening proofs needed no rewriting: `append` on `cons`
reduces definitionally by iota, so the `here`/`there`/`tAbs` cases checked
up to conversion.

### Deltas: Agda/Lean idiom -> Eponym (each a candidate follow-up issue)

1. `lam` is a reserved surface keyword (the lambda introducer); the
   object-language constructor had to be renamed to `abs` (and `tLam` to
   `tAbs`). In Agda `lam` is a legal constructor name. Recorded in
   `examples/ep/corpus103/FAILURE_SITES.md`.
2. Imports resolve relative to the importing file; the deeper
   `examples/ep/corpus103/` directory needs `../../../lib/...` where
   `examples/ep/` files use `../../lib/...`. Authoring repair only.
3. Indexed families with all indices in the header
   (`data Lookup : List Ty -> Nat -> Ty -> ?`) worked as in Agda; the
   generated eliminator's motive binds every index plus the family value,
   and non-recursive constructors of *other* families (`p : Lookup ...`
   in `tVar`) correctly get no induction hypothesis.

### Failure sites

2, both parse-level (see FAILURE_SITES.md). Elaboration failures after
parsing: none.
