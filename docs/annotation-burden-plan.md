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

## Status
Corpus selection done; porting not yet started (next step).
