# The elaborator's tower (Issue #63)

Tests the Amin–Rompf "Collapsing Towers of Interpreters" claim against the
elaborator's *search* levels: does staging the tower collapse it into a
single Jones-optimal pass, or does search resist staging?

## The tower, level by level

Levels run top (surface) to bottom (term walks). Every level reads and
writes the same `MetaStore` (`src/relational/unify.nim`); the store is the
tower's shared dynamic channel. "Static" = known when staging for a fixed
source program; "dynamic" = depends on the store's runtime contents.

### L3 — surface elaboration: `inferTm` / `checkTm` (`src/eponym/elab.nim`)

The interpreter. Its static input is the preterm tree (the program text).
It dispatches on `pre.kind` and, for each node, generates constraints:
fresh metas for implicit arguments and holes (`freshMeta`), unification
goals (`unifyElab`), and quantity obligations (#66).

- Static: preterm shape; global environment (fully elaborated declarations,
  so each name's type skeleton is fixed); the *kind* of each elaboration
  decision per node (which rule fires is a pure function of the preterm).
- Dynamic: the constraint store contents — which metas are solved, their
  solutions, quantity-variable solutions (`qvarSols`, solved by propagation
  in elaboration order), conversion-handler verdicts (#41: user-installable,
  dynamically scoped), conversion-cache hits (#47: order-dependent).
- State effects: meta creation/solution, qvar solutions, handler
  installation, cache population.

### L2 — implicit insertion: `insertImplicits` (`elab.nim:630`)

The loop `while headTy(ms, fty) is an implicit Pi: apply a fresh meta`.
Its iteration count is the length of the callee's implicit-Pi telescope.

- Static: the implicit-Pi telescope of each global's type — the globals
  are fully elaborated before use, so for a fixed program the telescope
  is determined by the (static) declaration the variable resolves to.
  `resolveVar` is a pure function of name + static globals.
- Dynamic: `headTy` unfolds definitions and *zonks*, following the store;
  if the function's type still contains unsolved metas, the telescope
  length is not determined until later. Each iteration performs a store
  write (`freshMeta`) plus a `subst` of the body.
- So: stageable to the telescope *for programs whose implicit telescopes
  are meta-free at application sites* (the common case); the residual is
  `n` meta creations + applications, with `n` static.

### L1 — unification: `unify` / `solveMeta` (`src/relational/unify.nim`)

The search level proper. Dispatches on `(kind of zonked head a, kind of
zonked head b)`: flex-rigid → `solveMeta` (Miller pattern fragment),
rigid-rigid → structural recursion per `TermKind`, flex-flex → spine
unification, eta cases for lambda vs neutral, noConfusion fast-fail (#80).

- Static: the dispatch table itself (per `TermKind` pair, fixed code);
  the *pure* parts of `solveMeta` — `invertSpine` and `renameAt` are total
  functions of (spine shape, term shape), no store involved.
- Dynamic: `unifyHead`/`zonkHead` follow store solutions, so the *heads
  being dispatched on* are dynamic; the occurs check traverses the actual
  (possibly meta-containing) term; `solveMeta` writes solutions.
- A unifier "staged for a pair of term shapes" is therefore a compiled
  kind-matcher with *residual* store reads/writes: the recursion is
  unrolled, the table lookups and occurs-check traversal remain. Per the
  benchmarking-discipline rule (#26, #53 lessons): a staged unifier that
  still interprets term skeletons is not staged; the fair comparison
  names the residual work — store lookups per node, occurs-check
  traversals, solution writes — which the interpretive unifier does too.

### L0 — walks: `zonk`, `zonkHead`, `subst`, `substSpine`, `renameAt`

Pure traversals, but `zonk`/`zonkHead` follow solution pointers in the
store, so the path taken through a term is dynamic: it depends on which
metas are solved *at the moment of the walk*.

- Static: the traversal structure for a fixed term skeleton (unrollable).
- Dynamic: per-meta `solution.isNil` tests; the substituted terms
  themselves (solutions computed by L1 at runtime).

## The collapse question, precisely

In Amin–Rompf terms, collapse means: stage the tower so that intermediate
levels run in *pass-through mode* — staging commands for L3 are
interpreted directly in terms of L0's staging commands, and only the
top-level program generates code. Here that requires the *store
interactions* to be static: staging must know, for a fixed program,
exactly which metas are created and solved in which order, so the store
threads through the levels as compile-time data rather than residual
state.

**Where the tower plausibly collapses.** For programs elaborated entirely
in the Miller pattern fragment with meta-free implicit telescopes and no
dynamic features: every store write is determined by the preterm +
globals. The four levels are then one interpreter over a static preterm,
and staging the preterm interpreter *is* compiling the program — the
single pass is the #57 direct-style codegen direction. The residual keeps
only what is genuinely dynamic: term data the compiler cannot see (none
for a closed program) — i.e., ideally nothing; the store erases.

**Where search resists.** Each of these makes a store interaction
unpredictable at staging time, forcing the level boundary to stay
residual:

- Quantity variables (#66): `qvarSols` are solved by propagation in
  elaboration order; the order depends on which constraints fire.
- Conversion effect handlers (#41): user-installable, dynamically scoped;
  a handler may *extend* what counts as convertible — the verdict of a
  conversion goal is not a function of the program text.
- Conversion cache (#47): hit/miss is order-dependent; a cache-driven
  fast path changes which work L1 does.
- Non-pattern unification (#56 pre-unification): postpones constraints
  whose solving order is then dynamic.

This is also exactly the boundary #31's binding-time analysis computes:
the static/dynamic fallback split *is* the tower-collapse decision,
per program.

## Empirical plan (from the issue)

1. Corpus: extract real elaboration-time unification problems from the
   existing test suite (`elab.nim` self-tests, `run_examples.nim`,
   `unify.nim` main-module tests) — record (shape-a, shape-b, outcome,
   store-size) per problem.
2. Staged unifier for the pattern fragment: specialize `unify` to a pair
   of term-kind skeletons; wall-clock vs interpretive `unify` on the
   corpus. Name the residual work explicitly; profile surprises.
3. Staged implicit insertion: specialize `insertImplicits` to callee
   telescopes; same measurement.
4. Verdict in `decisions.org`: collapse or resistance, with the mechanism
   — *what stays dynamic and why*. If collapse: compose with #57's
   codegen path. If resistance: file the follow-up naming exactly what
   must change (e.g. constraint-store design) for a second attempt.

## Status

- [x] Tower documented (this file): levels + static/dynamic split
- [x] Corpus of unification problems from the test suite (see below)
- [ ] Staged pattern-fragment unifier + wall-clock comparison
- [ ] Staged implicit-insertion pass + wall-clock comparison
- [ ] decisions.org verdict

## Corpus findings (2026-10-09)

Instrumentation: `unifyShape` + `corpusLog` (`src/relational/unify.nim`,
zero-cost unless compiled with `-d:unifyCorpusLog`); `unifyElab`
(`src/eponym/elab.nim`) records raw and zonked kind-skeleton pairs,
outcome, and store size per elaborator-level problem.
Driver: `bench/corpus_unify.nim` (examples/) writes
`bench/unify_corpus.txt`; elab self-tests (same flag) write
`bench/unify_corpus_elabtests.txt`. Deterministic across runs.

- **986 problems**: 214 from `examples/` + `examples/ep/`, 772 from the
  elab self-tests. 985 ok, 1 fail (the fail is a negative test).
- **Dispatch is overwhelmingly rigid-rigid.** Zonked head-kind pairs:
  `C=C` 600, `R=R` 226, `A=A` 68, `V=V` 43, `P=P` 25 (P conflates tPrim
  with Pi/Si in the one-char summary; full shapes show e.g. `Pi(V,V)`
  and `A(A(R,V),V)` spines). Flex-rigid only **23/986 (2.3%)**
  (`C=?` 12, `R=?` 5, `V=?` 4, `?=` 2); **no flex-flex, no top-level
  eta cases** in elaboration-time problems.
- **Heads are nearly static at L1 entry.** `zonkHead` changes a side's
  shape in only **39/986 (4.0%)** — in 96% of problems the dispatch
  heads are already determined before the store is consulted.
- Store sizes 0–12 metas, median 0 (small test programs; scale-up is a
  follow-up measurement).
- **Limitation**: top-level `unifyElab` problems only; recursive
  subproblems inside `unify` (where solved metas appear mid-traversal)
  are not yet instrumented. The dynamic half of L1 lives there —
  `solveMeta` writes, occurs-check traversals, spine inversions.

Reading for the verdict: a unifier staged to the predicted (zonked)
head-kind pair would hit its fast path ~96% of the time on this corpus,
with the residual being the kind guard + general fallback. The L1
dispatch table — the part the tower doc called dynamic — is empirically
the *least* dynamic part of the search level; what stays genuinely
dynamic is the meta lifecycle inside the recursion (solutions written
by `solveMeta` mid-unification, then followed by later recursive
calls). Next: build the staged pattern-fragment unifier for the top
shape pairs and measure wall-clock vs interpretive `unify`.
