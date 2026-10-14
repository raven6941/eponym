# #170 design: lattice-monotone elaboration

## The decision: lattice-state vs Klister-blocking (2026-10-13)

The issue comment (klister re-read) sharpened the choice: Klister blocks the
*task* — continuation captured, task requeued until unification solves the
metavariable — while #170 reifies ambiguity into the *state* so no task ever
blocks. Both are threshold reads over monotone knowledge. The prototype
adopts **both, each where it belongs**:

- **Lattice-state** for all elaboration-*internal* ambiguity (constructor
  choice, index refinement, inferred-vs-expected type equality). The missing
  information is the thing elaboration itself computes; blocking would
  serialize what can be parallel refinement. The state carries the ambiguity
  as possibility sets; everything determined proceeds.
- **Klister-style blocking** retained for **holes**, where the missing
  information's source is *outside* elaboration (the user). A hole is a node
  whose shape never refines past a threshold; the driver reports `Stuck`
  (awaiting external info) as a distinct outcome from `Bottom`
  (contradiction). Blocking = "wait for an external information source";
  lattice = "compute with partial information from internal sources".

In the prototype (ground corpus, no holes/metas) neither mechanism is
stressed, but the state is built so a hole is just a permanently-partial
node — no separate stuck-task machinery needed for the representation, only
for the *resumption* (user input arrives between driver calls).

## The lattice

`src/relational/lattice_elab.nim`. State per node (term/type occurrence):

- `shape`: possibility set over 12 heads (`{hNil..hUniv}`); top = all,
  bottom = empty. Recorded from ground truth at numbering.
- `natl`: NatLat over indices — unknown / exact k / bottom. `zero`,
  `rint(k)`, and `suc`-chains all map into it, so *representations* of the
  same number are already identified.
- Union-find over nodes: `unionEq` meets shapes and natls and, for
  congruent pair constructions, unions kids pairwise (congruence closure —
  the e-node skeleton). **Bottom is detected by the meet, at the step that
  creates it, with provenance** (node, wanted, had). Never by stream
  exhaustion, never by cut.

Rules (`checkLat`/`inferLat`): no `disj`, no logic variables, no streams.
Dispatch on the term's ground head is rule *selection*, not search — exactly
one rule applies, and it only meets. Two deliberate refinements over
`rel_elab_dep`:

1. The spec *rejects* when the expected type isn't syntactically `pi`/`vec`
   (`tagOf` check); the lattice *refines* an unknown type node to
   `{hPi}`/`{hVec}` and materializes its structure (`materialize`). Refine,
   don't reject.
2. `nil`'s `disj(idx == zero, idx == rint(0))` becomes one
   `meetNat(idx, exact 0)` — the representation case-split disappears
   because both spellings are `exact 0` in the NatLat.

## Status

- `tests/test_lattice_elab.nim`: **16/16 verdict agreement** with the
  corpus expectations; accepted outputs rebuilt from the converged state
  (`rebuild`); rejections carry provenance, e.g.
  `bottom at vec#2: wanted suc needs Nat type, had shape {hVec}` (node
  descriptions are O(1) `head#id` — full-subterm rendering made numbering
  O(n²) and was fixed).
- New shared corpus module `src/relational/vec_corpus.nim` (RTerm side of
  the `bench_elab_end_to_end.nim` cases).
- **Benchmark done** (`bench/bench_lattice_elab.nim`, decisions.org
  2026-10-13): invalid-case latency is linear in input size
  (10.7us→125.7us for cons^0..cons^64 : Vec Nat 2) — the step-4 gate
  passes. Staged-relational engine reproduces #143 (16–17x vs direct on
  small invalids, 46.8x on the shape-mismatch case) but is ~flat ~7ms in
  term size: its deficit is a large constant, not size-dependent
  exhaustion. Lattice rejects 7–614x faster than direct, 113–227x faster
  than the engine on small invalids. Honest note: `elaboD` (#57) is the
  fastest rejector outright (1–10us); the lattice's distinctive value is
  the ambiguity-preserving state, which step 5 will test.
- **Synthesis direction done** (step 5, 2026-10-13): `synthLatTop` runs the
  *same* `checkLat` rules backwards — the term node starts at ⊤ and the
  type side saturates it. The `ckNone` branch now refines an unknown term
  from a singleton type head instead of failing. Outcomes are three-valued:
  **Bottom** (rejection with provenance), **accept** (fully determined),
  **Stuck** (partial state — holes awaiting external information, per the
  lattice-state vs Klister-blocking decision above). `rebuildHoles` builds
  the output from the converged state's constructions, emitting `rkVar`
  holes for nodes that never refined past a threshold.
- Step-5 findings (`tests/test_lattice_synth.nim`, 16/16):
  - `synth(Vec Nat 2)` → the spine `cons(?h0, cons(?h1, nil))` is
    *determined* by saturation; the two element unknowns stay holes
    (Stuck, 2 nodes). The relation genuinely runs backwards: no search,
    no branching, one deterministic pass.
  - `synth(Vec Nat 0)` → `nil`, fully determined, nothing stuck.
  - `synth(Vec Nat ?idx)` → nil-vs-cons ambiguity *preserved in the
    state* (`{hNil, hCons}`), no branch taken, reported Stuck — not
    Bottom. This is the multi-direction story surviving: ambiguity is
    data, not control flow.
  - `synth(Nat)` → stuck with `{hZero, hSuc, hNatLit}`: the fragment's
    numeral spellings are all kept, no guessing.
  - Backwards Bottom: term pre-constrained to `{hCons}` + type
    `Vec Nat 0` → contradiction detected *by the meet* with provenance
    (`wanted synth: Vec A 0 inhabitant, had shape {hCons}`) — local
    failure in the backwards direction too.
- Honest notes: output determination (§3) is no longer degenerate —
  `rebuildHoles` is exercised on genuinely partial states. The backwards
  cons case trusts `predIndex`'s structural predecessor (no explicit
  suc-edge in the state); the Vec fragment's dependent-index story stays
  structural, as in the forwards direction. Pi/lam synthesis refines the
  shape to `{hLam}` only — body synthesis against an open codomain is
  future work.

## Honest notes

- On the ground checking-mode corpus, *term* shapes are degenerate
  (singletons from numbering); the lattice work happens on *type* nodes.
  The term-side lattice is infrastructure for step 5 (synthesis): running
  backwards starts from a partial term-shape state and saturates.
- Output determination (§3) is degenerate on ground input (rebuild ==
  input); the mechanism (per-root constructions, congruence-propagated,
  output built from converged state) is in place for the non-ground
  extension. The verdict will say so plainly if it stays degenerate.
