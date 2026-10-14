# CPS + delimited continuations — hypothetical plan (recorded, not started)

Date recorded: 2026-10-13. Status: **planned, do not pursue yet** (Aaron).

## Objective

Give Eponym's *object language* delimited continuations (`shift`/`reset`),
as the runtime substrate for algebraic effects — the object-level half of
the effects story whose type-level half is #177 (ambient abilities) and
whose elaboration-time half is #41. Also converges with staging: CPS is
already the chosen staging target (Route A), and shift/reset lets the
specializer stay in direct style (Lawall & Danvy).

## Starting state

- No CPS transform of the object language exists. Route A (explicit CPS)
  decided 2026-10-08, not implemented.
- Only shift/reset *ideas* in the repo: `src/staging/genlet.nim` uses
  delimited-continuation-style let-insertion for code generation.
- #41's handlers are decision procedures without continuations; the code
  is explicit: "realized without algebraic effects."
- Key feasibility fact: **Eponym generates the Nim code**, so a
  whole-program (or selective) CPS transform of Eponym core → CPS core →
  Nim needs no host cooperation.

## Prior art (reviewed 2026-10-13)

Rompf/Maier/Odersky, "Implementing First-Class Polymorphic Delimited
Continuations by a Type-Directed Selective CPS-Transform" (ICFP 2009).
Notes: `pages/rompf-delimited-continuations-scala2.org`,
`pages/selective-cps-for-delimited-control.org`.
Revisions it forced on the naive plan are marked [R].

## Plan (7 steps, Rompf-revised)

1. **Selective CPS from the start** [R]. Naive plan said whole-program
   first, selective later; Rompf's evidence says selectivity is
   load-bearing for practicality on a stock runtime, not an
   optimization. Two-pass structure ports directly: selective ANF
   pre-pass, then the CPS transform. Nim macros are AST-to-AST
   natively, so no plugin machinery is needed.
2. **Shift sites are the transform; reset is library** [R]. Only
   `shift` sites need the transform; `reset` (and the shallow handlers
   built on top) can be ordinary functions over the CPS'd core. This
   shrinks the transform surface considerably.
3. **Closure-based continuations first.** Rompf's Shift objects are
   closures and the benchmarks say that's fine. Defunctionalized
   `apply` is the principled refinement for copying/inspecting
   continuations — a representation enabler, not the feasibility gate
   (#53's lesson applies).
4. **Answer types via the light route** [R]. Options, to be compared
   before building: (a) per-expression control effect with Rompf's
   neutral-pure composition; (b) delimited control as an ability in
   #177's ambient-Σ system (Frank-style bookkeeping, membership test
   instead of row unification). Both avoid Koka-style row machinery.
   The deep port — threading answer-type annotations through
   check/infer natively — is available because Eponym *is* an
   elaborator; that is our structural advantage over Scala.
5. **One-shot justified by QTT, not precedent** [R]. Rompf gives no
   one-shot prior art; multi-shot is free under GC (closures
   re-invoke). If one-shot comes first, the motivation is use-once
   continuations checked by the quantity system — our own invention,
   to be argued on its own terms.
6. **Nim-specific day-one constraints** (not later optimizations):
   - *Trampoline.* Nim→C gives no TCO guarantee and CPS builds closure
     chains; the paper's JVM hand-wave does not transfer. Budget for
     a trampoline from the start.
   - *Exception channel.* Adopt Rompf's explicit `Exception => B`
     channel; letting Nim exceptions unwind the native stack would
     skip captured continuations and break multi-shot resumption.
   - *Shift-inside-reset.* Enforce in the macro as a compile-time
     error — simpler than the type system, adequate.
   - *Stack vs heap.* Per Cong et al. 2019 (1st-class vs 2nd-class
     values): don't heap-allocate non-escaping continuations; design
     it in from the start, since Nim makes stack/heap explicit.
7. **Surface syntax + ability integration last.** `shift`/`reset`
   surface forms, with control effects tracked in the #177 ability
   system; then Frank-style shallow handlers on top as the
   user-facing algebraic-effects layer.

## Explicit non-goals for this plan

- Staging's Route A whole-program CPS is a *separate* objective
  (feeds binding-time analysis); the two share machinery but have
  different selectivity requirements. Do not conflate them.
- Anything plugin-shaped: scala-continuations is dormant (2.11/2.12
  only, never ported) — the maintenance tail of compiler-internals
  coupling is the argument for the macro/transform route.

## Decision points (open)

- (4a) vs (4b) for answer types: per-expression control effect vs
  ambient-ability tracking. Compare before building.
- Whether the trampoline can be selective too (only for
  control-effectful code paths).
- How the CPS'd core interacts with the kernel audit (the pure
  fragment must be kernel-audited before shift/reset land).
