---
name: capability-completeness
description: Use when finishing a feature, updating docs, or judging whether a capability is "done". Covers the described + documented + demonstrated standard, the docs-codegen sync rule for docs/known-limitations.md, and what counts as a demonstration (embedded examples with real surface area).
---

# Capability completeness: described, documented, demonstrated

A capability is only complete when all three hold. A merged
implementation with none of them is how known-but-unused results
accrue cost of delay: they exist, nobody can find or trust them, and
later work assumes they were never built.

## The three parts

1. **Described** — the design and its rationale are written down where
   the project keeps them (`decisions.org` for choices, the relevant
   `docs/` page for mechanism), including the trust boundary: what
   Eponym checks, what the host language checks, and what stays
   trusted.
2. **Documented** — user-facing docs match the shipped behavior.
   `README.md`, `docs/known-limitations.md`, and the surface-syntax
   reference must not claim less (or more) than the code does.
3. **Demonstrated** — an embedded example where normal Nim code uses
   the capability through Eponym's checked definitions. Eponym is
   first and foremost an embedded language in Nim; demonstrate through
   embedded examples unless that is strongly infeasible. The
   standalone (`.ep`) grammar and semantics are identical to the
   embedded context's — never maintain separate syntax for the two.

## The docs-codegen sync rule

Any codegen or interop merge that changes runtime behavior,
per-definition tiering/back-end selection, or wrapper/codec coverage
must update `docs/known-limitations.md` **in the same PR**. (A
maintainer note at the top of that file states this rule in the repo.)
Do not defer docs sync "until after the next change" — the README and
known-limitations drifted through an entire codegen phase that way,
and a close-out message then overclaimed the catch-up had happened.
Verify doc claims against the code before writing them; a stale bullet
saying dependent structures "do not yet have typed Nim wrappers"
survived months past the commit that made it false.

## What counts as a demonstration

- The example must have surface area a programmer could reasonably
  mess up without guardrails. A session-types demo whose protocol is
  trivially correct by construction demonstrates nothing; the Paxos
  example replaced it because the value-indexed ticket discipline can
  actually be gotten wrong.
- If a simpler motivating case doesn't need dependent types (it was
  already expressible in ordinary typed code), it is not the headline
  example. Pick the case where the checker earns its keep.
- Examples use the prelude (`lib/bool.ep`, `lib/list.ep`, `lib/vec.ep`,
  `lib/nat_lemmas.ep`) via real `import` instead of redefining standard
  types locally.
- When a merge changes the architecture, update `PLAN.md` in the same
  merge; keep the top-level `README.md` current as experiments evolve.
