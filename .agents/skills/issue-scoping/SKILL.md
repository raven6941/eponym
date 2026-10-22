---
name: issue-scoping
description: Use when filing, splitting, re-scoping, or closing an issue in this repo. Distinguishes technique-proving experiments (narrow initial scope is correct) from feature changes (must be comprehensive over the user-visible surface they claim), and gives the filing checklist and closing semantics for each kind.
---

# Issue scoping: experiments vs features

The most expensive scoping mistake in this repo's history was filing a
narrow technique proof under a feature-sized name and then closing it as
if the feature existed. This skill exists so that does not recur.

## The two kinds of issue

### (a) Experiment — proves a technique

An experiment answers a question: *does this mechanism work, under what
conditions, at what cost?*

- A narrow initial set is legitimate and desirable. Proving the technique
  on `int` alone is a good experiment. The narrowness is the point: it
  isolates the mechanism.
- The deliverable is knowledge, including negative results. A negative
  result is a result: close the issue, record the finding, move on.
- Closing an experiment asserts **the question was answered**. It does
  not assert that any user-facing capability exists.
- The issue must name, up front:
  - the question, stated so it can be answered yes/no/with-conditions;
  - the exact initial scope (which types, forms, or cases — by name);
  - the evidence that will count as an answer (differential test,
    benchmark against a named baseline, a compile that succeeds/fails);
  - the uncovered set: what this scope deliberately leaves out, and
    where that remainder lives (a linked follow-up issue, or an explicit
    "deferred, not yet filed" note).

### (b) Feature — changes what users can do

A feature issue owns a user-visible capability: something a user of the
library can rely on.

- A feature must be **comprehensive over the surface it claims**. If
  the capability is "the repr backend compiles definitions", the surface
  is every representation mapping a user can declare — not the three
  kinds the backend happens to honor today.
- The issue must enumerate that surface explicitly, from the code or
  the docs (e.g. the registry of mapping kinds, the term forms, the
  entry points), and its acceptance criteria must cover each enumerated
  element, or explicitly split the remainder into its own feature issue
  that stays open.
- Closing a feature asserts **the surface is covered**: implemented,
  documented (`docs/known-limitations.md` in the same PR — see the
  capability-completeness skill), and demonstrated by an embedded
  example.

## The classification test

Ask: *if this work succeeds perfectly on its stated scope, can a user
rely on the general capability the title names?*

- No → it is an experiment. Title it as one, with its scope in the
  title: "Experiment: repr-specialized codegen on the int fragment",
  not "Representation-specialized backend".
- Yes → it is a feature. Enumerate the surface before starting.
- A multi-phase capability build usually needs **both**: phase issues
  filed as experiments (each proving one technique on a named slice),
  plus one feature issue that owns completeness and stays open until
  the whole surface is covered. Phase numbers are work order, not
  capability levels — never let a phase inherit the feature's name and
  completion semantics.

## Worked example: the Phase 2 repr backend (#330)

#330 was filed under the feature-sized name "Codegen Phase 2:
representation-specialized backend" but scoped to the int fragment
(scalars mapped to `int`, plus `Vec`/`List`/`Option` over int elements).
It closed as "Phase 2 complete". Consequences:

- `requireCompiled()` (#358) was then built and accepted against that
  fragment, so the strict static-path guarantee applied only to
  `int` / `seq[int]` / `Option[int]`.
- The flagship Paxos example uses none of those shapes at its boundary
  (opaque `Promise`, index-erased `Chan`, dependent Sigma) and cannot
  pass strict mode at all — discovered by audit after the fact (#401,
  #402 are the repair issues).

Filed correctly, #330 would have been two issues: an *experiment*
("repr technique: scalars and one collection family over int") whose
closure would have been correct and unremarkable, and a *feature*
("repr coverage for declared representation mappings") enumerating the
mapping registry as its surface, still open today.

## Filing checklist

1. State the value category up front: (a) new capability, (b)
   ergonomics, (c) performance, (d) certainty about proved/certified
   conclusions, (e) internal aesthetics, or (f) pure knowledge.
2. Classify: experiment or feature, using the test above. Say which,
   in the issue body.
3. Experiment: question, named initial scope, success evidence,
   uncovered set, follow-up link or explicit deferral.
4. Feature: enumerated surface, acceptance per surface element,
   documentation and embedded-example requirements, error/negative
   cases.
5. If the other kind of issue is implied (an experiment that would
   leave a feature gap; a feature that needs a technique proven first),
   file it or name it as deferred. Do not let one issue silently do
   double duty.

## Re-scoping and closing rules

- If scope changes mid-flight, re-scope **publicly**: a comment on the
  issue stating the new scope and why. Never silently redefine "done".
- The closing comment must restate the achieved scope in the issue's
  own terms and link whatever remains. "Complete" claims about a phase
  or a slice are how the #330 failure happened.
- Never close a feature issue on experiment evidence.
- When auditing whether something is done, check the claim against the
  flagship example and the enumerated surface, not against the
  implementation's internal progress (chunks merged, suites green).
  A declared-vs-honored gap analysis (what users can declare vs what
  the implementation actually honors) is the reliable way to find the
  real remaining surface.
