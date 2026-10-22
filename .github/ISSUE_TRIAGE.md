# Issue labels and triage

Use labels to show both the kind of work and the strength of evidence behind
research proposals. These are separate questions: `production-path` means the
work directly improves supported Nim or editor use; an `epistemic:` label
describes what has been demonstrated so far.

## Epistemic status

Apply exactly one of these labels to each open research or experiment issue.
Update it when the evidence changes.

- `epistemic: demonstrated` — the issue's claim is supported by checked-in
  tests or shipped behavior at the stated scope. Do not generalize a toy case
  beyond what was tested.
- `epistemic: prototype` — a working partial implementation exists, but the
  issue's broader acceptance criteria remain unmet.
- `epistemic: plausible` — a specific proposal has a known technical basis,
  but this repository has not demonstrated it.
- `epistemic: conjecture` — an open hypothesis or research question without a
  concrete implementation or a sufficiently grounded design.

An open issue is not evidence that Eponym supports the idea. The status is a
statement about evidence, not priority, confidence, or whether the work is
worth doing.

## Work kind

- `production-path` — directly improves supported use of Eponym in real Nim
  programs or editor workflows. This label can coexist with an epistemic
  label when the work is still a prototype.
- `tracking` — coordinates work in linked issues and has no standalone
  implementation acceptance criteria. Do not claim it as an implementation
  task; claim its actionable sub-issue instead.
- `design` — the deliverable is a design decision or document.
- `duplicate` — the issue's mandate is tracked by another open issue; link the
  canonical issue in a comment, then close the duplicate.

Every open issue should have a distinct mandate. Before opening a new issue,
search for an existing issue that already owns the work and add a sub-issue or
acceptance criteria there when appropriate.

## Claiming work

Before starting, check whether the issue already has `in-progress`. Add that
label only when taking an unclaimed issue. When an issue is tracked in the
project board, set its Status to `In Progress` at the same time. Remove the
claim and set Status to `Done` when the issue is completed.

The decision log in `decisions.org` records evidence and conclusions; these
labels make the same evidence discipline visible in the issue list.
