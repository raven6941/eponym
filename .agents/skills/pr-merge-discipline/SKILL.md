---
name: pr-merge-discipline
description: Use when claiming an issue, opening or reviewing a pull request, or merging in this repo. Covers the in-progress label claim rule, worktree usage, the CI matrix as single source of truth, the merge gate, squash policy, and PR review conduct (nits as specific comments).
---

# PR and merge discipline

## Claiming work

- The `in-progress` label is the shared claim between agents. Before
  starting an issue, check its labels. If it carries `in-progress`, it
  is claimed: do not work it, do not open a competing branch or PR,
  regardless of how recent its commits are.
- Add the label as the first step of starting an issue; remove it when
  the issue is closed or you discontinue the work. Do not leave stale
  labels — other agents use them to detect stalled work.
- Feature branches merge via pull requests, squashed at merge time.
  Main history stays coarse-grained and readable; the PR branch keeps
  the fine-grained history.
- Use git worktrees for parallel branches (`~/workspace/eponym/` is
  always `main`; each experiment branch gets its own worktree) rather
  than switching branches in one checkout.

## The CI gate

- The CI matrix lives in `tools/ci-local.sh` — the single source of
  truth. `.github/workflows/ci.yml` just calls it. Run
  `sh tools/ci-local.sh` locally before opening a PR; never reconstruct
  the matrix from the YAML or guess which suites are "affected".
  Rendering, error-text, and pretty-printing changes have broken demos
  and examples that only the full matrix caught.
- Confirm compile and tests are healthy **before every commit**, not
  just before merge. A commit that breaks the build is a liability even
  on a branch.
- Keep the build warning-clean. A new "imported and not used" warning
  is a sign of dead code or a missed cleanup; fix it in the same commit.
- When a type changes (new field, renamed proc), grep for all
  construction and call sites before committing; CI should not be the
  first to find them.
- One matrix quirk: `src/eponym/lsp.nim` is a stdio JSON-RPC server;
  compile it with plain `nim c`, never `nim c -r` (which blocks on
  stdin).
- **Merge gate: never merge a PR with failing or pending CI.** Wait
  for green, then squash-merge. Merging red has broken main before.

## Review conduct

- When a review has nits, express each one as a specific comment on
  the PR itself. A verdict of "ship-with-nits" must name its nits on
  the PR; if no specific concerns remain, the verdict is "ship".
  A verdict change (e.g. needs-work → ship-with-nits) without stated
  concerns is not acceptable — the author must be able to find the
  reasons where the verdict is.
- No noise comments for clean PRs.
- This GitHub account is shared between agents: sign your issue and PR
  comments so authorship is attributable, and when closing a PR
  without merging, post a comment with the reasoning.
- Record consequential design decisions in `decisions.org` and update
  `PLAN.md` in the same merge when a branch changes the architecture.
