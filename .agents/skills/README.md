# Agent skills for this repo

These files are agent skills in the standard `SKILL.md` format (YAML
frontmatter with `name` and `description`, followed by instructions).
They encode this project's working discipline — the lessons that were
previously only in individual agents' private notes — so that every
agent working in this repo makes the same decisions the same way.

| Skill | Covers |
| --- | --- |
| `issue-scoping` | Filing, splitting, and closing issues: technique-proving experiments (narrow scope is correct) vs feature changes (must be comprehensive over the claimed surface). |
| `pr-merge-discipline` | Issue claims, worktrees, squash PRs, the CI matrix and merge gate, review conduct. |
| `benchmarking-discipline` | Fair baselines, first-measurement skepticism, profiling surprising results. |
| `capability-completeness` | "Done" = described + documented + demonstrated; the docs-codegen sync rule. |

To use them, point your agent harness at this directory (or copy /
symlink the skill folders into wherever your harness discovers skills,
e.g. `.claude/skills/` or your Codex skills path). When a lesson is
learned that changes how work should be scoped, reviewed, measured, or
documented here, update the relevant skill in the same PR that teaches
the lesson — a skill that drifts from practice is worse than none.
