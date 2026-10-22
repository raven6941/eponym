---
name: mistake-retrospectives
description: "Use when a piece of work — yours or another agent's — turns out to have been a mistake: poorly scoped, a limiting decision hidden instead of surfaced, a claim that proves false, a verdict without its reasons. Covers deciding whether the mistake is an instance of a repeatable pattern, and turning the pattern into a skill change via PR so future agents avoid it."
---

# Mistake retrospectives: turn errors into skill changes

When something turns out to have been a mistake, fixing the instance is
only half the response. The other half is asking whether an agent
facing the same situation again would make the same choice — and if a
rule in these skills would change that choice, proposing the rule.

This applies to your own work and to other agents' work equally. Most
shared-account, multi-agent failure modes are missing shared guidance,
not individual carelessness: if another agent's mistake reveals a
decision this repo's agents make inconsistently, that is exactly what
the skill files are for. Encode the pattern, not the blame.

## What counts as a mistake worth a retrospective

- **Mis-scoping**: a narrow technique proof closed as if it were a
  comprehensive feature (see issue-scoping), or a feature attempted
  without enumerating its surface.
- **A hidden limiting decision**: a choice that narrows what later
  work can do — a scope cut, a classification that moves something out
  of a guarantee, a fragment definition — made in passing (a code
  comment, a PR body, a close-out message) rather than surfaced where
  the people and agents it constrains will see it. The decision may
  even be right; hiding it is the mistake.
- **A false or overclaimed report**: a status summary, close message,
  or doc claim that the code or the record contradicts (e.g. a
  close-out claiming docs were caught up when one file was not).
- **Process breaks with consequences**: merging on red CI, a review
  verdict whose nits were never stated on the PR, a claim label left
  stale.

## The procedure

1. **Name the mistake precisely.** What decision, made where, recorded
   where (or nowhere), with what consequence. Until it is stated that
   concretely, there is nothing to learn from.
2. **Separate instance from pattern.** Was this a one-off (fix the
   instance and stop) or an instance of a repeatable failure mode that
   a future agent could walk into again? Only patterns earn skill
   changes.
3. **Test the candidate rule at decision time.** Ask: would this rule,
   loaded by an agent at the moment the original decision was made,
   have changed it? If the rule only makes sense with hindsight, it
   will not fire in the future either — discard it. If it would
   plausibly have blocked legitimate work in other cases, narrow it
   until it wouldn't.
4. **Put the rule where the decision happens.** Prefer editing the
   existing skill whose activity contains the decision (scoping rules
   in issue-scoping, merge rules in pr-merge-discipline) over creating
   a new skill; a rule fires only if the agent loads it at the right
   moment, so it must live behind that moment's trigger description.
   Create a new skill only when no existing skill covers the activity.
5. **Write the rule with its instance.** State the trigger, the
   action, and the concrete historical example. Rules without
   instances drift into slogans and get misapplied; the example is
   what keeps the next agent's judgment calibrated. Keep it terse —
   a skill that bloats stops being read.
6. **Make the PR.** Skill changes go through the same PR discipline as
   code: small, focused, referencing the mistake that motivated them.
   The PR body names the instance and the pattern.
7. **Fix the instance too, if it is still fixable.** A skill PR is not
   a substitute for repairing the actual damage: re-scope the
   mis-scoped issue, surface the hidden decision where it belongs (an
   issue comment, `decisions.org`), correct the false claim. Do both
   in the same response to the discovery.

## Anti-patterns

- Encoding one-off bad luck as a standing rule.
- Rules so broad they tax every future task to prevent one past one.
- Retrospective prose nobody will load: a lesson written in a chat
  log, a daily note, or a PR description instead of the skill file
  that triggers at the relevant moment.
- Re-litigating another agent's past decision instead of improving
  the shared guidance. The deliverable is the rule, not the verdict
  on the person.
