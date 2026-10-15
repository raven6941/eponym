// Pure 2D rendering for the inline shed view (issue #221). vscode-free so
// the headless node smoke test can exercise the exact text Aaron would see
// in the editor region: Epigram lineage, plain text with box-drawing
// characters.

import { BoxJson } from "./protocol";

/** Render a BoxJson as multi-line Epigram-style 2D text.
 *  `pad` is the left padding (spaces); the caller draws the outer frame. */
export function boxToText(b: BoxJson, pad = ""): string {
  const lines: string[] = [];
  const isHole =
    b.holeIds.length > 0 && b.premises.length === 0 && b.children.length === 0;

  // Header lines (context entries)
  for (const h of b.header) {
    lines.push(`${pad}${h}`);
  }

  // Premises above the rule line (deduction style)
  if (b.premises.length > 0) {
    for (const p of b.premises) {
      lines.push(...boxToText(p, pad + "  ").split("\n"));
    }
  }

  // Horizontal rule separating premises from conclusion
  if (b.premises.length > 0 || b.ruleLabel) {
    const label = b.ruleLabel ? ` ${b.ruleLabel}` : "";
    lines.push(`${pad}${"─".repeat(30)}${label}`);
  }

  // Conclusion below the rule
  if (b.conclusion) {
    lines.push(...boxToText(b.conclusion, pad + "  ").split("\n"));
  }

  // Children (side-by-side sub-deductions become stacked in text)
  for (const c of b.children) {
    lines.push(...boxToText(c, pad + "  ").split("\n"));
  }

  // Hole: empty box displaying the goal type (Epigram's shed brackets)
  if (isHole) {
    const goal = `?${b.holeIds[0]} : ${b.holeGoal}`;
    lines.push(`${pad}┌${"─".repeat(goal.length + 2)}┐`);
    lines.push(`${pad}│ ${goal} │`);
    lines.push(`${pad}└${"─".repeat(goal.length + 2)}┘`);
  }

  if (lines.length === 0 && b.holeGoal) {
    lines.push(`${pad}? : ${b.holeGoal}`);
  }

  return lines.join("\n");
}

/** Render the full inline shed view: framed box + action line.
 *
 *  `showButtons` toggles the clickable action line; the advisory keybinding
 *  line is always shown (uneditable), per Aaron's 2026-10-15 requirement. */
export function renderInlineShed(
  shedName: string,
  box: BoxJson,
  opts: { showButtons: boolean; keyHints: string }
): string {
  const out: string[] = [];
  // Width fits the content: max of body lines, buttons, key hints.
  const bodyLines = boxToText(box).split("\n");
  const width = Math.max(
    44,
    ...bodyLines.map((l) => l.length + 2),
    opts.keyHints.length + 2,
    opts.showButtons ? "[refine] [case-split] [give]".length + 2 : 0
  );
  const bar = (s: string) => `│ ${s}`.padEnd(width + 1) + "│";
  out.push(`┌─ ${shedName} ${"─".repeat(Math.max(0, width - shedName.length - 4))}┐`);
  for (const ln of boxToText(box).split("\n")) {
    out.push(bar(ln));
  }
  out.push(`├${"─".repeat(width)}┤`);
  if (opts.showButtons) {
    out.push(bar("[refine] [case-split] [give]"));
  }
  // Advisory keybinding line (always shown, uneditable)
  out.push(bar(opts.keyHints));
  out.push(`└${"─".repeat(width)}┘`);
  return out.join("\n");
}
