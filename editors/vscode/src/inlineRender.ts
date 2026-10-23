// Pure 2D rendering for the inline shed view (issue #221). vscode-free so
// the headless node smoke test can exercise the exact text Aaron would see
// in the editor region: Epigram lineage, plain text with box-drawing
// characters.

import { BoxJson } from "./protocol";

/** Render a BoxJson as multi-line Epigram-style 2D text.
 *  `pad` is the left padding (spaces); the caller draws the outer frame. */
export function boxToText(b: BoxJson, pad = ""): string {
  const lines: string[] = [];
  // The server may omit empty arrays (older binaries); never crash on a
  // partial box — treat missing fields as empty.
  const holeIds = b.holeIds ?? [];
  const premises = b.premises ?? [];
  const children = b.children ?? [];
  const header = b.header ?? [];
  const ruleLabel = b.ruleLabel ?? "";
  const holeGoal = b.holeGoal ?? "";
  const isHole =
    holeIds.length > 0 && premises.length === 0 && children.length === 0;

  // Header lines (context entries)
  for (const h of header) {
    lines.push(`${pad}${h}`);
  }

  // Premises above the rule line (deduction style)
  if (premises.length > 0) {
    for (const p of premises) {
      lines.push(...boxToText(p, pad + "  ").split("\n"));
    }
  }

  // Horizontal rule separating premises from conclusion
  if (premises.length > 0 || ruleLabel) {
    const label = ruleLabel ? ` ${ruleLabel}` : "";
    lines.push(`${pad}${"─".repeat(30)}${label}`);
  }

  // Conclusion below the rule
  if (b.conclusion) {
    lines.push(...boxToText(b.conclusion, pad + "  ").split("\n"));
  }

  // Children (side-by-side sub-deductions become stacked in text)
  for (const c of children) {
    lines.push(...boxToText(c, pad + "  ").split("\n"));
  }

  // Hole: empty box displaying the goal type. Match the source notation.
  if (isHole) {
    const goal = `?${holeIds[0]} : ${holeGoal}`;
    lines.push(`${pad}┌${"─".repeat(goal.length + 2)}┐`);
    lines.push(`${pad}│ ${goal} │`);
    lines.push(`${pad}└${"─".repeat(goal.length + 2)}┘`);
  }

  if (lines.length === 0 && holeGoal) {
    lines.push(`${pad}? : ${holeGoal}`);
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
    opts.showButtons ? "[refine] [case-split] [give] [intro]".length + 2 : 0
  );
  const bar = (s: string) => `│ ${s}`.padEnd(width + 1) + "│";
  out.push(`┌─ ${shedName} ${"─".repeat(Math.max(0, width - shedName.length - 4))}┐`);
  for (const ln of boxToText(box).split("\n")) {
    out.push(bar(ln));
  }
  out.push(`├${"─".repeat(width)}┤`);
  if (opts.showButtons) {
    out.push(bar("[refine] [case-split] [give] [intro]"));
  }
  // Advisory keybinding line (always shown, uneditable)
  out.push(bar(opts.keyHints));
  out.push(`└${"─".repeat(width)}┘`);
  return out.join("\n");
}
