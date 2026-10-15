// Inline shed view for issue #221: CodeLens + expandable 2D Epigram-style
// display in the editor region.
//
// Instead of the isolated HTML panel, this keeps interaction text-centric:
// - CodeLens above each `![shedName]` line shows a one-line goal summary.
// - `eponym.expandShed` (keyboard) expands a multi-line 2D view below the
//   line, in Epigram's deduction style: context premises above a rule line,
//   goal below, holes as empty boxes.
// - Cursor movement INTO the expanded region does NOT collapse it; only
//   Escape or cursor moving fully away collapses.
// - Actions are bindable to keyboard shortcuts; buttons can be hidden via
//   config, with an advisory keybinding reminder line.

import * as vscode from "vscode";
import { BoxJson, LspClient } from "./protocol";
import { shedAtCursor, sidecarPathFor, readSidecarShedNames } from "./sidecar";

// ---------------------------------------------------------------------------
// 2D box rendering (Epigram lineage, plain text with box-drawing characters)
// ---------------------------------------------------------------------------

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

/** Render the full inline shed view: framed box + action line. */
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

// ---------------------------------------------------------------------------
// CodeLens provider: one-line goal summaries on `![shedName]` lines
// ---------------------------------------------------------------------------

export class ShedCodeLensProvider implements vscode.CodeLensProvider {
  // Maps document URI -> shed name -> goal (from sidecar, refreshed on save)
  private goals = new Map<string, Map<string, string>>();
  private _onDidChange = new vscode.EventEmitter<void>();
  readonly onDidChangeCodeLenses = this._onDidChange.event;

  /** Refresh goals from the sidecar JSON (no LSP round-trip needed). */
  refreshDoc(doc: vscode.TextDocument): void {
    const names = readSidecarShedNames(sidecarPathFor(doc.uri.fsPath));
    // Goals come from the sidecar's shed entries; fall back to empty.
    const m = new Map<string, string>();
    try {
      const fs = require("fs");
      const raw = JSON.parse(fs.readFileSync(sidecarPathFor(doc.uri.fsPath), "utf8"));
      for (const s of raw.sheds ?? []) {
        if (s.name) m.set(String(s.name), String(s.goal ?? ""));
      }
    } catch {
      // sidecar missing/unreadable: leave empty
    }
    // Ensure every name from the picker has an entry
    for (const n of names) if (!m.has(n)) m.set(n, "");
    this.goals.set(doc.uri.toString(), m);
    // Tell VS Code to re-query provideCodeLenses
    this._onDidChange.fire();
  }

  provideCodeLenses(
    doc: vscode.TextDocument
  ): vscode.CodeLens[] {
    const lenses: vscode.CodeLens[] = [];
    const text = doc.getText();
    const goalMap = this.goals.get(doc.uri.toString()) ?? new Map();
    // Find `![shedName]` occurrences
    const re = /!\[([A-Za-z_][A-Za-z0-9_]*)(?:\s*,[^\]]*)?\]/g;
    let m: RegExpExecArray | null;
    while ((m = re.exec(text)) !== null) {
      const name = m[1];
      const start = doc.positionAt(m.index);
      const line = doc.lineAt(start.line);
      const goal = goalMap.get(name) ?? "";
      const title = goal ? `shed ${name} : ${goal}` : `shed ${name}`;
      lenses.push(
        new vscode.CodeLens(line.range, {
          title,
          command: "eponym.expandShed",
          tooltip: `Expand inline shed view for ${name}`,
        })
      );
    }
    return lenses;
  }
}

// ---------------------------------------------------------------------------
// Expand/collapse management
// ---------------------------------------------------------------------------

interface ExpandedShed {
  docUri: string;
  shedName: string;
  /** 0-based line where the `![...]` sits; view renders below it. */
  anchorLine: number;
  /** Number of lines the decoration occupies (for collapse detection). */
  viewLineCount: number;
  decoration: vscode.TextEditorDecorationType;
}

let expanded: ExpandedShed | null = null;
let cursorListener: vscode.Disposable | null = null;

function clearExpanded(): void {
  if (expanded) {
    expanded.decoration.dispose();
    expanded = null;
  }
  if (cursorListener) {
    cursorListener.dispose();
    cursorListener = null;
  }
  vscode.commands.executeCommand("setContext", "eponym.shedExpanded", false);
}

/**
 * Collapse when the cursor leaves the expanded region entirely.
 * Movement INTO the region (anchor line through anchor+viewLineCount)
 * does NOT collapse — per Aaron's 2026-10-15 feedback.
 */
function onCursorChange(e: vscode.TextEditorSelectionChangeEvent): void {
  if (!expanded) return;
  if (e.textEditor.document.uri.toString() !== expanded.docUri) {
    clearExpanded();
    return;
  }
  const line = e.selections[0].active.line;
  const lo = expanded.anchorLine;
  const hi = expanded.anchorLine + expanded.viewLineCount;
  if (line < lo || line > hi) {
    clearExpanded();
  }
}

/**
 * Expand the inline shed view below the `![...]` at the cursor.
 * `getClient` lazily creates the LSP client for the document.
 */
export async function expandShed(
  editor: vscode.TextEditor,
  getClient: (doc: vscode.TextDocument) => Promise<LspClient>,
  opts: { showButtons: boolean }
): Promise<void> {
  const doc = editor.document;
  const cursorOff = doc.offsetAt(editor.selection.active);
  const at = shedAtCursor(doc.getText(), cursorOff);
  if (!at) {
    vscode.window.showInformationMessage("Eponym: cursor is not on a shed");
    return;
  }
  const shedName = at.name;

  // Collapse any existing expansion first
  clearExpanded();

  const client = await getClient(doc);
  const docUri = doc.uri.toString();
  let box: BoxJson;
  try {
    const res = await client.shedLayout(docUri, shedName);
    box = res.box;
  } catch (e) {
    vscode.window.showErrorMessage(`Eponym: shed layout failed: ${String(e)}`);
    return;
  }

  const keyHints = "r: refine  c: case-split  g: give  (Esc: collapse)";
  const text = renderInlineShed(shedName, box, { showButtons: opts.showButtons, keyHints });
  const viewLines = text.split("\n");

  const anchorLine = doc.positionAt(at.start).line;
  const deco = vscode.window.createTextEditorDecorationType({
    isWholeLine: false,
    after: {
      contentText: "",
      // We render via an after-decoration on the anchor line's end.
      // Multi-line content: join with \n — VS Code renders it below.
    },
  });

  // Use a single after-decoration with the full multi-line text.
  const anchorPos = new vscode.Position(anchorLine, doc.lineAt(anchorLine).text.length);
  const range = new vscode.Range(anchorPos, anchorPos);
  const renderOpts: vscode.DecorationRenderOptions = {
    after: {
      contentText: "\n" + viewLines.join("\n"),
      color: new vscode.ThemeColor("editorCodeLens.foreground"),
      fontStyle: "normal",
    },
  };
  const d = vscode.window.createTextEditorDecorationType(renderOpts);
  editor.setDecorations(d, [range]);

  expanded = {
    docUri,
    shedName,
    anchorLine,
    viewLineCount: viewLines.length,
    decoration: d,
  };
  vscode.commands.executeCommand("setContext", "eponym.shedExpanded", true);

  // Collapse on cursor leaving the region, or on Escape.
  cursorListener = vscode.window.onDidChangeTextEditorSelection(onCursorChange);
}

/** Collapse the inline view (bound to Escape via when-clause). */
export function collapseShed(): void {
  clearExpanded();
}

/** The currently expanded shed, if any (for action commands). */
export function currentExpanded(): { docUri: string; shedName: string } | null {
  if (!expanded) return null;
  return { docUri: expanded.docUri, shedName: expanded.shedName };
}
