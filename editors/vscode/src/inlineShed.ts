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
import { renderInlineShed } from "./inlineRender";
import { shedAtCursor, sidecarPathFor, readSidecarShedNames } from "./sidecar";
import { log } from "./log";

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
    // Debug: log to Eponym output channel via console (visible in devtools)
    // For now, we rely on the caller to check.
    const lenses: vscode.CodeLens[] = [];
    try {
      const text = doc.getText();
      const goalMap = this.goals.get(doc.uri.toString()) ?? new Map();
      // Find `![shedName]` occurrences
      const re = /!\[([A-Za-z_][A-Za-z0-9_]*)(?:\s*,[^\]]*)?\]/g;
      let m: RegExpExecArray | null;
      let count = 0;
      while ((m = re.exec(text)) !== null) {
        count++;
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
            arguments: [m.index],
          })
        );
      }
      // Store count for debugging (accessible via a command if needed)
      (globalThis as any).__eponymLastLensCount = count;
      (globalThis as any).__eponymLastLensDoc = doc.uri.fsPath;
    } catch (e) {
      (globalThis as any).__eponymLensError = String(e);
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
 * `getClient` lazily creates the LSP client for the document; it returns
 * null (after showing an actionable error) when the server binary is
 * missing, so the click path never fails silently.
 */
export async function expandShed(
  editor: vscode.TextEditor,
  getClient: (doc: vscode.TextDocument) => Promise<LspClient | null>,
  opts: { showButtons: boolean },
  atOffset?: number
): Promise<void> {
  const doc = editor.document;
  // CodeLens clicks pass the shed marker's offset (clicking doesn't move the
  // cursor); the Ctrl+Shift+S keybinding passes none, so fall back to cursor.
  const cursorOff = atOffset ?? doc.offsetAt(editor.selection.active);
  const at = shedAtCursor(doc.getText(), cursorOff);
  log("[eponym] expandShed: shedAtCursor -> " + (at ? at.name : "none"));
  if (!at) {
    vscode.window.showInformationMessage("Eponym: cursor is not on a shed");
    return;
  }
  const shedName = at.name;

  // Collapse any existing expansion first
  clearExpanded();

  let client: LspClient | null;
  try {
    client = await getClient(doc);
  } catch (e) {
    vscode.window.showErrorMessage(`Eponym: could not start LSP server: ${String(e)}`);
    return;
  }
  if (!client) return; // getClient already surfaced the problem
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
