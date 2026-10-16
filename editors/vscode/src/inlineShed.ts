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
  /** 0-based line where the `![...]` sits; view is inserted below it. */
  anchorLine: number;
  /** Number of inserted view lines. */
  viewLineCount: number;
  /** Editor holding the insertion (for removal). */
  editor: vscode.TextEditor;
  /** Exact text we inserted (to recognize our own change events). */
  insertText: string;
}

let expanded: ExpandedShed | null = null;
let cursorListener: vscode.Disposable | null = null;
let docChangeListener: vscode.Disposable | null = null;

async function clearExpanded(): Promise<void> {
  if (expanded) {
    const { editor, anchorLine, viewLineCount } = expanded;
    expanded = null;
    // Delete the inserted lines: from start of first inserted line to
    // start of the line after the last inserted line.
    const delRange = new vscode.Range(
      new vscode.Position(anchorLine + 1, 0),
      new vscode.Position(anchorLine + viewLineCount + 1, 0)
    );
    try {
      await editor.edit((eb) => eb.delete(delRange));
    } catch {
      // Editor may be closed; ignore.
    }
  }
  if (cursorListener) {
    cursorListener.dispose();
    cursorListener = null;
  }
  if (docChangeListener) {
    docChangeListener.dispose();
    docChangeListener = null;
  }
  vscode.commands.executeCommand("setContext", "eponym.shedExpanded", false);
}

/**
 * Collapse when the cursor leaves the expanded region entirely.
 * Movement INTO the inserted region (anchor line through anchor+viewLineCount)
 * does NOT collapse — per Aaron's 2026-10-15 feedback. The region is real
 * document text, so the cursor can move into it with keyboard commands.
 */
function onCursorChange(e: vscode.TextEditorSelectionChangeEvent): void {
  if (!expanded) return;
  if (e.textEditor.document.uri.toString() !== expanded.docUri) {
    void clearExpanded();
    return;
  }
  const line = e.selections[0].active.line;
  const lo = expanded.anchorLine;
  const hi = expanded.anchorLine + expanded.viewLineCount;
  if (line < lo || line > hi) {
    void clearExpanded();
  }
}

/**
 * If the user edits the inserted view text (or the anchor line), collapse
 * to avoid corrupting the tracked range. Edits elsewhere are fine.
 * Our own insert/delete changes are recognized by content and ignored
 * (no racy timeout flags — the web extension host delivers change events
 * asynchronously after the edit promise resolves).
 */
function onDocChange(e: vscode.TextDocumentChangeEvent): void {
  if (!expanded) return;
  if (e.document.uri.toString() !== expanded.docUri) return;
  const lo = expanded.anchorLine;
  const hi = expanded.anchorLine + expanded.viewLineCount;
  for (const ch of e.contentChanges) {
    // Ignore our own insertion: empty range at insert position with our text.
    if (
      ch.range.start.line === lo + 1 &&
      ch.range.start.character === 0 &&
      ch.range.end.line === lo + 1 &&
      ch.range.end.character === 0 &&
      ch.text === expanded.insertText
    ) {
      continue;
    }
    // Ignore our own deletion: range covering the inserted lines, empty text.
    if (
      ch.range.start.line === lo + 1 &&
      ch.range.start.character === 0 &&
      ch.range.end.line === lo + expanded.viewLineCount + 1 &&
      ch.range.end.character === 0 &&
      ch.text === ""
    ) {
      continue;
    }
    const s = ch.range.start.line;
    const en = ch.range.end.line;
    // Overlaps [lo, hi]?
    if (s <= hi && en >= lo) {
      void clearExpanded();
      return;
    }
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
  await clearExpanded();
  log("[eponym] expandShed: cleared");

  let client: LspClient | null;
  try {
    client = await getClient(doc);
    log("[eponym] expandShed: client ok");
  } catch (e) {
    log("[eponym] expandShed: getClient failed: " + String(e));
    vscode.window.showErrorMessage(`Eponym: could not start LSP server: ${String(e)}`);
    return;
  }
  if (!client) return; // getClient already surfaced the problem
  const docUri = doc.uri.toString();
  let box: BoxJson;
  try {
    const res = await client.shedLayout(docUri, shedName);
    box = res.box;
    log("[eponym] expandShed: layout ok, box keys=" + Object.keys(box ?? {}).join(","));
  } catch (e) {
    log("[eponym] expandShed: shedLayout failed: " + String(e));
    vscode.window.showErrorMessage(`Eponym: shed layout failed: ${String(e)}`);
    return;
  }

  const keyHints = "r: refine  c: case-split  g: give  (Esc: collapse)";
  const text = renderInlineShed(shedName, box, { showButtons: opts.showButtons, keyHints });
  const viewLines = text.split("\n");
  log("[eponym] expandShed: rendered " + viewLines.length + " lines");

  // Insert the view as real document text below the anchor line.
  // (VS Code's `after` decoration contentText silently drops multi-line
  // content — verified 2026-10-16 — so decorations cannot render the 2D box.)
  const anchorLine = doc.positionAt(at.start).line;
  const insertPos = new vscode.Position(anchorLine + 1, 0);
  const insertText = viewLines.join("\n") + "\n";
  const ok = await editor.edit((eb) => eb.insert(insertPos, insertText));
  if (!ok) {
    vscode.window.showErrorMessage("Eponym: could not insert shed view");
    return;
  }
  log("[eponym] expandShed: text inserted");

  expanded = {
    docUri,
    shedName,
    anchorLine,
    viewLineCount: viewLines.length,
    editor,
    insertText,
  };
  vscode.commands.executeCommand("setContext", "eponym.shedExpanded", true);

  // Collapse on cursor leaving the region, on Escape, on edits to the
  // region, and before save (so the view text never hits the file).
  cursorListener = vscode.window.onDidChangeTextEditorSelection(onCursorChange);
  docChangeListener = vscode.workspace.onDidChangeTextDocument(onDocChange);
}

/** Collapse the inline view (bound to Escape via when-clause). */
export async function collapseShed(): Promise<void> {
  await clearExpanded();
}

/** The currently expanded shed, if any (for action commands). */
export function currentExpanded(): { docUri: string; shedName: string } | null {
  if (!expanded) return null;
  return { docUri: expanded.docUri, shedName: expanded.shedName };
}
