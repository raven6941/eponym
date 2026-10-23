// Inline shed view for issue #221: CodeLens summaries plus a temporary,
// cursor-addressable 2D display inserted below the selected shed marker.
// The preview is removed before saving so it never becomes Nim source.

import * as vscode from "vscode";
import { BoxJson, LspClient } from "./protocol";
import { renderInlineShed } from "./inlineRender";
import { shedAtCursor, shedBlocks, sidecarPathFor, readSidecarShedNames } from "./sidecar";
import { log } from "./log";

// ---------------------------------------------------------------------------
// CodeLens provider: one-line goal summaries on shed marker lines
// ---------------------------------------------------------------------------

export class ShedCodeLensProvider implements vscode.CodeLensProvider {
  // Maps document URI -> shed name -> goal (from sidecar, refreshed on save)
  private goals = new Map<string, Map<string, string>>();
  private _onDidChange = new vscode.EventEmitter<void>();
  readonly onDidChangeCodeLenses = this._onDidChange.event;

  /** Re-query lenses when the inline proof view expands or collapses. */
  refreshCodeLenses(): void {
    this._onDidChange.fire();
  }

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
      // Use the same marker parser as cursor lookup and source splicing.
      const nodes = shedBlocks(text).flatMap((block) => block.sheds);
      for (const node of nodes) {
        const name = node.name;
        const start = doc.positionAt(node.start);
        const line = doc.lineAt(start.line);
        const goal = goalMap.get(name) ?? "";
        const title = goal ? `shed ${name} : ${goal}` : `shed ${name}`;
        lenses.push(
          new vscode.CodeLens(line.range, {
            title,
            command: "eponym.expandShed",
            tooltip: `Show 2D shed layout for ${name}`,
            arguments: [node.start],
          })
        );
      }
      // Store count for debugging (accessible via a command if needed)
      (globalThis as any).__eponymLastLensCount = nodes.length;
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
  /** 0-based source line whose following lines contain the view. */
  anchorLine: number;
  /** Number of temporary view lines inserted after the marker. */
  viewLineCount: number;
  /** Editor holding the insertion (for removal). */
  editor: vscode.TextEditor;
}

let expanded: ExpandedShed | null = null;
let cursorListener: vscode.Disposable | null = null;
let refreshCodeLenses: (() => void) | null = null;

/** Connect inline-view state changes to the CodeLens provider. */
export function setInlineShedRefresh(callback: () => void): void {
  refreshCodeLenses = callback;
}

async function clearExpanded(): Promise<void> {
  log("[eponym] clearExpanded called, expanded=" + (expanded ? expanded.shedName : "null"));
  if (expanded) {
    const { editor, anchorLine, viewLineCount } = expanded;
    // Clear state before editing so resulting editor events cannot recurse.
    expanded = null;
    const delRange = new vscode.Range(
      new vscode.Position(anchorLine + 1, 0),
      new vscode.Position(anchorLine + viewLineCount + 1, 0)
    );
    try {
      await editor.edit((eb) => eb.delete(delRange));
    } catch {
      // The editor may have been closed while the view was expanded.
    }
  }
  if (cursorListener) {
    cursorListener.dispose();
    cursorListener = null;
  }
  vscode.commands.executeCommand("setContext", "eponym.shedExpanded", false);
  refreshCodeLenses?.();
}

/** Remove the preview through VS Code's supported will-save edit mechanism. */
export function removeExpandedForSave(docUri: string): vscode.TextEdit[] {
  if (!expanded || expanded.docUri !== docUri) return [];
  const { anchorLine, viewLineCount } = expanded;
  expanded = null;
  if (cursorListener) {
    cursorListener.dispose();
    cursorListener = null;
  }
  void vscode.commands.executeCommand("setContext", "eponym.shedExpanded", false);
  refreshCodeLenses?.();
  const delRange = new vscode.Range(
    new vscode.Position(anchorLine + 1, 0),
    new vscode.Position(anchorLine + viewLineCount + 1, 0)
  );
  return [vscode.TextEdit.delete(delRange)];
}

/**
 * Collapse when the cursor leaves the expanded region. The inserted rows are
 * real editor text, so the user can move into the view and use its key actions.
 */
function onCursorChange(e: vscode.TextEditorSelectionChangeEvent): void {
  if (!expanded) return;
  if (e.textEditor.document.uri.toString() !== expanded.docUri) {
    log("[eponym] onCursorChange: different doc, clearing");
    void clearExpanded();
    return;
  }
  const line = e.selections[0].active.line;
  const lo = expanded.anchorLine;
  const hi = expanded.anchorLine + expanded.viewLineCount;
  if (line < lo || line > hi) void clearExpanded();
}

/**
 * Expand the inline shed view below the shed marker as temporary editor text.
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

  const keyHints = "i: intro  r: refine  c: case-split  g: give  (Esc: collapse)";
  const text = renderInlineShed(shedName, box, { showButtons: opts.showButtons, keyHints });
  const viewLines = text.split("\n");
  log("[eponym] expandShed: rendered " + viewLines.length + " lines");

  const anchorLine = doc.positionAt(at.start).line;
  const insertPos = new vscode.Position(anchorLine + 1, 0);
  const ok = await editor.edit((eb) => eb.insert(insertPos, viewLines.join("\n") + "\n"));
  if (!ok) {
    vscode.window.showErrorMessage("Eponym: could not insert shed view");
    return;
  }
  log("[eponym] expandShed: text inserted");
  expanded = { docUri, shedName, anchorLine, viewLineCount: viewLines.length, editor };
  vscode.commands.executeCommand("setContext", "eponym.shedExpanded", true);
  refreshCodeLenses?.();

  // Collapse when leaving the view or on Escape.
  cursorListener = vscode.window.onDidChangeTextEditorSelection(onCursorChange);
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
