// LSP server binary resolution + pre-spawn validation.
//
// Clicking a shed CodeLens silently did nothing when the server binary was
// missing: `new LspClient(path)` spawns in its constructor, the spawn of a
// nonexistent binary fails asynchronously, and the click handler's promise
// rejected with no user-visible feedback. Every interactive spawn site now
// goes through ensureServerBinary() first, which shows an actionable error
// and returns null so the caller returns early.

import * as vscode from "vscode";
import * as path from "path";
import * as fs from "fs";

export function serverPath(): string {
  const cfg = vscode.workspace.getConfiguration("eponym").get<string>("lspServerPath", "");
  if (cfg) return cfg;
  const ws = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  if (!ws) throw new Error("Eponym: no workspace folder open");
  return path.join(ws, "src", "eponym", "lsp");
}

/** The repo-root build command for the LSP server (matches tools/ci-local.sh). */
export const LSP_BUILD_CMD =
  "nim c --hints:off --path:src --path:src/eponym src/eponym/lsp.nim";

/**
 * Resolve the server binary and verify it exists and is executable.
 * Shows an actionable error message and returns null when unusable —
 * callers must return early (never spawn a missing binary silently).
 */
export function ensureServerBinary(): string | null {
  let p: string;
  try {
    p = serverPath();
  } catch (e) {
    vscode.window.showErrorMessage(`Eponym: ${e instanceof Error ? e.message : String(e)}`);
    return null;
  }
  try {
    fs.accessSync(p, fs.constants.X_OK);
  } catch {
    vscode.window.showErrorMessage(
      `Eponym: LSP server not found at ${p}. Build it from the eponym repo root with: ${LSP_BUILD_CMD} — or set eponym.lspServerPath.`
    );
    return null;
  }
  return p;
}
