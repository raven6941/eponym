// VSCode glue for the Eponym sheds webview (issue #136).
// Thin client: the Nim LSP server is the backend; this extension spawns it
// over stdio, forwards `eponym/shedLayout`, and applies codeAction edits.
//
// Issue #153: the extension owns sidecar generation. The `shedsBlock`
// macro writes `<file>.sheds.json` at macro-expansion time, so opening a
// shed file or saving it (re)compiles it with Nim -- no terminal needed.
// The LSP server is kept pure: it never shells out to a toolchain.

import * as vscode from "vscode";
import * as path from "path";
import * as fs from "fs";
import { LspClient } from "./protocol";
import { pageHtml } from "./render";
import {
  generateSidecar,
  hasShedBlocks,
  eponymRepoRoot,
  shedAtCursor,
  blockShedsAtCursor,
  sidecarPathFor,
  sidecarFresh,
  readSidecarShedNames,
} from "./sidecar";

function serverPath(): string {
  const cfg = vscode.workspace.getConfiguration("eponym").get<string>("lspServerPath", "");
  if (cfg) return cfg;
  const ws = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  if (!ws) throw new Error("Eponym: no workspace folder open");
  return path.join(ws, "src", "eponym", "lsp");
}

function nimBin(): string {
  return vscode.workspace.getConfiguration("eponym").get<string>("nimPath", "nim") || "nim";
}

interface ShedPanel {
  panel: vscode.WebviewPanel;
  client: LspClient;
  shedName: string; // mutable: in-view switching (issue #190) updates it
  shedNames: string[];
  refresh: () => Promise<void>;
}

const openPanels = new Map<string, ShedPanel>(); // docUri -> panel
let out: vscode.OutputChannel;

// Issue #190: pre-fetched layouts, keyed by docUri, tagged with the
// sidecar mtime they were rendered from. Filled in the background when a
// shed file is opened (sidecar fresh); consumed by the command so the
// view opens without waiting on the LSP round-trip.
const layoutCache = new Map<string, { mtime: number; layouts: Map<string, string> }>();

function sidecarMtime(nimFile: string): number {
  try {
    return fs.statSync(sidecarPathFor(nimFile)).mtimeMs;
  } catch {
    return -1;
  }
}

async function prefetchLayouts(doc: vscode.TextDocument): Promise<void> {
  // Eager render, minus the expensive part: measured 2026-10-14, `nim c`
  // (sidecar generation) costs ~9s cold, so we never eagerly *compile*.
  // Pre-fetching layouts is ~0.3ms per shedLayout over stdio, but only
  // trustworthy when the sidecar is already fresh.
  const nimFile = doc.uri.fsPath;
  if (!sidecarFresh(nimFile)) return;
  let client: LspClient;
  try {
    client = new LspClient(serverPath());
    await client.initialize(nimFile.replace(/\/[^/]+$/, ""));
  } catch (e) {
    out.appendLine(`[eponym] prefetch: no LSP server: ${String(e)}`);
    return;
  }
  try {
    const docUri = doc.uri.toString();
    const names = await client.shedNames(docUri);
    const layouts = new Map<string, string>();
    for (const n of names) {
      try {
        layouts.set(n, JSON.stringify(await client.shedLayout(docUri, n)));
      } catch (e) {
        out.appendLine(`[eponym] prefetch: shedLayout(${n}) failed: ${String(e)}`);
      }
    }
    layoutCache.set(docUri, { mtime: sidecarMtime(nimFile), layouts });
    out.appendLine(`[eponym] prefetched ${layouts.size} shed layouts for ${nimFile}`);
  } finally {
    client.shutdown();
  }
}

async function ensureSidecar(doc: vscode.TextDocument): Promise<boolean> {
  // Issue #190: skip the `nim c` rerun when the sidecar is newer than the
  // source — this was the visible pause on "Show shed layout" whenever
  // the file had not changed since the last generation.
  if (sidecarFresh(doc.uri.fsPath)) {
    out.appendLine(`[eponym] sidecar fresh for ${doc.uri.fsPath}, skipping nim c`);
    return true;
  }
  const root = eponymRepoRoot(path.dirname(doc.uri.fsPath));
  if (!root) {
    vscode.window.showErrorMessage(
      "Eponym: could not find the eponym repo (no src/eponym/lsp.nim above this file). " +
        "Open the eponym repo as a workspace folder so the extension can compile shed files."
    );
    return false;
  }
  let ok = false;
  await vscode.window.withProgress(
    {
      location: vscode.ProgressLocation.Notification,
      title: `Eponym: generating shed sidecar (${path.basename(doc.uri.fsPath)})`,
    },
    async () => {
      const res = await generateSidecar(nimBin(), root, doc.uri.fsPath);
      if (res.ok) {
        ok = true;
      } else {
        out.appendLine(`[eponym] sidecar generation failed for ${doc.uri.fsPath}`);
        out.appendLine(res.error ?? "(no output)");
        const show = await vscode.window.showErrorMessage(
          `Eponym: shed sidecar generation failed for ${path.basename(doc.uri.fsPath)} ` +
            "(nim compile error or Nim not on PATH).",
          "Show output"
        );
        if (show === "Show output") out.show();
      }
    }
  );
  return ok;
}

export function activate(ctx: vscode.ExtensionContext) {
  out = vscode.window.createOutputChannel("Eponym");

  // Issue #190: eager pre-render. When a shed file is opened and its
  // sidecar is already fresh, fetch the shed layouts in the background so
  // "Show shed layout" opens without any round-trip. Fire-and-forget: a
  // failure here just means the command takes the live path.
  ctx.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument((doc) => {
      if (doc.languageId !== "nim" && !doc.fileName.endsWith(".nim")) return;
      if (!hasShedBlocks(doc.getText())) return;
      prefetchLayouts(doc).catch((e) =>
        out.appendLine(`[eponym] prefetch failed: ${String(e)}`)
      );
    })
  );

  // Issue #153: editing a shed block and saving refreshes the webview.
  // Only fires for documents that already have a shed panel open, so
  // ordinary Nim files are never compiled as a side effect of saving.
  ctx.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(async (doc) => {
      // The sidecar was just regenerated; any prefetched layouts are stale.
      layoutCache.delete(doc.uri.toString());
      const entry = openPanels.get(doc.uri.toString());
      if (!entry) return;
      if (!hasShedBlocks(doc.getText())) return;
      if (await ensureSidecar(doc)) await entry.refresh();
    })
  );

  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.showShedLayout", async () => {
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        vscode.window.showErrorMessage("Eponym: open a .nim file with sheds first");
        return;
      }
      const docUri = editor.document.uri.toString();

      // A panel is already open for this document: reveal it, then follow
      // the cursor (issue #203). The #190 cursor-aware default only ran on
      // first open; re-invoking the command with the cursor on a different
      // shed re-rendered the old shed. Re-resolve unambiguously from the
      // cursor; otherwise keep the current shed and just refresh.
      const existing = openPanels.get(docUri);
      if (existing) {
        existing.panel.reveal(vscode.ViewColumn.Beside);
        const reText = editor.document.getText();
        const reCursorOff = editor.document.offsetAt(editor.selection.active);
        const reAtCursor = shedAtCursor(reText, reCursorOff)?.name;
        const reInBlock = reAtCursor
          ? []
          : blockShedsAtCursor(reText, reCursorOff);
        const reTarget =
          reAtCursor ?? (reInBlock.length === 1 ? reInBlock[0].name : undefined);
        if (reTarget && reTarget !== existing.shedName) {
          existing.shedName = reTarget;
          if (!existing.shedNames.includes(reTarget)) existing.shedNames.push(reTarget);
          existing.panel.title = `Shed: ${reTarget}`;
        }
        await existing.refresh();
        return;
      }

      if (!hasShedBlocks(editor.document.getText())) {
        vscode.window.showErrorMessage(
          "Eponym: no shedsBlock in this file -- nothing to render"
        );
        return;
      }
      if (!(await ensureSidecar(editor.document))) return;

      // Issue #190: cursor-aware default. With the cursor inside a shed
      // node (`![ name ...]`), open that shed directly — no typing. With
      // the cursor elsewhere in a single-shed block, that shed is the
      // unambiguous choice. Otherwise offer a QuickPick of the file's
      // sheds (read from the sidecar; no LSP round-trip needed), falling
      // back to the free-text box only when the sidecar lists nothing.
      const text = editor.document.getText();
      const cursorOff = editor.document.offsetAt(editor.selection.active);
      let shedName: string | undefined = shedAtCursor(text, cursorOff)?.name;
      if (!shedName) {
        const inBlock = blockShedsAtCursor(text, cursorOff);
        if (inBlock.length === 1) shedName = inBlock[0].name;
      }
      const shedNames = readSidecarShedNames(sidecarPathFor(editor.document.uri.fsPath));
      if (!shedName) {
        if (shedNames.length > 0) {
          const picked = await vscode.window.showQuickPick(shedNames, {
            placeHolder: "Shed (from shedsBlock)",
          });
          if (!picked) return;
          shedName = picked;
        } else {
          const typed = await vscode.window.showInputBox({
            prompt: "Shed name (from shedsBlock)",
            placeHolder: "e.g. quadBody",
          });
          if (!typed) return;
          shedName = typed;
        }
      }
      if (shedNames.length === 0) shedNames.push(shedName);

      let client: LspClient;
      try {
        client = new LspClient(serverPath());
        await client.initialize(editor.document.uri.fsPath.replace(/\/[^/]+$/, ""));
      } catch (e) {
        vscode.window.showErrorMessage("Eponym: could not start LSP server: " + String(e));
        return;
      }
      const panel = vscode.window.createWebviewPanel(
        "eponymShed",
        `Shed: ${shedName}`,
        vscode.ViewColumn.Beside,
        { enableScripts: true }
      );
      const entry: ShedPanel = {
        panel,
        client,
        shedName,
        shedNames,
        refresh: async () => {},
      };
      const refresh = async () => {
        try {
          // Prefer a prefetched layout (issue #190) when it matches the
          // current sidecar; otherwise ask the server live.
          const cached = layoutCache.get(docUri);
          const fresh = cached && cached.mtime === sidecarMtime(editor.document.uri.fsPath);
          const layoutJson =
            fresh && cached.layouts.has(entry.shedName)
              ? cached.layouts.get(entry.shedName)!
              : JSON.stringify(await client.shedLayout(docUri, entry.shedName));
          panel.webview.html = pageHtml(layoutJson, entry.shedName, entry.shedNames);
        } catch (e) {
          panel.webview.postMessage({ cmd: "actionmsg", text: "layout error: " + String(e) });
        }
      };
      entry.refresh = refresh;
      panel.webview.onDidReceiveMessage(async (m: any) => {
        try {
          if (m.cmd === "switch-shed" && typeof m.shedName === "string") {
            // Issue #190: in-view shed switching — no close/reopen.
            entry.shedName = m.shedName;
            if (!entry.shedNames.includes(m.shedName)) entry.shedNames.push(m.shedName);
            entry.panel.title = `Shed: ${m.shedName}`;
            await entry.refresh();
          } else if (m.cmd === "refine" || m.cmd === "give") {
            // Issue #137: the server owns the whole refine round-trip --
            // it fills the hole in the macro-recorded generated source,
            // refreshes statuses, and rewrites the sidecar. The client
            // splices the returned term over the single-line `![...]`
            // node at (nimLine, nimCol) so the .nim source advances.
            const res = await client.refineShed(docUri, entry.shedName, m.term ?? "");
            const line = res.nimLine - 1;
            const startCh = res.nimCol - 1;
            const text = editor.document.lineAt(line).text;
            let depth = 0;
            let endCh = -1;
            for (let i = startCh; i < text.length; i++) {
              if (text[i] === "[") depth++;
              else if (text[i] === "]") {
                depth--;
                if (depth === 0) { endCh = i + 1; break; }
              }
            }
            if (endCh < 0) throw new Error("Eponym: unbalanced shed node at " +
              `${res.nimLine}:${res.nimCol}`);
            await editor.edit((b) =>
              b.replace(new vscode.Range(line, startCh, line, endCh), res.term)
            );
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `refined ${res.shedName}: ${res.status} (${res.yellowCount} yellow left)`,
            });
            await refresh();
          } else if (m.cmd === "case-split") {
            const res = await client.request("textDocument/codeAction", {
              textDocument: { uri: docUri },
              range: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } },
              context: { diagnostics: [] },
              variable: m.variable ?? "",
            });
            await applyCodeActions(res, editor);
            await refresh();
          }
        } catch (e) {
          panel.webview.postMessage({ cmd: "actionmsg", text: "action failed: " + String(e) });
        }
      });
      panel.onDidDispose(() => {
        client.shutdown();
        openPanels.delete(docUri);
      });
      openPanels.set(docUri, entry);
      await refresh();
    })
  );
}

async function applyCodeActions(res: any, editor: vscode.TextEditor) {
  const actions: any[] = Array.isArray(res) ? res : res?.actions ?? [];
  const edit = new vscode.WorkspaceEdit();
  for (const a of actions) {
    const changes = a?.edit?.changes;
    if (!changes) continue;
    for (const [uri, edits] of Object.entries<any>(changes)) {
      for (const e of edits) {
        edit.replace(
          vscode.Uri.parse(uri),
          new vscode.Range(e.range.start.line, e.range.start.character, e.range.end.line, e.range.end.character),
          e.newText
        );
      }
    }
  }
  await vscode.workspace.applyEdit(edit);
}

export function deactivate() {}
