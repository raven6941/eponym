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
import { LspClient } from "./protocol";
import { pageHtml } from "./render";
import { generateSidecar, hasShedBlocks, eponymRepoRoot } from "./sidecar";

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
  shedName: string;
  refresh: () => Promise<void>;
}

const openPanels = new Map<string, ShedPanel>(); // docUri -> panel
let out: vscode.OutputChannel;

async function ensureSidecar(doc: vscode.TextDocument): Promise<boolean> {
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

  // Issue #153: editing a shed block and saving refreshes the webview.
  // Only fires for documents that already have a shed panel open, so
  // ordinary Nim files are never compiled as a side effect of saving.
  ctx.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(async (doc) => {
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

      // A panel is already open for this document: reveal and refresh it
      // (its sidecar may have changed since it was last rendered).
      const existing = openPanels.get(docUri);
      if (existing) {
        existing.panel.reveal(vscode.ViewColumn.Beside);
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

      const shedName = await vscode.window.showInputBox({
        prompt: "Shed name (from shedsBlock)",
        placeHolder: "e.g. quadBody",
      });
      if (!shedName) return;

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
      const refresh = async () => {
        try {
          const layout = await client.shedLayout(docUri, shedName);
          panel.webview.html = pageHtml(JSON.stringify(layout), shedName);
        } catch (e) {
          panel.webview.postMessage({ cmd: "actionmsg", text: "layout error: " + String(e) });
        }
      };
      panel.webview.onDidReceiveMessage(async (m: any) => {
        try {
          if (m.cmd === "refine" || m.cmd === "give") {
            // Issue #137: the server owns the whole refine round-trip --
            // it fills the hole in the macro-recorded generated source,
            // refreshes statuses, and rewrites the sidecar. The client
            // splices the returned term over the single-line `![...]`
            // node at (nimLine, nimCol) so the .nim source advances.
            const res = await client.refineShed(docUri, shedName, m.term ?? "");
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
      openPanels.set(docUri, { panel, client, shedName, refresh });
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
