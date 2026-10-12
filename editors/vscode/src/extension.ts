// VSCode glue for the Eponym sheds webview (issue #136).
// Thin client: the Nim LSP server is the backend; this extension spawns it
// over stdio, forwards `eponym/shedLayout`, and applies codeAction edits.

import * as vscode from "vscode";
import * as path from "path";
import { LspClient } from "./protocol";
import { pageHtml } from "./render";

function serverPath(): string {
  const cfg = vscode.workspace.getConfiguration("eponym").get<string>("lspServerPath", "");
  if (cfg) return cfg;
  const ws = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  if (!ws) throw new Error("Eponym: no workspace folder open");
  return path.join(ws, "src", "eponym", "lsp");
}

export function activate(ctx: vscode.ExtensionContext) {
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.showShedLayout", async () => {
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        vscode.window.showErrorMessage("Eponym: open a .nim file with sheds first");
        return;
      }
      const shedName = await vscode.window.showInputBox({
        prompt: "Shed name (from shedsBlock)",
        placeHolder: "e.g. myShed",
      });
      if (!shedName) return;
      const docUri = editor.document.uri.toString();
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
      panel.onDidDispose(() => client.shutdown());
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
