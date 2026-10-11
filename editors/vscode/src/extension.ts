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
            const res = await client.codeAction(docUri, 0, 0, m.term ?? "");
            await applyCodeActions(res, editor);
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
