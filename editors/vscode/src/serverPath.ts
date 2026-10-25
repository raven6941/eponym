import * as vscode from "vscode";
import * as fs from "fs";
import * as path from "path";
import { buildServerBinary, discoverEponymSource } from "./serverSetup";

/** Resolve or build the LSP in extension-owned storage, with visible progress. */
export async function ensureServerBinary(
  storageDir: string,
  workspaceDir: string,
  nim: string,
  output: vscode.OutputChannel,
): Promise<string | null> {
  const configured = vscode.workspace.getConfiguration("eponym").get<string>("lspServerPath", "").trim();
  if (configured) {
    try {
      fs.accessSync(configured, fs.constants.X_OK);
      return configured;
    } catch {
      vscode.window.showErrorMessage(`Eponym: configured LSP server is not executable: ${configured}`);
      return null;
    }
  }

  const source = await discoverEponymSource(workspaceDir);
  if (!source) {
    vscode.window.showErrorMessage(
      "Eponym: could not find the server source. Install Eponym with `nimble install eponym`, or open an Eponym repository."
    );
    return null;
  }
  if (source.kind === "repo") {
    const existing = path.join(source.dir, process.platform === "win32" ? "lsp.exe" : "lsp");
    try { fs.accessSync(existing, fs.constants.X_OK); return existing; } catch { /* Build below. */ }
  }

  let binary: string | null = null;
  let buildError = "";
  await vscode.window.withProgress(
    { location: vscode.ProgressLocation.Notification, title: "Eponym: preparing LSP server" },
    async () => {
      try { binary = await buildServerBinary(nim, source, storageDir, workspaceDir); }
      catch (error) { buildError = error instanceof Error ? error.message : String(error); }
    },
  );
  if (!binary) {
    const show = await vscode.window.showErrorMessage(
      `Eponym: could not build the LSP server with Nim. Install Nim 2.0 or newer and ensure the Eponym Nimble package is current.`,
      "Show details",
    );
    if (show === "Show details") {
      output.appendLine(`[eponym] LSP build failed from ${source.dir}`);
      output.appendLine(buildError);
      output.show();
    }
    return null;
  }
  return binary;
}
