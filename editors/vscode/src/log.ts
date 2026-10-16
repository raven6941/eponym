// Shared diagnostic log for the Eponym extension.
//
// Single "Eponym" output channel, registered once from activate().
// Safe to call before registration (messages are dropped, never throw),
// and never creates a second channel.
import * as vscode from "vscode";

let channel: vscode.OutputChannel | undefined;

/** Register the single shared channel (called from activate()). */
export function initLog(c: vscode.OutputChannel): void {
  channel = c;
}

/** Append a line to the shared channel; re-creates it defensively if lost. */
export function log(msg: string): void {
  if (!channel) {
    // Defensive: if initLog never ran or the host dropped the channel
    // (seen in web VS Code with stale extension-host state), create it.
    try {
      channel = vscode.window.createOutputChannel("Eponym");
    } catch {
      return;
    }
  }
  channel.appendLine(msg);
}
