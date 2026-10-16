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

/** Append a line to the shared channel; no-op until initLog runs. */
export function log(msg: string): void {
  channel?.appendLine(msg);
}
