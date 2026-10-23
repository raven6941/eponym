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
import { serverPath, ensureServerBinary } from "./serverPath";
import { initLog, log } from "./log";
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
  shedNodeStartingAt,
} from "./sidecar";
import {
  ShedCodeLensProvider,
  expandShed,
  collapseShed,
  currentExpanded,
  setInlineShedRefresh,
  removeExpandedForSave,
} from "./inlineShed";

function nimBin(): string {
  const cfg = vscode.workspace.getConfiguration("eponym").get<string>("nimPath", "");
  if (cfg) return cfg;
  // Issue #221: try common Nim locations if not on PATH (e.g. VS Code
  // launched from Finder/Dock without shell PATH).
  const home = process.env.HOME ?? "";
  const candidates = [
    "nim", // PATH
    `${home}/.nimble/bin/nim`, // choosenim default
    "/opt/nim/bin/nim",
    "/usr/local/bin/nim",
  ];
  for (const c of candidates) {
    try {
      // execFileSync throws on ENOENT; we only need existence here.
      require("child_process").execFileSync(c, ["--version"], { stdio: "ignore" });
      if (c !== "nim") {
        out.appendLine(`[eponym] using Nim at ${c} (not on PATH)`);
      }
      return c;
    } catch {
      // try next
    }
  }
  return "nim"; // fallback; generateSidecar will report the ENOENT clearly
}

interface ShedPanel {
  panel: vscode.WebviewPanel;
  client: LspClient;
  shedName: string; // mutable: in-view switching (issue #190) updates it
  shedNames: string[];
  refresh: () => Promise<void>;
}

interface ActionSourceSnapshot {
  beforeText: string;
  afterText: string;
}

const openPanels = new Map<string, ShedPanel>(); // docUri -> panel
const documentClients = new Map<string, LspClient>();
const actionSourceSnapshots = new Map<string, Map<number, ActionSourceSnapshot>>();
const sidecarJobs = new Map<string, Promise<boolean>>();
let lensProvider: ShedCodeLensProvider;
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

async function applySourceSnapshot(
  editor: vscode.TextEditor, expected: string, replacement: string
): Promise<boolean> {
  const current = editor.document.getText();
  if (current !== expected) return false;
  let prefix = 0;
  while (prefix < current.length && prefix < replacement.length &&
         current[prefix] === replacement[prefix]) prefix++;
  let suffix = 0;
  while (suffix < current.length - prefix &&
         suffix < replacement.length - prefix &&
         current[current.length - 1 - suffix] ===
           replacement[replacement.length - 1 - suffix]) suffix++;
  const start = editor.document.positionAt(prefix);
  const end = editor.document.positionAt(current.length - suffix);
  const newText = replacement.slice(prefix, replacement.length - suffix);
  return editor.edit((builder) =>
    builder.replace(new vscode.Range(start, end), newText)
  );
}

function rememberActionSource(
  docUri: string, transitionId: number, beforeText: string, afterText: string
): void {
  let snapshots = actionSourceSnapshots.get(docUri);
  if (!snapshots) {
    snapshots = new Map<number, ActionSourceSnapshot>();
    actionSourceSnapshots.set(docUri, snapshots);
  }
  snapshots.set(transitionId, { beforeText, afterText });
}

function syncActionSourceHistory(
  docUri: string, transitions: Array<{ id: number }>
): void {
  const snapshots = actionSourceSnapshots.get(docUri);
  if (!snapshots) return;
  const liveIds = new Set(transitions.map((transition) => transition.id));
  for (const id of snapshots.keys()) {
    if (!liveIds.has(id)) snapshots.delete(id);
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

async function ensureSidecar(doc: vscode.TextDocument, force = false): Promise<boolean> {
  // Sidecar compilation reads the file from disk. Save dirty editor content
  // first so a just-added marker is included instead of silently using an
  // older but mtime-fresh sidecar.
  if (doc.isDirty && !(await doc.save())) {
    vscode.window.showWarningMessage("Eponym: save the Nim file before opening its shed view");
    return false;
  }
  const docUri = doc.uri.toString();
  const activeJob = sidecarJobs.get(docUri);
  if (activeJob) return activeJob;
  const job = (async (): Promise<boolean> => {
    // Issue #190: skip the `nim c` rerun when the sidecar is newer than the
    // source — this was the visible pause on "Show shed layout" whenever
    // the file had not changed since the last generation.
    // Force after a save or source splice; mtime resolution can otherwise
    // leave a same-millisecond edit looking fresh.
    if (!force && sidecarFresh(doc.uri.fsPath)) {
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
  })();
  sidecarJobs.set(docUri, job);
  try {
    return await job;
  } finally {
    if (sidecarJobs.get(docUri) === job) sidecarJobs.delete(docUri);
  }
}

export function activate(ctx: vscode.ExtensionContext) {
  out = vscode.window.createOutputChannel("Eponym");
  initLog(out);
  log("[eponym] extension v0.1.18 activated");

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

  // Recompile every saved shedsBlock file so new or changed markers always
  // have fresh goals and source positions. Ordinary Nim files are untouched.
  ctx.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(async (doc) => {
      if (doc.languageId !== "nim" && !doc.fileName.endsWith(".nim")) return;
      if (!hasShedBlocks(doc.getText())) return;
      const docUri = doc.uri.toString();
      layoutCache.delete(docUri);
      const entry = openPanels.get(docUri);
      if (entry) {
        // Keep the open LSP document current before the sidecar is read.
        entry.client.didChange(docUri, doc.getText());
      }
      if (!(await ensureSidecar(doc, true))) return;
      lensProvider.refreshDoc(doc);
      if (entry) await entry.refresh();
    })
  );

  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.showShedLayout", async (requestedOffset?: number) => {
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
        const reCursorOff = requestedOffset ?? editor.document.offsetAt(editor.selection.active);
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
      // marker (`![ name ...]` or `shedHole(name)`), open that shed directly.
      // Elsewhere in a single-shed block, that shed is the
      // unambiguous choice. Otherwise offer a QuickPick of the file's
      // sheds (read from the sidecar; no LSP round-trip needed), falling
      // back to the free-text box only when the sidecar lists nothing.
      const text = editor.document.getText();
      const cursorOff = requestedOffset ?? editor.document.offsetAt(editor.selection.active);
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

      // The binary check shows an actionable error itself; the try/catch
      // below covers spawn/initialize failures of an existing binary.
      let client: LspClient;
      try {
        const existing = await inlineClient(editor.document);
        if (!existing) return;
        client = existing;
      } catch (e) {
        vscode.window.showErrorMessage("Eponym: could not start LSP server: " + String(e));
        return;
      }
      // Issue #208: the server's textDocument/codeAction path ("case-split"
      // in the webview) requires an open document; shedLayout/refineShed
      // work from disk and never needed this.
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
          const history = await client.shedActionHistory(docUri);
          syncActionSourceHistory(docUri, history.transitions);
          panel.webview.postMessage({
            cmd: "historyState",
            canUndo: history.canUndo,
            canRedo: history.canRedo,
          });
        } catch (e) {
          panel.webview.postMessage({ cmd: "actionmsg", text: "layout error: " + String(e) });
        }
      };
      entry.refresh = refresh;
      panel.webview.onDidReceiveMessage(async (m: any) => {
        try {
          if (m.cmd === "ready") {
            const history = await client.shedActionHistory(docUri);
            panel.webview.postMessage({
              cmd: "historyState",
              canUndo: history.canUndo,
              canRedo: history.canRedo,
            });
          } else if (m.cmd === "switch-shed" && typeof m.shedName === "string") {
            // Issue #190: in-view shed switching — no close/reopen.
            entry.shedName = m.shedName;
            if (!entry.shedNames.includes(m.shedName)) entry.shedNames.push(m.shedName);
            entry.panel.title = `Shed: ${m.shedName}`;
            await entry.refresh();
          } else if (m.cmd === "intro") {
            const res = await client.introShed(docUri, entry.shedName, m.count ?? 1);
            const line = res.nimLine - 1;
            const startCh = res.nimCol - 1;
            const startOffset = editor.document.offsetAt(
              new vscode.Position(line, startCh)
            );
            const node = shedNodeStartingAt(editor.document.getText(), startOffset);
            if (!node || editor.document.positionAt(node.end).line !== line) {
              throw new Error(`intro: could not find the shed marker for '${entry.shedName}'`);
            }
            const endCh = editor.document.positionAt(node.end).character;
            await editor.edit((b) =>
              b.replace(new vscode.Range(line, startCh, line, endCh), res.term)
            );
            await editor.document.save();
            layoutCache.delete(docUri);
            if (!(await ensureSidecar(editor.document, true))) return;
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `introduced ${res.shedName}: ${res.status} (${res.yellowCount} yellow left)`,
            });
            await refresh();
          } else if (m.cmd === "construct") {
            const options = await client.refineConstructorsShed(
              docUri, entry.shedName
            );
            if (options.constructors.length === 0) {
              panel.webview.postMessage({
                cmd: "actionmsg",
                text: options.message ?? "No constructor is known to fit this goal",
              });
              return;
            }
            const constructor = await vscode.window.showQuickPick(
              options.constructors.map((label) => ({ label })),
              { placeHolder: `Constructor for ${entry.shedName}` }
            );
            if (!constructor) return;
            const res = await client.refineConstructorsShed(
              docUri, entry.shedName, constructor.label
            );
            const line = res.nimLine - 1;
            const startCh = res.nimCol - 1;
            const startOffset = editor.document.offsetAt(
              new vscode.Position(line, startCh)
            );
            const node = shedNodeStartingAt(editor.document.getText(), startOffset);
            if (!node || editor.document.positionAt(node.end).line !== line) {
              throw new Error(`construct: could not find shed marker for '${entry.shedName}'`);
            }
            const endCh = editor.document.positionAt(node.end).character;
            await editor.edit((b) =>
              b.replace(new vscode.Range(line, startCh, line, endCh), res.term)
            );
            await editor.document.save();
            layoutCache.delete(docUri);
            if (!(await ensureSidecar(editor.document, true))) return;
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `constructed ${constructor.label}: ${res.status} (${res.yellowCount} yellow left)`,
            });
            await refresh();
          } else if (m.cmd === "apply") {
            const options = await client.refineFromContextShed(
              docUri, entry.shedName
            );
            if (options.candidates.length === 0) {
              panel.webview.postMessage({
                cmd: "actionmsg",
                text: options.message ?? "No local hypothesis is known to fit this goal",
              });
              return;
            }
            const candidate = await vscode.window.showQuickPick(
              options.candidates.map((label) => ({ label })),
              { placeHolder: `Apply from context to ${entry.shedName}` }
            );
            if (!candidate) return;
            const res = await client.refineFromContextShed(
              docUri, entry.shedName, candidate.label
            );
            const line = res.nimLine - 1;
            const startCh = res.nimCol - 1;
            const startOffset = editor.document.offsetAt(
              new vscode.Position(line, startCh)
            );
            const node = shedNodeStartingAt(editor.document.getText(), startOffset);
            if (!node || editor.document.positionAt(node.end).line !== line) {
              throw new Error(`apply: could not find shed marker for '${entry.shedName}'`);
            }
            const endCh = editor.document.positionAt(node.end).character;
            await editor.edit((b) =>
              b.replace(new vscode.Range(line, startCh, line, endCh), res.term)
            );
            await editor.document.save();
            layoutCache.delete(docUri);
            if (!(await ensureSidecar(editor.document, true))) return;
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `applied ${candidate.label}: ${res.status} (${res.yellowCount} yellow left)`,
            });
            await refresh();
          } else if (m.cmd === "rewrite") {
            const options = await client.refineEqualityShed(
              docUri, entry.shedName
            );
            if (options.candidates.length === 0) {
              panel.webview.postMessage({
                cmd: "actionmsg",
                text: options.message ?? "No equality rewrite is known to fit this goal",
              });
              return;
            }
            const rewrite = await vscode.window.showQuickPick(
              options.candidates.map((label) => ({ label })),
              { placeHolder: `Rewrite ${entry.shedName} using equality (choose direction)` }
            );
            if (!rewrite) return;
            const res = await client.refineEqualityShed(
              docUri, entry.shedName, rewrite.label
            );
            const line = res.nimLine - 1;
            const startCh = res.nimCol - 1;
            const startOffset = editor.document.offsetAt(
              new vscode.Position(line, startCh)
            );
            const node = shedNodeStartingAt(editor.document.getText(), startOffset);
            if (!node || editor.document.positionAt(node.end).line !== line) {
              throw new Error(`rewrite: could not find shed marker for '${entry.shedName}'`);
            }
            const endCh = editor.document.positionAt(node.end).character;
            await editor.edit((b) =>
              b.replace(new vscode.Range(line, startCh, line, endCh), res.term)
            );
            await editor.document.save();
            layoutCache.delete(docUri);
            if (!(await ensureSidecar(editor.document, true))) return;
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `rewrote using ${rewrite.label}: ${res.status} (${res.yellowCount} yellow left)`,
            });
            await refresh();
          } else if (m.cmd === "refine" || m.cmd === "give") {
            const sourceBefore = editor.document.getText();
            const action = m.cmd === "give"
              ? { kind: "give" as const, target: entry.shedName,
                  arguments: { term: m.term ?? "" } }
              : { kind: "refine" as const, target: entry.shedName,
                  arguments: { term: m.term ?? "" } };
            const res = await client.performShedAction(docUri, action);
            const line = res.edit.nimLine - 1;
            const startCh = res.edit.nimCol - 1;
            const startOffset = editor.document.offsetAt(
              new vscode.Position(line, startCh)
            );
            const node = shedNodeStartingAt(editor.document.getText(), startOffset);
            if (!node) throw new Error("Eponym: no shed marker at " +
              `${res.edit.nimLine}:${res.edit.nimCol}`);
            const end = editor.document.positionAt(node.end);
            if (end.line !== line) throw new Error("Eponym: shed marker spans multiple lines");
            await editor.edit((b) =>
              b.replace(new vscode.Range(line, startCh, line, end.character), res.edit.term)
            );
            await editor.document.save();
            layoutCache.delete(docUri);
            if (!(await ensureSidecar(editor.document, true))) return;
            const committed = await client.commitShedAction(docUri, res.id);
            rememberActionSource(docUri, res.id, sourceBefore, editor.document.getText());
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `${m.cmd} ${entry.shedName}: ${committed.validation.status} ` +
                `(${committed.validation.yellowCount} yellow left)`,
            });
            await refresh();
          } else if (m.cmd === "case-split") {
            // Issue #209: shed-aware case-split via eponym/caseSplitShed
            // (term-level eliminator application; the old codeAction path
            // rewrote .ep procs into clause-defs, which cannot round-trip
            // through the nim ![...] node).
            const variable = m.variable ?? "";
            if (variable === "") {
              panel.webview.postMessage({
                cmd: "actionmsg",
                text: "case-split: type a variable name first",
              });
              return;
            }
            const sourceBefore = editor.document.getText();
            const res = await client.performShedAction(docUri, {
              kind: "caseSplit", target: entry.shedName,
              arguments: { variable },
            });
            // Splice the eliminator term over the shed marker
            // (same single-line span logic as refine).
            const line = res.edit.nimLine - 1;
            const startCh = res.edit.nimCol - 1;
            const startOffset = editor.document.offsetAt(
              new vscode.Position(line, startCh)
            );
            const node = shedNodeStartingAt(editor.document.getText(), startOffset);
            if (!node || editor.document.positionAt(node.end).line !== line) {
              throw new Error(
                `case-split: could not find the shed marker for '${entry.shedName}'`
              );
            }
            const endCh = editor.document.positionAt(node.end).character;
            await editor.edit((b) =>
              b.replace(
                new vscode.Range(line, startCh, line, endCh),
                res.edit.term
              )
            );
            // Persist the source splice, then always compile it so the
            // macro rewrites the sidecar with the newly-created sub-sheds.
            // Force avoids same-millisecond mtime races with Auto Save and
            // the onDidSave handler.
            await editor.document.save();
            layoutCache.delete(docUri);
            if (await ensureSidecar(editor.document, true)) {
              await client.commitShedAction(docUri, res.id);
              rememberActionSource(docUri, res.id, sourceBefore, editor.document.getText());
              lensProvider.refreshDoc(editor.document);
              entry.shedName = res.subSheds[0];
              await refresh();
            }
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `case-split ${variable}: ${res.subSheds.length} new sheds (${res.subSheds.join(", ")})`,
            });
          } else if (m.cmd === "undo") {
            const history = await client.shedActionHistory(docUri);
            syncActionSourceHistory(docUri, history.transitions);
            const last = history.transitions[history.cursor - 1];
            const snapshot = last
              ? actionSourceSnapshots.get(docUri)?.get(last.id)
              : undefined;
            if (!last || !snapshot) {
              throw new Error("no source projection is available for the last checked action");
            }
            const res = await client.undoShedAction(docUri);
            if (res.transitionId !== last.id) {
              throw new Error("undo history changed while the action was being prepared");
            }
            const applied = await applySourceSnapshot(
              editor, snapshot.afterText, snapshot.beforeText
            );
            if (!applied) throw new Error("undo refused because the editor source changed");
            await editor.document.save();
            layoutCache.delete(docUri);
            if (!(await ensureSidecar(editor.document, true))) return;
            await client.commitShedHistoryMove(docUri, res.transitionId, "undo");
            entry.shedName = res.transition.action.target;
            if (!entry.shedNames.includes(entry.shedName)) entry.shedNames.push(entry.shedName);
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({ cmd: "actionmsg", text: "undid the last checked shed action" });
            await refresh();
          } else if (m.cmd === "redo") {
            const history = await client.shedActionHistory(docUri);
            syncActionSourceHistory(docUri, history.transitions);
            const next = history.transitions[history.cursor];
            const snapshot = next
              ? actionSourceSnapshots.get(docUri)?.get(next.id)
              : undefined;
            if (!next || !snapshot) {
              throw new Error("no source projection is available for the next checked action");
            }
            const res = await client.redoShedAction(docUri);
            if (res.id !== next.id || editor.document.getText() !== snapshot.beforeText) {
              throw new Error("redo history no longer matches the current source");
            }
            const line = res.edit.nimLine - 1;
            const startCh = res.edit.nimCol - 1;
            const startOffset = editor.document.offsetAt(new vscode.Position(line, startCh));
            const node = shedNodeStartingAt(editor.document.getText(), startOffset);
            if (!node || editor.document.positionAt(node.end).line !== line) {
              throw new Error("redo could not locate the original shed marker");
            }
            const endCh = editor.document.positionAt(node.end).character;
            await editor.edit((b) =>
              b.replace(new vscode.Range(line, startCh, line, endCh), res.edit.term)
            );
            await editor.document.save();
            layoutCache.delete(docUri);
            if (!(await ensureSidecar(editor.document, true))) return;
            await client.commitShedHistoryMove(docUri, res.id, "redo");
            rememberActionSource(docUri, res.id, snapshot.beforeText, editor.document.getText());
            const nextGoal = res.after.goals.find((goal) => goal.status === "yellow");
            if (nextGoal) entry.shedName = nextGoal.shedName;
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({ cmd: "actionmsg", text: "replayed the checked shed action" });
            await refresh();
          } else if (m.cmd === "history") {
            const history = await client.shedActionHistory(docUri);
            syncActionSourceHistory(docUri, history.transitions);
            if (history.transitions.length === 0) {
              panel.webview.postMessage({ cmd: "actionmsg", text: "no checked actions in this session" });
              return;
            }
            const selected = await vscode.window.showQuickPick(
              history.transitions.map((transition, index) => ({
                label: `${transition.applied ? "applied" : "undone"} ${index + 1}. ` +
                  `${transition.action.kind} ${transition.action.target}`,
                description: JSON.stringify(transition.action.arguments),
                detail: transition.before.goal,
              })),
              { placeHolder: history.cursor > 0 && !history.canUndo
                ? `Checked actions (${history.cursor} applied; stale in the current source)`
                : `Checked actions (${history.cursor} applied)` }
            );
            if (selected) {
              vscode.window.showInformationMessage(
                `${selected.label}\nGoal before action: ${selected.detail}`
              );
            }
          }
        } catch (e) {
          panel.webview.postMessage({ cmd: "actionmsg", text: "action failed: " + String(e) });
        }
      });
      panel.onDidDispose(() => {
        openPanels.delete(docUri);
      });
      openPanels.set(docUri, entry);
      await refresh();
    })
  );

  // Issue #221: marker summaries and keyboard-navigable inline 2D previews.
  lensProvider = new ShedCodeLensProvider();
  setInlineShedRefresh(() => lensProvider.refreshCodeLenses());
  // Match by language ID "nim" OR by .nim file extension, since the
  // extension does not contribute the Nim language definition itself.
  const nimSelector: vscode.DocumentSelector = [
    { language: "nim" },
    { pattern: "**/*.nim" },
  ];
  ctx.subscriptions.push(
    vscode.languages.registerCodeLensProvider(nimSelector, lensProvider)
  );
  // The inline box is temporary text so it can occupy multiple visual lines
  // and accept cursor actions. Remove it as part of the save event so neither
  // manual save nor Auto Save can persist the preview as Nim source.
  ctx.subscriptions.push(
    vscode.workspace.onWillSaveTextDocument((e) => {
      e.waitUntil(Promise.resolve(removeExpandedForSave(e.document.uri.toString())));
    })
  );
  // Refresh CodeLens when a shed file is opened (so goals show without save).
  ctx.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument((doc) => {
      if (doc.languageId !== "nim" && !doc.fileName.endsWith(".nim")) return;
      if (!hasShedBlocks(doc.getText())) return;
      lensProvider.refreshDoc(doc);
    })
  );

  // Lazily create an LSP client for inline-shed actions. Returns null
  // (after showing an actionable error) when the server binary is missing.
  async function inlineClient(doc: vscode.TextDocument): Promise<LspClient | null> {
    const docUri = doc.uri.toString();
    const existing = documentClients.get(docUri);
    if (existing) {
      existing.didChange(docUri, doc.getText());
      return existing;
    }
    const sp = ensureServerBinary();
    if (!sp) return null;
    const c = new LspClient(sp);
    await c.initialize(path.dirname(doc.uri.fsPath));
    c.didOpen(docUri, doc.getText());
    documentClients.set(docUri, c);
    return c;
  }
  ctx.subscriptions.push(
    vscode.workspace.onDidChangeTextDocument((event) => {
      const docUri = event.document.uri.toString();
      const client = documentClients.get(docUri);
      client?.didChange(docUri, event.document.getText());
      const panel = openPanels.get(docUri);
      if (client && panel) {
        void client.shedActionHistory(docUri).then((history) => {
          if (openPanels.get(docUri) !== panel) return;
          panel.panel.webview.postMessage({
            cmd: "historyState",
            canUndo: history.canUndo,
            canRedo: history.canRedo,
          });
        }).catch(() => {
          // Keep the current button state if the LSP is shutting down.
        });
      }
    })
  );
  ctx.subscriptions.push(
    vscode.workspace.onDidCloseTextDocument((doc) => {
      const docUri = doc.uri.toString();
      documentClients.get(docUri)?.shutdown();
      documentClients.delete(docUri);
      openPanels.get(docUri)?.panel.dispose();
    })
  );
  ctx.subscriptions.push({ dispose: () => {
    for (const client of documentClients.values()) client.shutdown();
    documentClients.clear();
  }});
  function inlineShowButtons(): boolean {
    return vscode.workspace
      .getConfiguration("eponym")
      .get<boolean>("inlineShed.showButtons", true);
  }
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.expandShed", async (atOffset?: number) => {
      log("[eponym] expandShed fired, atOffset=" + String(atOffset));
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        vscode.window.showErrorMessage("Eponym: no active text editor");
        return;
      }
      if (!(await ensureSidecar(editor.document))) return;
      lensProvider.refreshDoc(editor.document);
      try {
        await expandShed(
          editor,
          inlineClient,
          { showButtons: inlineShowButtons() },
          atOffset
        );
      } catch (e) {
        vscode.window.showErrorMessage(`Eponym: expand failed: ${String(e)}`);
      }
    })
  );
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.collapseShed", () => collapseShed())
  );
  // Issue #221 follow-up: splice a returned term over the single-line
  // shed marker at (nimLine, nimCol)
  // (1-based, from the LSP). Returns false when the node can't be found.
  async function spliceTermOverShed(
    editor: vscode.TextEditor,
    nimLine: number,
    nimCol: number,
    term: string
  ): Promise<boolean> {
    const line = nimLine - 1;
    const startCh = nimCol - 1;
    if (line < 0 || line >= editor.document.lineCount) return false;
    const startOffset = editor.document.offsetAt(new vscode.Position(line, startCh));
    const node = shedNodeStartingAt(editor.document.getText(), startOffset);
    if (!node) return false;
    const end = editor.document.positionAt(node.end);
    if (end.line !== line) return false;
    await editor.edit((b) =>
      b.replace(new vscode.Range(line, startCh, line, end.character), term)
    );
    return true;
  }

  // Keyboard-bound shed actions (i/r/c/g) operate on the expanded shed.
  // They reuse the webview's refine/case-split flows via a transient client.
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.shedIntro", async () => {
      const cur = currentExpanded();
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        vscode.window.showErrorMessage("Eponym: no active text editor");
        return;
      }
      if (!cur) {
        vscode.window.showErrorMessage("Eponym: no shed expanded");
        return;
      }
      const client = await inlineClient(editor.document);
      if (!client) return;
      try {
        const res = await client.introShed(cur.docUri, cur.shedName);
        const ok = await spliceTermOverShed(editor, res.nimLine, res.nimCol, res.term);
        if (!ok) {
          vscode.window.showWarningMessage(
            `Introduced ${cur.shedName} server-side, but could not locate its shed marker to splice.`
          );
          return;
        }
        await collapseShed();
        await editor.document.save();
        layoutCache.delete(editor.document.uri.toString());
        if (!(await ensureSidecar(editor.document, true))) return;
        lensProvider.refreshDoc(editor.document);
        vscode.window.showInformationMessage(
          `Introduced a binder for ${cur.shedName}: ${res.status} (${res.yellowCount} yellow left)`
        );
      } catch (e) {
        vscode.window.showErrorMessage(`Intro failed: ${String(e)}`);
      }
    })
  );
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.shedRefine", async () => {
      const cur = currentExpanded();
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        vscode.window.showErrorMessage("Eponym: no active text editor");
        return;
      }
      if (!cur) {
        vscode.window.showErrorMessage("Eponym: no shed expanded");
        return;
      }
      const term = await vscode.window.showInputBox({
        prompt: `Refine shed ${cur.shedName} with term`,
        placeHolder: "e.g. zero()",
      });
      if (term === undefined) return;
      const client = await inlineClient(editor.document);
      if (!client) return; // binary missing; actionable error already shown
      try {
        const sourceBefore = editor.document.getText();
        const res = await client.performShedAction(cur.docUri, {
          kind: "refine", target: cur.shedName, arguments: { term },
        });
        // Complete the round-trip: splice the returned term over the shed
        // node, collapse its virtual view, then save so the sidecar regenerates.
        const ok = await spliceTermOverShed(
          editor, res.edit.nimLine, res.edit.nimCol, res.edit.term
        );
        if (!ok) {
          vscode.window.showWarningMessage(
            `Refined ${cur.shedName} server-side, but could not locate its shed marker to splice.`
          );
          return;
        }
        await collapseShed();
        await editor.document.save();
        layoutCache.delete(editor.document.uri.toString());
        if (!(await ensureSidecar(editor.document, true))) return;
        await client.commitShedAction(cur.docUri, res.id);
        rememberActionSource(cur.docUri, res.id, sourceBefore, editor.document.getText());
        lensProvider.refreshDoc(editor.document);
        vscode.window.showInformationMessage(
          `Refined ${cur.shedName}: ${res.validation.status} ` +
            `(${res.validation.yellowCount} yellow left)`
        );
      } catch (e) {
        vscode.window.showErrorMessage(`Refine failed: ${String(e)}`);
      }
    })
  );
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.shedCaseSplit", async () => {
      const cur = currentExpanded();
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        vscode.window.showErrorMessage("Eponym: no active text editor");
        return;
      }
      if (!cur) {
        vscode.window.showErrorMessage("Eponym: no shed expanded");
        return;
      }
      const variable = await vscode.window.showInputBox({
        prompt: `Case-split shed ${cur.shedName} on variable`,
        placeHolder: "e.g. n",
      });
      if (!variable) return;
      const client = await inlineClient(editor.document);
      if (!client) return; // binary missing; actionable error already shown
      try {
        const sourceBefore = editor.document.getText();
        const res = await client.performShedAction(cur.docUri, {
          kind: "caseSplit", target: cur.shedName, arguments: { variable },
        });
        // Splice the eliminator term (carrying the new sub-shed nodes)
        // over the shed node, then save so the recompile discovers them.
        const ok = await spliceTermOverShed(
          editor, res.edit.nimLine, res.edit.nimCol, res.edit.term
        );
        if (!ok) {
          vscode.window.showWarningMessage(
            `Case-split ${cur.shedName} server-side, but could not locate its shed marker to splice.`
          );
          return;
        }
        await collapseShed();
        await editor.document.save();
        layoutCache.delete(editor.document.uri.toString());
        if (!(await ensureSidecar(editor.document, true))) return;
        await client.commitShedAction(cur.docUri, res.id);
        rememberActionSource(cur.docUri, res.id, sourceBefore, editor.document.getText());
        lensProvider.refreshDoc(editor.document);
        vscode.window.showInformationMessage(
          `Case-split ${variable}: ${res.subSheds.length} new sheds (${res.subSheds.join(", ")})`
        );
      } catch (e) {
        vscode.window.showErrorMessage(`Case-split failed: ${String(e)}`);
      }
    })
  );
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.shedGive", async () => {
      const cur = currentExpanded();
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        vscode.window.showErrorMessage("Eponym: no active text editor");
        return;
      }
      if (!cur) {
        vscode.window.showErrorMessage("Eponym: no shed expanded");
        return;
      }
      const term = await vscode.window.showInputBox({
        prompt: `Give term for shed ${cur.shedName}`,
        placeHolder: "e.g. suc(zero())",
      });
      if (term === undefined) return;
      const client = await inlineClient(editor.document);
      if (!client) return; // binary missing; actionable error already shown
      try {
        const sourceBefore = editor.document.getText();
        const res = await client.performShedAction(cur.docUri, {
          kind: "give", target: cur.shedName, arguments: { term },
        });
        const ok = await spliceTermOverShed(
          editor, res.edit.nimLine, res.edit.nimCol, res.edit.term
        );
        if (!ok) {
          vscode.window.showWarningMessage(
            `Gave ${cur.shedName} server-side, but could not locate its shed marker to splice.`
          );
          return;
        }
        await collapseShed();
        await editor.document.save();
        layoutCache.delete(editor.document.uri.toString());
        if (!(await ensureSidecar(editor.document, true))) return;
        await client.commitShedAction(cur.docUri, res.id);
        rememberActionSource(cur.docUri, res.id, sourceBefore, editor.document.getText());
        lensProvider.refreshDoc(editor.document);
        vscode.window.showInformationMessage(
          `Gave ${cur.shedName}: ${res.validation.status}`
        );
      } catch (e) {
        vscode.window.showErrorMessage(`Give failed: ${String(e)}`);
      }
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
