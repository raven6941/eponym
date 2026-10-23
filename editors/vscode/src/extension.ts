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

const openPanels = new Map<string, ShedPanel>(); // docUri -> panel
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
      const sp = ensureServerBinary();
      if (!sp) return;
      let client: LspClient;
      try {
        client = new LspClient(sp);
        await client.initialize(editor.document.uri.fsPath.replace(/\/[^/]+$/, ""));
      } catch (e) {
        vscode.window.showErrorMessage("Eponym: could not start LSP server: " + String(e));
        return;
      }
      // Issue #208: the server's textDocument/codeAction path ("case-split"
      // in the webview) requires an open document; shedLayout/refineShed
      // work from disk and never needed this.
      client.didOpen(docUri, editor.document.getText());
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
          } else if (m.cmd === "refine" || m.cmd === "give") {
            // Issue #137: the server owns the whole refine round-trip --
            // it fills the hole in the macro-recorded generated source,
            // refreshes statuses, and rewrites the sidecar. The client
            // splices the returned term over the single-line shed marker
            // at (nimLine, nimCol) so the .nim source advances.
            const res = await client.refineShed(
              docUri, entry.shedName, m.term ?? "", m.cmd === "give"
            );
            const line = res.nimLine - 1;
            const startCh = res.nimCol - 1;
            const startOffset = editor.document.offsetAt(
              new vscode.Position(line, startCh)
            );
            const node = shedNodeStartingAt(editor.document.getText(), startOffset);
            if (!node) throw new Error("Eponym: no shed marker at " +
              `${res.nimLine}:${res.nimCol}`);
            const end = editor.document.positionAt(node.end);
            if (end.line !== line) throw new Error("Eponym: shed marker spans multiple lines");
            await editor.edit((b) =>
              b.replace(new vscode.Range(line, startCh, line, end.character), res.term)
            );
            await editor.document.save();
            layoutCache.delete(docUri);
            if (!(await ensureSidecar(editor.document, true))) return;
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `refined ${res.shedName}: ${res.status} (${res.yellowCount} yellow left)`,
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
            const res = await client.caseSplitShed(
              docUri,
              entry.shedName,
              variable
            );
            // Splice the eliminator term over the shed marker
            // (same single-line span logic as refine).
            const line = res.nimLine - 1;
            const startCh = res.nimCol - 1;
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
                res.term
              )
            );
            // Persist the source splice, then always compile it so the
            // macro rewrites the sidecar with the newly-created sub-sheds.
            // Force avoids same-millisecond mtime races with Auto Save and
            // the onDidSave handler.
            await editor.document.save();
            layoutCache.delete(docUri);
            if (await ensureSidecar(editor.document, true)) {
              lensProvider.refreshDoc(editor.document);
              entry.shedName = res.subSheds[0];
              await refresh();
            }
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: `case-split ${variable}: ${res.subSheds.length} new sheds (${res.subSheds.join(", ")})`,
            });
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
    const sp = ensureServerBinary();
    if (!sp) return null;
    const c = new LspClient(sp);
    await c.initialize(path.dirname(doc.uri.fsPath));
    c.didOpen(doc.uri.toString(), doc.getText());
    return c;
  }
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
      } finally {
        client.shutdown();
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
        const res = await client.refineShed(cur.docUri, cur.shedName, term);
        // Complete the round-trip: splice the returned term over the shed
        // node, collapse its virtual view, then save so the sidecar regenerates.
        const ok = await spliceTermOverShed(editor, res.nimLine, res.nimCol, res.term);
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
        lensProvider.refreshDoc(editor.document);
        vscode.window.showInformationMessage(
          `Refined ${cur.shedName}: ${res.status} (${res.yellowCount} yellow left)`
        );
      } catch (e) {
        vscode.window.showErrorMessage(`Refine failed: ${String(e)}`);
      } finally {
        client.shutdown();
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
        const res = await client.caseSplitShed(cur.docUri, cur.shedName, variable);
        // Splice the eliminator term (carrying the new sub-shed nodes)
        // over the shed node, then save so the recompile discovers them.
        const ok = await spliceTermOverShed(editor, res.nimLine, res.nimCol, res.term);
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
        lensProvider.refreshDoc(editor.document);
        vscode.window.showInformationMessage(
          `Case-split ${variable}: ${res.subSheds.length} new sheds (${res.subSheds.join(", ")})`
        );
      } catch (e) {
        vscode.window.showErrorMessage(`Case-split failed: ${String(e)}`);
      } finally {
        client.shutdown();
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
        const res = await client.refineShed(cur.docUri, cur.shedName, term, true);
        const ok = await spliceTermOverShed(editor, res.nimLine, res.nimCol, res.term);
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
        lensProvider.refreshDoc(editor.document);
        vscode.window.showInformationMessage(`Gave ${cur.shedName}: ${res.status}`);
      } catch (e) {
        vscode.window.showErrorMessage(`Give failed: ${String(e)}`);
      } finally {
        client.shutdown();
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
