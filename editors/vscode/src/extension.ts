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
import { LspClient, ShedStateGoal, ShedStateTransition } from "./protocol";
import { serverPath, ensureServerBinary } from "./serverPath";
import { initLog, log } from "./log";
import { pageHtml } from "./render";
import {
  canAdoptSuccessor, knownGoalNames, restoredStateForDocumentText,
  requestGoalLayout, requestGoalTransition, stateGoalReference,
} from "./stateHistory";
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
import {
  ShedCodeLensProvider,
  expandShed,
  collapseShed,
  collapseShedForDocument,
  currentExpanded,
  setInlineShedRefresh,
  removeExpandedForSave,
  sourceTextWithoutExpandedView,
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

interface LocalShedState {
  stateId: string;
  documentText: string;
  goals: ShedStateGoal[];
  parentStateId?: string;
  actionLabel?: string;
  targetName?: string;
  beforeGoal?: string;
}

interface LocalShedEdge {
  parentStateId: string;
  successorStateId: string;
  goalId: string;
  targetName: string;
  actionId: string;
  arguments: Record<string, unknown>;
  beforeGoal: string;
}

interface LocalShedHistory {
  currentStateId: string;
  states: Map<string, LocalShedState>;
  edges: LocalShedEdge[];
  editorText: string;
  editorVersion: number;
}

const openPanels = new Map<string, ShedPanel>(); // docUri -> panel
const documentClients = new Map<string, LspClient>();
const localShedHistories = new Map<string, LocalShedHistory>();
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
  const applied = await editor.edit((builder) =>
    builder.replace(new vscode.Range(start, end), newText)
  );
  // A successful edit transaction is not enough to claim that the requested
  // projection is visible. The editor can be stale or the document can have
  // changed while an adoption request was in flight; report a conflict unless
  // the target snapshot is now the document contents.
  return applied && editor.document.getText() === replacement;
}

async function ensureLocalShedHistory(
  client: LspClient, doc: vscode.TextDocument
): Promise<LocalShedHistory> {
  const docUri = doc.uri.toString();
  const existing = localShedHistories.get(docUri);
  if (existing) return existing;
  const bootstrap = await client.createShedState(docUri);
  const state: LocalShedState = {
    stateId: bootstrap.stateId,
    documentText: doc.getText(),
    goals: bootstrap.goals,
  };
  const history: LocalShedHistory = {
    currentStateId: state.stateId,
    states: new Map([[state.stateId, state]]),
    edges: [],
    editorText: doc.getText(),
    editorVersion: doc.version,
  };
  localShedHistories.set(docUri, history);
  return history;
}

function refreshEditorBaselineIfUnchanged(
  editor: vscode.TextEditor, history: LocalShedHistory
): void {
  // Inline preview insertion/removal advances VS Code's document version while
  // restoring identical source. Treat that as the same base revision; any
  // actual source difference still blocks source adoption.
  if (editor.document.getText() === history.editorText) {
    history.editorVersion = editor.document.version;
  }
}

function selectedLocalState(history: LocalShedHistory): LocalShedState {
  const state = history.states.get(history.currentStateId);
  if (!state) throw new Error("selected proof state is missing from local history");
  return state;
}

function postLocalHistoryState(docUri: string, panel?: ShedPanel): void {
  const history = localShedHistories.get(docUri);
  if (!history || !panel) return;
  const canUndo = !!selectedLocalState(history).parentStateId;
  const canRedo = history.edges.some((edge) => edge.parentStateId === history.currentStateId);
  panel.panel.webview.postMessage({ cmd: "historyState", canUndo, canRedo });
}

async function selectLocalState(
  editor: vscode.TextEditor, history: LocalShedHistory, targetStateId: string
): Promise<boolean> {
  const target = history.states.get(targetStateId);
  if (!target) throw new Error("that proof state is no longer in local history");
  // Root selection is local and immediate. Source adoption is a separate,
  // compare-and-apply operation against the last editor revision we observed.
  history.currentStateId = targetStateId;
  // A local undo can return the editor buffer to a previously known snapshot
  // while the cached baseline still names another branch. The snapshot itself
  // is the compare token; an editor version change alone is not a conflict.
  if (editor.document.getText() === target.documentText) {
    history.editorText = target.documentText;
    history.editorVersion = editor.document.version;
    return true;
  }
  refreshEditorBaselineIfUnchanged(editor, history);
  const safe = editor.document.version === history.editorVersion &&
    editor.document.getText() === history.editorText;
  if (!safe) return false;
  if (target.documentText !== history.editorText) {
    const applied = await applySourceSnapshot(editor, history.editorText, target.documentText);
    if (!applied) return false;
  }
  history.editorText = target.documentText;
  history.editorVersion = editor.document.version;
  return true;
}

async function recordLocalTransition(
  editor: vscode.TextEditor, history: LocalShedHistory,
  transition: ShedStateTransition, actionId: string,
  arguments_: Record<string, unknown>, targetName: string
): Promise<boolean> {
  const parent = history.states.get(transition.stateId);
  if (!parent) throw new Error("transition refers to a proof state not in local history");
  const beforeGoal = parent.goals.find((goal) =>
    goal.name === targetName && goal.goalId === transition.goalId
  );
  if (!beforeGoal) throw new Error(`goal '${targetName}' is not present in the transition's source state`);
  const next: LocalShedState = {
    stateId: transition.successorStateId,
    documentText: transition.documentText,
    goals: transition.goals,
    parentStateId: parent.stateId,
    actionLabel: actionId,
    targetName,
    beforeGoal: beforeGoal.goal,
  };
  history.states.set(next.stateId, next);
  history.edges.push({
    parentStateId: parent.stateId,
    successorStateId: next.stateId,
    goalId: transition.goalId,
    targetName,
    actionId,
    arguments: { ...arguments_ },
    beforeGoal: next.beforeGoal ?? "",
  });
  // A request may target a known historical root while another root remains
  // selected. Keep the checked successor in the local DAG, but only adopt it
  // when that exact source root is selected and displayed in the editor.
  if (!canAdoptSuccessor(history.currentStateId, editor.document.getText(),
      parent.stateId, parent.documentText)) return false;
  refreshEditorBaselineIfUnchanged(editor, history);
  if (editor.document.getText() !== history.editorText) return false;
  const applied = await applySourceSnapshot(editor, parent.documentText, next.documentText);
  if (!applied) return false;
  history.currentStateId = next.stateId;
  history.editorText = next.documentText;
  history.editorVersion = editor.document.version;
  return true;
}

async function performLocalAction(
  client: LspClient, editor: vscode.TextEditor, docUri: string,
  shedName: string, actionId: string, arguments_: Record<string, unknown>
): Promise<{ transition: ShedStateTransition; history: LocalShedHistory; applied: boolean }> {
  let history = localShedHistories.get(docUri);
  if (!history) {
    if (!(await ensureSidecar(editor.document))) throw new Error("shed sidecar is unavailable");
    history = await ensureLocalShedHistory(client, editor.document);
  }
  const transition = await requestGoalTransition(
    client, history, docUri, shedName, actionId, arguments_
  );
  const applied = await recordLocalTransition(
    editor, history, transition, actionId, arguments_, shedName
  );
  return { transition, history, applied };
}

async function currentStateActions(
  client: LspClient, docUri: string, shedName: string
) {
  const history = localShedHistories.get(docUri);
  if (!history) throw new Error("local proof-state history was not initialized");
  const reference = stateGoalReference(history, shedName);
  if (!reference) {
    throw new Error(
      `no locally known proof state contains an unresolved goal named '${shedName}'`
    );
  }
  return client.queryShedStateActions(
    docUri, reference.state.stateId, reference.goal.goalId
  );
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
  // Sidecar compilation reads the file from disk. Do not save editor content
  // as a side effect of opening a shed view: that buffer may contain a local
  // proof-state projection or edits that have not been adopted by the user.
  // The state-addressed path can keep using its client-held root without the
  // sidecar; a fresh bootstrap requires an explicit save first.
  if (doc.isDirty) {
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
  log("[eponym] extension v0.1.19 activated");

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
      if (entry) entry.client.didChange(docUri, sourceTextWithoutExpandedView(doc));
      if (!(await ensureSidecar(doc, true))) return;
      lensProvider.refreshDoc(doc);

      const history = localShedHistories.get(docUri);
      const client = entry?.client ?? documentClients.get(docUri);
      if (history && client) {
        const bootstrap = await client.createShedState(docUri);
        const state: LocalShedState = {
          stateId: bootstrap.stateId,
          documentText: doc.getText(),
          goals: bootstrap.goals,
        };
        const current = selectedLocalState(history);
        if (current.documentText !== doc.getText()) {
          // A saved manual edit establishes a new root while keeping prior
          // local states selectable as branches.
          history.states.set(state.stateId, state);
          history.currentStateId = state.stateId;
        }
        // Saving an adopted transition preserves its root and local edges.
        history.editorText = doc.getText();
        history.editorVersion = doc.version;
        if (entry && state.goals.length > 0) entry.shedName = state.goals[0].name;
        await entry?.refresh();
      } else if (entry) {
        await ensureLocalShedHistory(entry.client, doc);
        const state = selectedLocalState(localShedHistories.get(docUri)!);
        if (state.goals.length > 0) entry.shedName = state.goals[0].name;
        await entry.refresh();
      }
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
      // A client-held DAG already has the selected state's open goal set. Do
      // not compile the disk sidecar here: this editor may contain an
      // unsaved source projection from the preceding state transition.
      const localHistory = localShedHistories.get(docUri);
      if (!localHistory && !(await ensureSidecar(editor.document))) return;

      // Issue #190: cursor-aware default. With the cursor inside a shed
      // marker (`![ name ...]` or `shedHole(name)`), open that shed directly.
      // Elsewhere in a single-shed block, that shed is the
      // unambiguous choice. Otherwise offer a QuickPick of the file's
      // sheds (read from the sidecar; no LSP round-trip needed), falling
      // back to the free-text box only when the sidecar lists nothing.
      const text = editor.document.getText();
      const cursorOff = requestedOffset ?? editor.document.offsetAt(editor.selection.active);
      let shedName: string | undefined;
      const activeInline = currentExpanded();
      if (activeInline?.docUri === docUri && localHistory?.states.has(localHistory.currentStateId)) {
        const currentState = selectedLocalState(localHistory);
        if (currentState.goals.some((goal) => goal.name === activeInline.shedName)) {
          shedName = activeInline.shedName;
        }
      }
      if (!shedName) shedName = shedAtCursor(text, cursorOff)?.name;
      if (!shedName) {
        const inBlock = blockShedsAtCursor(text, cursorOff);
        if (inBlock.length === 1) shedName = inBlock[0].name;
      }
      const shedNames = localHistory
        ? selectedLocalState(localHistory).goals.map((goal) => goal.name)
        : readSidecarShedNames(sidecarPathFor(editor.document.uri.fsPath));
      // The cursor can still point at the old source marker after a local
      // transition (for example, case-split replaces it with clause goals).
      // In that case let the picker target a goal in the selected state.
      if (shedName && !shedNames.includes(shedName)) shedName = undefined;
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
      try {
        const history = await ensureLocalShedHistory(client, editor.document);
        if (!stateGoalReference(history, shedName)) {
          throw new Error(
            `goal '${shedName}' has no unique state reference in local history; ` +
            "select a history state that contains the unresolved goal"
          );
        }
      } catch (e) {
        vscode.window.showErrorMessage(`Eponym: could not initialize proof state: ${String(e)}`);
        return;
      }
      // State queries are rooted in immutable client-selected proof states;
      // no server history or transition acceptance message is involved.
      // Issue #208: the server's textDocument/codeAction path ("case-split"
      // in the webview) requires an open document; shedLayout/refineShed
      // work from disk and never needed this.
      const panel = vscode.window.createWebviewPanel(
        "eponymShed",
        `Shed: ${shedName}`,
        vscode.ViewColumn.Beside,
        { enableScripts: true }
      );
      // Render a usable shell before the first asynchronous layout request.
      // If LSP initialization/layout fails, the error is posted below; without
      // this initial HTML there is no page to receive that message and the
      // newly opened panel appears completely blank.
      panel.webview.html = pageHtml(JSON.stringify({ box: {} }), shedName, shedNames);
      let webviewReady = false;
      let pendingRender: {
        layout: unknown;
        shedName: string;
        shedNames: string[];
      } | undefined;
      let pendingActionMessage: string | undefined;
      const renderPage = (layout: unknown, name: string, names: string[]) => {
        if (!webviewReady) {
          pendingRender = { layout, shedName: name, shedNames: names };
          return;
        }
        void panel.webview.postMessage({ cmd: "rerender", layout, shedName: name, shedNames: names });
      };
      const showActionMessage = (text: string) => {
        if (!webviewReady) {
          pendingActionMessage = text;
          return;
        }
        void panel.webview.postMessage({ cmd: "actionmsg", text });
      };
      const entry: ShedPanel = {
        panel,
        client,
        shedName,
        shedNames,
        refresh: async () => {},
      };
      const refresh = async () => {
        try {
          const history = localShedHistories.get(docUri);
          if (!history) throw new Error("local proof-state history is unavailable");
          const selected = selectedLocalState(history);
          const reference = selected.goals.some((item) => item.name === entry.shedName)
            ? { state: selected, goal: selected.goals.find((item) => item.name === entry.shedName)! }
            : stateGoalReference(history, entry.shedName) as
              { state: LocalShedState; goal: { name: string; goalId: string } } | undefined;
          const state = reference?.state;
          const goal = reference?.goal;
          if (!state || !goal) {
            const known = knownGoalNames(history).includes(entry.shedName);
            renderPage({ box: {} }, entry.shedName, []);
            showActionMessage(known
                ? `goal '${entry.shedName}' is known in multiple historical branches. ` +
                  "Select a state where it is open from History, then choose the goal again."
                : `No locally known proof state contains an unresolved goal named '${entry.shedName}'. ` +
                  "Restore or declare a state that contains it.");
            if (webviewReady) postLocalHistoryState(docUri, entry);
            return;
          }
          entry.shedName = goal.name;
          entry.shedNames = knownGoalNames(history);
          const historical = state.stateId !== selected.stateId;
          entry.panel.title = `Shed: ${goal.name}${historical ? " (history)" : ""}`;
          const rendered = await requestGoalLayout(
            client, history, docUri, entry.shedName
          );
          const layout = rendered.layout;
          renderPage(layout.box, goal.name, entry.shedNames);
          if (historical) {
            showActionMessage(`Showing '${goal.name}' from a known historical state. Actions create a local branch; ` +
              "select the successor in History to adopt its source projection.");
          }
          if (webviewReady) postLocalHistoryState(docUri, entry);
        } catch (e) {
          showActionMessage("layout error: " + String(e));
        }
      };
      entry.refresh = refresh;
      const collapseInlineBeforeAdoption = async () => {
        if (!(await collapseShedForDocument(docUri))) {
          throw new Error(
            "could not remove the inline preview; the proof-state change was not applied"
          );
        }
      };
      panel.webview.onDidReceiveMessage(async (m: any) => {
        try {
          if (m.cmd === "ready") {
            webviewReady = true;
            if (pendingRender) {
              panel.webview.postMessage({ cmd: "rerender", ...pendingRender });
              pendingRender = undefined;
            }
            if (pendingActionMessage) {
              panel.webview.postMessage({ cmd: "actionmsg", text: pendingActionMessage });
              pendingActionMessage = undefined;
            }
            postLocalHistoryState(docUri, entry);
            return;
          }
          if (m.cmd === "switch-shed" && typeof m.shedName === "string") {
            const history = localShedHistories.get(docUri)!;
            if (!stateGoalReference(history, m.shedName)) {
              throw new Error(
                `goal '${m.shedName}' has no unique historical state; ` +
                "select a state where it is open from History"
              );
            }
            entry.shedName = m.shedName;
            await refresh();
            return;
          }
          if (["intro", "construct", "apply", "rewrite", "case-split"].includes(m.cmd)) {
            const available = await currentStateActions(client, docUri, entry.shedName);
            const actionId = m.cmd === "case-split" ? "caseSplit" : m.cmd;
            const descriptor = available.actions.find((action) => action.id === actionId);
            if (!descriptor) throw new Error(`${m.cmd} is not applicable to this goal`);
            let args: Record<string, unknown>;
            if (m.cmd === "intro") {
              args = { count: m.count ?? 1 };
            } else if (m.cmd === "case-split") {
              const variable = String(m.variable ?? "");
              const choices = descriptor.arguments.find((arg) => arg.name === "variable")?.choices?.map(String) ?? [];
              if (!variable || !choices.includes(variable)) {
                throw new Error(`'${variable}' is not a case-split choice for this goal`);
              }
              args = { variable };
            } else {
              const argName = m.cmd === "construct" ? "constructor" :
                m.cmd === "apply" ? "candidate" : "rewrite";
              const choices = descriptor.arguments.find((arg) => arg.name === argName)?.choices?.map(String) ?? [];
              if (choices.length === 0) throw new Error(`no ${m.cmd} choice is available`);
              const picked = await vscode.window.showQuickPick(
                choices.map((label) => ({ label })),
                { placeHolder: `${m.cmd} for ${entry.shedName}` }
              );
              if (!picked) return;
              args = { [argName]: picked.label };
            }
            await collapseInlineBeforeAdoption();
            const result = await performLocalAction(
              client, editor, docUri, entry.shedName, actionId, args
            );
            if (result.applied) {
              const successor = selectedLocalState(result.history);
              const nextGoal = successor.goals.find((goal) => goal.name === entry.shedName) ?? successor.goals[0];
              if (nextGoal) entry.shedName = nextGoal.name;
            }
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: result.applied
                ? `${m.cmd} ${entry.shedName}: ${result.transition.validation.status} ` +
                  `(${result.transition.validation.yellowCount} open goals)`
                : `checked ${m.cmd}; successor is stored in History. ` +
                  "Select that successor in History to adopt its source projection.",
            });
            await refresh();
            postLocalHistoryState(docUri, entry);
            return;
          }
          if (m.cmd === "refine" || m.cmd === "give") {
            await collapseInlineBeforeAdoption();
            const result = await performLocalAction(
              client, editor, docUri, entry.shedName, m.cmd, { term: m.term ?? "" }
            );
            if (result.applied) {
              const successor = selectedLocalState(result.history);
              const nextGoal = successor.goals.find((goal) => goal.name === entry.shedName) ?? successor.goals[0];
              if (nextGoal) entry.shedName = nextGoal.name;
            }
            lensProvider.refreshDoc(editor.document);
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: result.applied
                ? `${m.cmd} ${entry.shedName}: ${result.transition.validation.status} ` +
                  `(${result.transition.validation.yellowCount} open goals)`
                : `checked ${m.cmd}; successor is stored in History. ` +
                  "Select that successor in History to adopt its source projection.",
            });
            await refresh();
            postLocalHistoryState(docUri, entry);
            return;
          }
          if (m.cmd === "undo" || m.cmd === "redo") {
            const history = localShedHistories.get(docUri);
            if (!history) throw new Error("there is no local proof-state history");
            const current = selectedLocalState(history);
            let targetId: string | undefined;
            if (m.cmd === "undo") {
              targetId = current.parentStateId;
            } else {
              const next = history.edges.filter((edge) => edge.parentStateId === current.stateId);
              if (next.length === 1) targetId = next[0].successorStateId;
              else if (next.length > 1) {
                const picked = await vscode.window.showQuickPick(next.map((edge, index) => ({
                  label: `${index + 1}. ${edge.actionId} ${edge.targetName}`,
                  description: JSON.stringify(edge.arguments),
                  stateId: edge.successorStateId,
                })), { placeHolder: "Choose a local branch to redo" });
                targetId = picked?.stateId;
              }
            }
            if (!targetId) throw new Error(m.cmd === "undo" ? "there is no local state to undo to" : "there is no local branch to redo");
            await collapseInlineBeforeAdoption();
            const applied = await selectLocalState(editor, history, targetId);
            const selected = selectedLocalState(history);
            if (selected.goals.length > 0) entry.shedName = selected.goals[0].name;
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: applied ? `${m.cmd} selected a locally known proof state` :
                `proof state selected immediately; source adoption conflicted with editor changes`,
            });
            await refresh();
            postLocalHistoryState(docUri, entry);
            return;
          }
          if (m.cmd === "history") {
            const history = localShedHistories.get(docUri);
            if (!history) throw new Error("there is no local proof-state history");
            const options = [...history.states.values()].map((state) => ({
              label: `${state.stateId === history.currentStateId ? "selected · " : ""}` +
                `${state.actionLabel ?? "initial"} ${state.targetName ?? "proof state"}`,
              description: state.stateId,
              detail: state.beforeGoal ?? state.goals[0]?.goal ?? "",
              stateId: state.stateId,
            }));
            const picked = await vscode.window.showQuickPick(options,
              { placeHolder: "Select a local proof-state branch" });
            if (!picked) return;
            await collapseInlineBeforeAdoption();
            const applied = await selectLocalState(editor, history, picked.stateId);
            const selected = selectedLocalState(history);
            if (selected.goals.length > 0) entry.shedName = selected.goals[0].name;
            panel.webview.postMessage({
              cmd: "actionmsg",
              text: applied ? "selected the local proof state" :
                "selected the proof state locally; editor source conflicted and was left untouched",
            });
            await refresh();
            postLocalHistoryState(docUri, entry);
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
      existing.didChange(docUri, sourceTextWithoutExpandedView(doc));
      return existing;
    }
    const sp = ensureServerBinary();
    if (!sp) return null;
    const c = new LspClient(sp);
    await c.initialize(path.dirname(doc.uri.fsPath));
    c.didOpen(docUri, sourceTextWithoutExpandedView(doc));
    documentClients.set(docUri, c);
    return c;
  }
  ctx.subscriptions.push(
    vscode.workspace.onDidChangeTextDocument((event) => {
      const docUri = event.document.uri.toString();
      const history = localShedHistories.get(docUri);
      if (history) {
        const liveText = event.document.getText();
        const current = selectedLocalState(history);
        if (current.documentText !== liveText) {
          // VS Code Undo/Redo and File: Revert File restore text without going
          // through the webview history controls. Follow a matching snapshot
          // along this branch so the next goal query uses the represented root.
          const restored = restoredStateForDocumentText(history, liveText);
          if (restored) {
            history.currentStateId = restored.stateId;
            history.editorText = liveText;
            history.editorVersion = event.document.version;
          }
        }
      }
      const client = documentClients.get(docUri);
      client?.didChange(docUri, sourceTextWithoutExpandedView(event.document));
      const panel = openPanels.get(docUri);
      postLocalHistoryState(docUri, panel);
    })
  );
  ctx.subscriptions.push(
    vscode.workspace.onDidCloseTextDocument((doc) => {
      const docUri = doc.uri.toString();
      documentClients.get(docUri)?.shutdown();
      documentClients.delete(docUri);
      localShedHistories.delete(docUri);
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
      // Existing client history is authoritative for layouts after an
      // action. Recompiling the sidecar here could save that selected state
      // merely because the user moved to another shed in the same file.
      if (!localShedHistories.has(editor.document.uri.toString()) &&
          !(await ensureSidecar(editor.document))) return;
      lensProvider.refreshDoc(editor.document);
      try {
        await expandShed(
          editor,
          inlineClient,
          { showButtons: inlineShowButtons() },
          atOffset,
          async (client, doc, shedName) => {
            const history = await ensureLocalShedHistory(client, doc);
            const { layout } = await requestGoalLayout(
              client, history, doc.uri.toString(), shedName
            );
            return layout.box;
          }
        );
      } catch (e) {
        vscode.window.showErrorMessage(`Eponym: expand failed: ${String(e)}`);
      }
    })
  );
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.collapseShed", () => collapseShed())
  );
  // Keyboard-bound actions share the panel's immutable state graph. Collapse
  // the temporary inline text before reading or editing the document.
  async function runInlineAction(
    actionId: string, arguments_: Record<string, unknown>, label: string
  ): Promise<void> {
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
      if (!(await collapseShed())) {
        vscode.window.showErrorMessage(
          `${label} cancelled: the inline view could not be removed, so the source state is unchanged.`
        );
        return;
      }
      await ensureLocalShedHistory(client, editor.document);
      const result = await performLocalAction(
        client, editor, cur.docUri, cur.shedName, actionId, arguments_
      );
      lensProvider.refreshDoc(editor.document);
      vscode.window.showInformationMessage(result.applied
        ? `${label}: ${result.transition.validation.status} ` +
          `(${result.transition.validation.yellowCount} open goals)`
        : `${label} checked; successor is stored in History. ` +
          "Select that successor in History to adopt its source projection.");
      const panel = openPanels.get(cur.docUri);
      await panel?.refresh();
      postLocalHistoryState(cur.docUri, panel);
    } catch (e) {
      vscode.window.showErrorMessage(`${label} failed: ${String(e)}`);
    }
  }

  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.shedIntro", () =>
      runInlineAction("intro", { count: 1 }, "Intro")
    )
  );
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.shedRefine", async () => {
      const cur = currentExpanded();
      if (!cur) {
        vscode.window.showErrorMessage("Eponym: no shed expanded");
        return;
      }
      const term = await vscode.window.showInputBox({
        prompt: `Refine shed ${cur.shedName} with an Eponym term`,
        placeHolder: "e.g. zero or suc zero",
      });
      if (term !== undefined) await runInlineAction("refine", { term }, "Refine");
    })
  );
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.shedCaseSplit", async () => {
      const cur = currentExpanded();
      if (!cur) {
        vscode.window.showErrorMessage("Eponym: no shed expanded");
        return;
      }
      const variable = await vscode.window.showInputBox({
        prompt: `Case-split shed ${cur.shedName} on variable`, placeHolder: "e.g. n",
      });
      if (variable) await runInlineAction("caseSplit", { variable }, "Case-split");
    })
  );
  ctx.subscriptions.push(
    vscode.commands.registerCommand("eponym.shedGive", async () => {
      const cur = currentExpanded();
      if (!cur) {
        vscode.window.showErrorMessage("Eponym: no shed expanded");
        return;
      }
      const term = await vscode.window.showInputBox({
        prompt: `Give an Eponym term for shed ${cur.shedName}`,
        placeHolder: "e.g. zero or suc zero",
      });
      if (term !== undefined) await runInlineAction("give", { term }, "Give");
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
