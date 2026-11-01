// Minimal stdio JSON-RPC client for the eponym LSP server (issue #136).
// vscode-free: usable from extension.ts and from the node smoke test.

import { spawn, ChildProcess } from "child_process";

/** A server diagnostic in plain JSON — vscode-free so the smoke test can use this module. */
export interface ServerDiagnostic {
  range: { start: { line: number; character: number }; end: { line: number; character: number } };
  severity: 1 | 2 | 3 | 4; // 1 Error, 2 Warning, 3 Information, 4 Hint (LSP)
  message: string;
}

export interface BoxJson {
  // All fields optional: older server binaries may omit empty arrays, and
  // the renderers must not crash on a partial box (defensive ?? []/"" at
  // every read site).
  header?: string[]; // context lines above the box
  ruleLabel?: string;
  premises?: BoxJson[];
  conclusion?: BoxJson | null;
  children?: BoxJson[];
  arrange?: string;
  holeIds?: number[];
  holeGoal?: string;
  width?: number;
  height?: number;
}

export type ShedAction =
  | { kind: "refine"; target: string; arguments: { term: string } }
  | { kind: "give"; target: string; arguments: { term: string } }
  | { kind: "caseSplit"; target: string; arguments: { variable: string } };

export interface ShedTransition {
  id: number;
  proofStateVersion?: number;
  action: { id?: string; kind: string; target: string; arguments: Record<string, unknown> };
  before: { goal: string; context: string[] };
  edit: { term: string; nimLine: number; nimCol: number };
  after: { goals: Array<{ shedName: string; goal: string; status: string }> };
  validation: { accepted: boolean; status: string; yellowCount: number };
  subSheds: string[];
}

/** Submission shape used by the existing shed editor splice handlers. */
export interface SubmittedShedAction extends ShedTransition {
  shedName: string;
  term: string;
  nimLine: number;
  nimCol: number;
  status: string;
  yellowCount: number;
}

export interface AvailableShedAction {
  id: string;
  kind: string;
  label: string;
  arguments: Array<{
    name: string;
    type: string;
    required: boolean;
    choices?: Array<string | number>;
  }>;
  expectedSubgoals: Record<string, unknown>;
}

export interface AvailableShedActions {
  stateVersion: number;
  goal: string;
  context: string[];
  actions: AvailableShedAction[];
}


export interface ShedStateGoal {
  goalId: string;
  name: string;
  goal: string;
  context: string[];
  status: "white" | "yellow" | "brown";
  nimLine: number;
  nimCol: number;
}

export interface ShedStateBootstrap {
  stateId: string;
  nodes: StateNodeWire[];
  goals: ShedStateGoal[];
  environment: string;
}

export interface StateNodeWire {
  id: string;
  kind: string;
  payload: string;
  children: string[];
  byteLength: number;
}

export interface ShedStateActions {
  stateId: string;
  goalId: string;
  goal: string;
  context: string[];
  actions: AvailableShedAction[];
}

export interface ShedStateTransition {
  stateId: string;
  goalId: string;
  successorStateId: string;
  transitionId: string;
  nodes: StateNodeWire[];
  edit: { term: string; nimLine: number; nimCol: number };
  documentText: string;
  goals: ShedStateGoal[];
  validation: { accepted: boolean; status: string; yellowCount: number };
  subSheds: string[];
}

export class LspClient {
  private proc: ChildProcess;
  private buf = Buffer.alloc(0);
  private nextId = 1;
  private pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();
  private stateNodeStore = new Map<string, StateNodeWire>();
  private onDiagnostics: ((uri: string, diagnostics: ServerDiagnostic[]) => void) | null;

  constructor(
    serverPath: string,
    onDiagnostics?: (uri: string, diagnostics: ServerDiagnostic[]) => void,
  ) {
    this.onDiagnostics = onDiagnostics ?? null;
    this.proc = spawn(serverPath, [], { stdio: ["pipe", "pipe", "inherit"] });
    this.proc.stdout!.on("data", (d: Buffer) => this.onData(d));
    this.proc.on("exit", () => {
      for (const [, p] of this.pending) p.reject(new Error("server exited"));
      this.pending.clear();
    });
  }

  private onData(d: Buffer) {
    this.buf = Buffer.concat([this.buf, d]);
    for (;;) {
      const headEnd = this.buf.indexOf("\r\n\r\n");
      if (headEnd < 0) return;
      const head = this.buf.subarray(0, headEnd).toString("utf8");
      const m = /Content-Length:\s*(\d+)/i.exec(head);
      if (!m) throw new Error("missing Content-Length");
      const len = parseInt(m[1], 10);
      if (this.buf.length < headEnd + 4 + len) return;
      const body = this.buf.subarray(headEnd + 4, headEnd + 4 + len).toString("utf8");
      this.buf = this.buf.subarray(headEnd + 4 + len);
      const msg = JSON.parse(body);
      if (msg.id !== undefined && this.pending.has(msg.id)) {
        const p = this.pending.get(msg.id)!;
        this.pending.delete(msg.id);
        if (msg.error) p.reject(new Error(String(msg.error.message ?? msg.error)));
        else p.resolve(msg.result);
      }
      if (msg.method === "textDocument/publishDiagnostics") {
        const params = msg.params ?? {};
        const uri = String(params.uri ?? "");
        const diagnostics: ServerDiagnostic[] = (params.diagnostics ?? []).map((d: any) => {
          const start = d.range?.start ?? { line: 0, character: 0 };
          const end = d.range?.end ?? start;
          const sev = Number(d.severity);
          return {
            range: {
              start: { line: start.line ?? 0, character: start.character ?? 0 },
              end: { line: end.line ?? 0, character: end.character ?? 0 },
            },
            severity: (sev >= 1 && sev <= 4 ? sev : 1) as 1 | 2 | 3 | 4,
            message: String(d.message ?? "Eponym diagnostic"),
          };
        });
        this.onDiagnostics?.(uri, diagnostics);
      }
    }
  }

  request(method: string, params: any): Promise<any> {
    const id = this.nextId++;
    const body = JSON.stringify({ jsonrpc: "2.0", id, method, params });
    this.proc.stdin!.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
    return new Promise((resolve, reject) => this.pending.set(id, { resolve, reject }));
  }

  notify(method: string, params: any) {
    const body = JSON.stringify({ jsonrpc: "2.0", method, params });
    this.proc.stdin!.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
  }

  async initialize(rootUri: string): Promise<void> {
    await this.request("initialize", {
      processId: process.pid,
      rootUri,
      capabilities: {},
    });
    this.notify("initialized", {});
  }

  shedLayout(docUri: string, shedName: string): Promise<{ box: BoxJson }> {
    return this.request("eponym/shedLayout", {
      textDocument: { uri: docUri },
      shedName,
    });
  }

  /** Issue #209: shed-aware case-split (term-level via eliminators). */
  caseSplitShed(
    docUri: string,
    shedName: string,
    variable: string
  ): Promise<{
    shedName: string;
    term: string;
    nimLine: number;
    nimCol: number;
    subSheds: string[];
  }> {
    return this.request("eponym/caseSplitShed", {
      textDocument: { uri: docUri },
      shedName,
      variable,
    });
  }

  /** Issue #208: the server's codeAction path requires an open document. */
  didOpen(docUri: string, text: string): void {
    this.notify("textDocument/didOpen", {
      textDocument: { uri: docUri, text },
    });
  }

  /** Issue #208: keep the server's buffer fresh for code actions. */
  didChange(docUri: string, text: string): void {
    this.notify("textDocument/didChange", {
      textDocument: { uri: docUri },
      contentChanges: [{ text }],
    });
  }

  codeAction(docUri: string, line: number, character: number, term: string): Promise<any> {
    return this.request("textDocument/codeAction", {
      textDocument: { uri: docUri },
      range: { start: { line, character }, end: { line, character } },
      context: { diagnostics: [] },
      term,
    });
  }

  shedNames(docUri: string): Promise<string[]> {
    // Issue #137: the server now implements eponym/shedNames; keep the
    // fallback so an older server binary still yields [].
    return this.request("eponym/shedNames", { textDocument: { uri: docUri } }).catch(() => []);
  }

  refineShed(docUri: string, shedName: string, term: string,
             requireComplete = false): Promise<{
    shedName: string;
    term: string;
    nimLine: number; // 1-based start of the `![...]` node in the .nim
    nimCol: number;
    status: "white" | "yellow" | "brown";
    yellowCount: number;
  }> {
    // Issue #137: the server-owned refine round-trip. The server fills
    // the hole in the macro-recorded generated source, refreshes
    // statuses, rewrites the sidecar, and returns the term for the
    // client to splice over the shed node. Give sets requireComplete so
    // the server rejects candidates that leave holes behind.
    return this.request("eponym/refineShed", {
      textDocument: { uri: docUri },
      shedName,
      term,
      requireComplete,
    });
  }

  private rememberStateNodes(nodes: StateNodeWire[]): void {
    for (const node of nodes) this.stateNodeStore.set(node.id, node);
  }

  async createShedState(docUri: string): Promise<ShedStateBootstrap> {
    const state = await this.request("eponym/createShedState", {
      textDocument: { uri: docUri },
    }) as ShedStateBootstrap;
    this.rememberStateNodes(state.nodes);
    return state;
  }

  private async stateRequest<T>(method: string, docUri: string, stateId: string,
                                goalId: string, extra: Record<string, unknown> = {}): Promise<T> {
    const root = this.stateNodeStore.get(stateId);
    if (!root) throw new Error(`client has no Merkle root node for state ${stateId}`);
    let nodes: StateNodeWire[] = [root];
    for (let attempts = 0; attempts < 64; attempts++) {
      const result = await this.request(method, {
        textDocument: { uri: docUri }, stateId, goalId, ...extra, nodes,
      });
      if (Array.isArray(result?.needsNodes)) {
        nodes = result.needsNodes.map((id: string) => {
          const node = this.stateNodeStore.get(id);
          if (!node) throw new Error(`client is missing requested Merkle node ${id}`);
          return node;
        });
        continue;
      }
      if (Array.isArray(result?.nodes)) this.rememberStateNodes(result.nodes);
      return result as T;
    }
    throw new Error("state recovery exceeded 64 node-transfer rounds");
  }

  queryShedStateActions(docUri: string, stateId: string, goalId: string): Promise<ShedStateActions> {
    return this.stateRequest("eponym/queryShedStateActions", docUri, stateId, goalId);
  }

  transitionShedState(docUri: string, stateId: string, goalId: string,
                      actionId: string, arguments_: Record<string, unknown>): Promise<ShedStateTransition> {
    return this.stateRequest("eponym/transitionShedState", docUri, stateId, goalId,
      { action: { id: actionId, arguments: arguments_ } });
  }

  shedStateLayout(docUri: string, stateId: string, goalId: string): Promise<{
    stateId: string; goalId: string; name: string; box: BoxJson;
  }> {
    return this.stateRequest("eponym/shedStateLayout", docUri, stateId, goalId);
  }

  /** Run Refine, Give, or Case-split through the common transition contract (#429). */
  performShedAction(docUri: string, action: ShedAction): Promise<ShedTransition> {
    return this.request("eponym/performShedAction", {
      textDocument: { uri: docUri }, action,
    });
  }

  availableShedActions(docUri: string, shedName: string): Promise<AvailableShedActions> {
    return this.request("eponym/availableShedActions", {
      textDocument: { uri: docUri }, shedName,
    });
  }

  submitShedAction(
    docUri: string, shedName: string, stateVersion: number,
    actionId: string, arguments_: Record<string, unknown>
  ): Promise<SubmittedShedAction> {
    return this.request("eponym/submitShedAction", {
      textDocument: { uri: docUri }, shedName, stateVersion,
      action: { id: actionId, arguments: arguments_ },
    }).then((transition: ShedTransition): SubmittedShedAction => ({
      ...transition,
      shedName: transition.action.target,
      term: transition.edit.term,
      nimLine: transition.edit.nimLine,
      nimCol: transition.edit.nimCol,
      status: transition.validation.status,
      yellowCount: transition.validation.yellowCount,
    }));
  }

  commitShedAction(docUri: string, transitionId: number): Promise<ShedTransition> {
    return this.request("eponym/commitShedAction", {
      textDocument: { uri: docUri }, transitionId,
    });
  }

  shedActionHistory(docUri: string): Promise<{
    cursor: number;
    canUndo: boolean;
    canRedo: boolean;
    transitions: Array<ShedTransition & { applied: boolean }>;
  }> {
    return this.request("eponym/shedActionHistory", {
      textDocument: { uri: docUri },
    });
  }

  undoShedAction(docUri: string): Promise<{
    transitionId: number;
    transition: ShedTransition;
  }> {
    return this.request("eponym/undoShedAction", {
      textDocument: { uri: docUri },
    });
  }

  redoShedAction(docUri: string): Promise<ShedTransition> {
    return this.request("eponym/redoShedAction", {
      textDocument: { uri: docUri },
    });
  }

  commitShedHistoryMove(
    docUri: string, transitionId: number, direction: "undo" | "redo"
  ): Promise<{ cursor: number; transitions: Array<ShedTransition & { applied: boolean }> }> {
    return this.request("eponym/commitShedHistoryMove", {
      textDocument: { uri: docUri }, transitionId, direction,
    });
  }

  /** Introduce checked Pi binders into a shed goal (#425). */
  introShed(docUri: string, shedName: string, count = 1): Promise<{
    shedName: string;
    term: string;
    nimLine: number;
    nimCol: number;
    status: "white" | "yellow" | "brown";
    yellowCount: number;
  }> {
    return this.request("eponym/introShed", {
      textDocument: { uri: docUri },
      shedName,
      count,
    });
  }

  /** Goal-directed constructor refinement for indexed datatype goals (#426). */
  refineConstructorsShed(
    docUri: string,
    shedName: string,
    constructor?: string
  ): Promise<{
    shedName: string;
    constructors: string[];
    term: string;
    nimLine: number;
    nimCol: number;
    status: "white" | "yellow" | "brown";
    yellowCount: number;
    message?: string;
  }> {
    return this.request("eponym/refineConstructorsShed", {
      textDocument: { uri: docUri },
      shedName,
      ...(constructor ? { constructor } : {}),
    });
  }

  /** Search local hypotheses for goal-directed applications (#427). */
  refineFromContextShed(
    docUri: string,
    shedName: string,
    candidate?: string
  ): Promise<{
    shedName: string;
    candidates: string[];
    term: string;
    nimLine: number;
    nimCol: number;
    status: "white" | "yellow" | "brown";
    yellowCount: number;
    message?: string;
  }> {
    return this.request("eponym/refineFromContextShed", {
      textDocument: { uri: docUri },
      shedName,
      ...(candidate ? { candidate } : {}),
    });
  }

  /** Rewrite the shed goal using an equality proof in local context (#428). */
  refineEqualityShed(
    docUri: string,
    shedName: string,
    rewrite?: string
  ): Promise<{
    shedName: string;
    candidates: string[];
    term: string;
    nimLine: number;
    nimCol: number;
    status: "white" | "yellow" | "brown";
    yellowCount: number;
    message?: string;
  }> {
    return this.request("eponym/refineEqualityShed", {
      textDocument: { uri: docUri },
      shedName,
      ...(rewrite ? { rewrite } : {}),
    });
  }

  shutdown() {
    this.notify("exit", {});
    this.proc.kill();
  }
}
