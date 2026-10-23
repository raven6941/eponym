// Minimal stdio JSON-RPC client for the eponym LSP server (issue #136).
// vscode-free: usable from extension.ts and from the node smoke test.

import { spawn, ChildProcess } from "child_process";

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

export class LspClient {
  private proc: ChildProcess;
  private buf = Buffer.alloc(0);
  private nextId = 1;
  private pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();

  constructor(serverPath: string) {
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
      // notifications (e.g. publishDiagnostics) are ignored here
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

  shutdown() {
    this.notify("exit", {});
    this.proc.kill();
  }
}
