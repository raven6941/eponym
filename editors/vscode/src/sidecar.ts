// Sidecar generation for the Eponym sheds webview (issue #153).
// vscode-free: usable from extension.ts and from the node smoke test.
//
// The `eponymBlock` macro writes `<file>.sheds.json` at macro-expansion
// time, so the sidecar only exists after the file has been compiled with
// Nim. Rather than asking the user to run `nim c` by hand, the extension
// compiles the file itself whenever it sees shed blocks. The LSP server
// re-reads the sidecar on every request, so a regenerated sidecar is
// picked up without restarting anything.

import { execFile } from "child_process";
import * as fs from "fs";
import * as path from "path";
import type { EponymSource } from "./serverSetup";

const NIM_PATH_FLAGS = ["src", "src/eponym"];

// Issue #478: a file has sheds when an `eponymBlock:` body contains a
// shed marker. Shed-free blocks do not count: the extension must not
// recompile plain eponymBlock files on every save. (The save handler
// additionally recompiles when a sidecar exists, so a file whose sheds
// were all filled still gets its stale sidecar cleared.)
export function hasShedBlocks(text: string): boolean {
  return shedBlocks(text).some((b) => b.sheds.length > 0);
}

export function eponymRepoRoot(startDir: string): string | null {
  // Walk up from the document's directory until a directory containing
  // src/eponym/lsp.nim is found. Works even when the file is opened
  // outside the workspace root (e.g. a single .nim file in the editor).
  let dir = path.resolve(startDir);
  for (;;) {
    if (fs.existsSync(path.join(dir, "src", "eponym", "lsp.nim"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
}

/**
 * Resolve the LSP binary from a workspace nested inside the Eponym repository.
 * For an ordinary project workspace outside the repository, retain the
 * documented `<workspace>/src/eponym/lsp` fallback.
 */
export function defaultLspServerPath(workspaceDir: string): string {
  const root = eponymRepoRoot(workspaceDir) ?? path.resolve(workspaceDir);
  return path.join(root, "src", "eponym", "lsp");
}

export function sidecarCompileArgs(repoRoot: string, nimFile: string): string[] {
  const args = ["c", "--hints:off"];
  for (const p of NIM_PATH_FLAGS) args.push("--path:" + path.join(repoRoot, p));
  args.push(nimFile);
  return args;
}

/** Build args using either checkout paths or a flat Nimble package root. */
export function sidecarCompileArgsForSource(source: EponymSource, nimFile: string): string[] {
  if (source.kind === "repo" && source.repoRoot) {
    return sidecarCompileArgs(source.repoRoot, nimFile);
  }
  return ["c", "--hints:off", `--path:${source.dir}`, nimFile];
}

export interface GenerateResult {
  ok: boolean;
  error?: string;
}

// Issue #190: cursor-aware shed detection. A *shed node* is one `![ name ]`,
// `![ name, draft ]`, or residual `shedHole(name)` occurrence; a shed block
// is a top-level `eponymBlock:` statement plus its indented body (issue #478:
// sheds live in eponymBlock now; blocks without markers yield no sheds).
// Offsets are absolute character offsets into the document text.

export interface ShedNode {
  name: string;
  start: number; // offset of the shed marker
  end: number; // offset just past the marker
}

export interface ShedBlock {
  start: number; // offset of the `eponymBlock:` line start
  end: number; // offset of the first line past the indented body
  sheds: ShedNode[];
}

const SHED_NODE_RE = /!\[\s*([A-Za-z_][\w']*)(?:\s*,[^\]]*)?\]|shedHole\(\s*([A-Za-z_][\w']*)\s*\)/g;
const SHED_BLOCK_RE = /^([ \t]*)eponymBlock\s*:/;

function lineStartOffsets(text: string): number[] {
  const offs = [0];
  for (let i = 0; i < text.length; i++) if (text[i] === "\n") offs.push(i + 1);
  return offs;
}

function indentOf(line: string): number {
  const m = /^[ \t]*/.exec(line);
  return m ? m[0].length : 0;
}

export function shedBlocks(text: string): ShedBlock[] {
  const lines = text.split("\n");
  const offs = lineStartOffsets(text);
  const blocks: ShedBlock[] = [];
  for (let i = 0; i < lines.length; i++) {
    const m = SHED_BLOCK_RE.exec(lines[i]);
    if (!m) continue;
    const headIndent = m[1].length;
    // The body is the run of lines strictly more indented than the
    // `eponymBlock:` line (blank lines ride along).
    let j = i + 1;
    while (j < lines.length && (lines[j].trim() === "" || indentOf(lines[j]) > headIndent)) j++;
    const blockStart = offs[i];
    const blockEnd = offs[j] ?? text.length;
    const body = text.slice(blockStart, blockEnd);
    const sheds: ShedNode[] = [];
    SHED_NODE_RE.lastIndex = 0;
    let nm: RegExpExecArray | null;
    while ((nm = SHED_NODE_RE.exec(body)) !== null) {
      const close = nm.index + nm[0].length - 1;
      sheds.push({
        name: nm[1] ?? nm[2],
        start: blockStart + nm.index,
        end: blockStart + close + 1,
      });
    }
    blocks.push({ start: blockStart, end: blockEnd, sheds });
  }
  return blocks;
}

/** The shed marker beginning exactly at `offset`, or null. */
export function shedNodeStartingAt(text: string, offset: number): ShedNode | null {
  for (const block of shedBlocks(text)) {
    for (const shed of block.sheds) {
      if (shed.start === offset) return shed;
    }
  }
  return null;
}

/**
 * The shed node at the cursor, or null. Matches when the cursor is inside
 * the marker itself, or anywhere else on the node's line (issue
 * #203): in practice each shed lives on its proc's line
 * (`proc quad(n: Int): Int = ![quadBody, ...]`), and requiring the cursor
 * to sit inside the brackets made the cursor-aware default almost
 * undiscoverable -- every other cursor position fell through to the
 * name picker.
 */
export function shedAtCursor(text: string, offset: number): ShedNode | null {
  const offs = lineStartOffsets(text);
  let lineIdx = 0;
  for (let i = 0; i < offs.length; i++) {
    if (offs[i] <= offset) lineIdx = i;
    else break;
  }
  const lineStart = offs[lineIdx];
  const lineEnd = lineIdx + 1 < offs.length ? offs[lineIdx + 1] : text.length;
  const sheds = shedBlocks(text).flatMap((b) => b.sheds);
  // Prefer the marker containing the cursor before applying the convenient
  // same-line fallback. A line can contain several shed nodes (for example
  // `add ( ![left] ) ( ![right] )`), and returning the first same-line node
  // would make the later marker impossible to open with the cursor shortcut.
  const containing = sheds.find((s) => s.start <= offset && offset <= s.end);
  if (containing) return containing;

  // When the cursor is elsewhere on a proc line, choose the closest marker
  // on that line rather than always choosing the first one.
  return sheds
    .filter((s) => s.start >= lineStart && s.start < lineEnd)
    .sort((a, b) => Math.abs(a.start - offset) - Math.abs(b.start - offset))[0] ?? null;
}

/** The sheds of the `eponymBlock:` block containing the cursor, or []. */
export function blockShedsAtCursor(text: string, offset: number): ShedNode[] {
  for (const b of shedBlocks(text)) {
    if (b.start <= offset && offset < b.end) return b.sheds;
  }
  return [];
}

/** `<file>.sheds.json`, the sidecar the eponymBlock macro writes. */
export function sidecarPathFor(nimFile: string): string {
  return nimFile.replace(/\.nim$/, ".sheds.json");
}

/**
 * Issue #190: a sidecar is *fresh* when it exists and is at least as new
 * as the source. A fresh sidecar needs no `nim c` rerun, so the command
 * path skips generation (and background pre-rendering can trust it).
 */
export function sidecarFresh(nimFile: string): boolean {
  const sc = sidecarPathFor(nimFile);
  try {
    const src = fs.statSync(nimFile);
    const side = fs.statSync(sc);
    return side.mtimeMs >= src.mtimeMs;
  } catch {
    return false;
  }
}

export interface SidecarShed {
  name: string;
}

/** Shed names straight from the sidecar JSON (no LSP needed for the list). */
export function readSidecarShedNames(sidecarPath: string): string[] {
  try {
    const raw = JSON.parse(fs.readFileSync(sidecarPath, "utf8"));
    const sheds: any[] = Array.isArray(raw?.sheds) ? raw.sheds : [];
    return sheds.map((s) => String(s?.name ?? "")).filter((n) => n.length > 0);
  } catch {
    return [];
  }
}

/** Shed name → status straight from the sidecar JSON (white = draft filled). */
export function readSidecarShedStatuses(sidecarPath: string): Record<string, string> {
  try {
    const raw = JSON.parse(fs.readFileSync(sidecarPath, "utf8"));
    const sheds: any[] = Array.isArray(raw?.sheds) ? raw.sheds : [];
    const out: Record<string, string> = {};
    for (const s of sheds) {
      const name = String(s?.name ?? "");
      if (name.length > 0) out[name] = String(s?.status ?? "");
    }
    return out;
  } catch {
    return {};
  }
}

export function generateSidecar(
  nimBin: string,
  repoRoot: string,
  nimFile: string
): Promise<GenerateResult> {
  return runSidecarCompile(nimBin, sidecarCompileArgs(repoRoot, nimFile), repoRoot);
}

/** Generate a user's sidecar from a repo checkout or Nimble-installed source. */
export function generateSidecarForSource(
  nimBin: string,
  source: EponymSource,
  nimFile: string,
): Promise<GenerateResult> {
  const cwd = source.kind === "repo" && source.repoRoot
    ? source.repoRoot
    : path.dirname(nimFile);
  return runSidecarCompile(nimBin, sidecarCompileArgsForSource(source, nimFile), cwd);
}

function runSidecarCompile(nimBin: string, args: string[], cwd: string): Promise<GenerateResult> {
  // Compile the file (macro expansion writes the sidecar). Plain `c`,
  // not `c -r`: we need the sidecar, not the program's stdout.
  return new Promise((resolve) => {
    execFile(
      nimBin,
      args,
      { cwd, timeout: 300_000, maxBuffer: 8 * 1024 * 1024 },
      (err, stdout, stderr) => {
        if (err) {
          // Nim reports fatal errors on stderr, but choosenim shims (and
          // other wrappers) report theirs on stdout. With stderr empty
          // the real cause was previously dropped, leaving only the
          // command line -- which is how the PR #457 shard failure
          // looked like an inexplicable `nim c` failure plus an
          // unrelated server EOF trace.
          const output = (stderr && stderr.trim()) || (stdout && stdout.trim()) || "";
          let detail = (output || String(err.message || err)).trim();
          if (/ENOENT/.test(detail) || /ENOENT/.test(String(err))) {
            detail =
              `could not run '${nimBin}' (ENOENT) -- is Nim on PATH? ` +
              `Set the eponym.nimPath setting to the Nim binary.`;
          } else {
            detail = detail.split("\n").slice(-15).join("\n");
          }
          resolve({ ok: false, error: `${nimBin} ${args.join(" ")}\n${detail}` });
        } else {
          resolve({ ok: true });
        }
      }
    );
  });
}
