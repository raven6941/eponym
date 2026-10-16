// Sidecar generation for the Eponym sheds webview (issue #153).
// vscode-free: usable from extension.ts and from the node smoke test.
//
// The `shedsBlock` macro writes `<file>.sheds.json` at macro-expansion
// time, so the sidecar only exists after the file has been compiled with
// Nim. Rather than asking the user to run `nim c` by hand, the extension
// compiles the file itself whenever it sees shed blocks. The LSP server
// re-reads the sidecar on every request, so a regenerated sidecar is
// picked up without restarting anything.

import { execFile } from "child_process";
import * as fs from "fs";
import * as path from "path";

const NIM_PATH_FLAGS = ["src", "src/eponym"];

export function hasShedBlocks(text: string): boolean {
  return /\bshedsBlock\b/.test(text);
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

export function sidecarCompileArgs(repoRoot: string, nimFile: string): string[] {
  const args = ["c", "--hints:off"];
  for (const p of NIM_PATH_FLAGS) args.push("--path:" + path.join(repoRoot, p));
  args.push(nimFile);
  return args;
}

export interface GenerateResult {
  ok: boolean;
  error?: string;
}

// Issue #190: cursor-aware shed detection. A *shed node* is one `![ name ]`
// or `![ name, draft ]` occurrence; a *shed block* is a top-level
// `shedsBlock:` statement plus its indented body. Offsets are absolute
// character offsets into the document text.

export interface ShedNode {
  name: string;
  start: number; // offset of the `![`
  end: number; // offset just past the closing `]`
}

export interface ShedBlock {
  start: number; // offset of the `shedsBlock:` line start
  end: number; // offset of the first line past the indented body
  sheds: ShedNode[];
}

const SHED_NODE_RE = /!\[\s*([A-Za-z_][\w']*)/g;
const SHED_BLOCK_RE = /^([ \t]*)shedsBlock\s*:/;

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
    // `shedsBlock:` line (blank lines ride along).
    let j = i + 1;
    while (j < lines.length && (lines[j].trim() === "" || indentOf(lines[j]) > headIndent)) j++;
    const blockStart = offs[i];
    const blockEnd = offs[j] ?? text.length;
    const body = text.slice(blockStart, blockEnd);
    const sheds: ShedNode[] = [];
    SHED_NODE_RE.lastIndex = 0;
    let nm: RegExpExecArray | null;
    while ((nm = SHED_NODE_RE.exec(body)) !== null) {
      // The node ends at the first `]` after the name. Drafts are
      // single-line Nim expressions in practice; a bracket inside a
      // draft would truncate the range, which only affects the
      // generous cursor-containment check, not correctness.
      const close = body.indexOf("]", nm.index);
      if (close < 0) continue;
      sheds.push({
        name: nm[1],
        start: blockStart + nm.index,
        end: blockStart + close + 1,
      });
    }
    blocks.push({ start: blockStart, end: blockEnd, sheds });
  }
  return blocks;
}

/**
 * The shed node at the cursor, or null. Matches when the cursor is inside
 * the `![...]` node itself, or anywhere else on the node's line (issue
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
  for (const b of shedBlocks(text)) {
    for (const s of b.sheds) {
      if (s.start <= offset && offset <= s.end) return s;
      if (s.start >= lineStart && s.start < lineEnd) return s;
    }
  }
  return null;
}

/** The sheds of the `shedsBlock:` block containing the cursor, or []. */
export function blockShedsAtCursor(text: string, offset: number): ShedNode[] {
  for (const b of shedBlocks(text)) {
    if (b.start <= offset && offset < b.end) return b.sheds;
  }
  return [];
}

/** `<file>.sheds.json`, the sidecar the shedsBlock macro writes. */
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

export function generateSidecar(
  nimBin: string,
  repoRoot: string,
  nimFile: string
): Promise<GenerateResult> {
  // Compile the file (macro expansion writes the sidecar). Plain `c`,
  // not `c -r`: we need the sidecar, not the program's stdout.
  return new Promise((resolve) => {
    const args = sidecarCompileArgs(repoRoot, nimFile);
    execFile(
      nimBin,
      args,
      { cwd: repoRoot, timeout: 300_000, maxBuffer: 8 * 1024 * 1024 },
      (err, _stdout, stderr) => {
        if (err) {
          let detail = String(stderr || err.message || err).trim();
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
