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

const NIM_PATH_FLAGS = ["src", "src/eponym", "src/relational", "src/staging"];

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
