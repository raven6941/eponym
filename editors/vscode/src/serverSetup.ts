// Discovery and first-use compilation for the Nim LSP server. Kept free of
// VS Code APIs so package discovery and cache behavior can be tested headless.
import { execFile } from "child_process";
import { createHash } from "crypto";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { promisify } from "util";
import { eponymRepoRoot } from "./sidecar";

const execFileAsync = promisify(execFile);
const buildJobs = new Map<string, Promise<string>>();

export interface EponymSource {
  kind: "repo" | "nimble";
  dir: string;
  repoRoot?: string;
  version: string;
  cacheKey?: string;
}

export function packageVersion(dir: string): string {
  try {
    const metadata = JSON.parse(fs.readFileSync(path.join(dir, "nimblemeta.json"), "utf8"));
    const version = metadata.versionStr ?? metadata.package?.version ?? metadata.metaData?.specialVersions?.[0];
    if (typeof version === "string" && version.length) return version;
  } catch { /* Older Nimble metadata may be absent or use another format. */ }
  try {
    const nimble = fs.readFileSync(path.join(dir, "eponym.nimble"), "utf8");
    const match = /^version\s*=\s*["']([^"']+)["']/m.exec(nimble);
    if (match) return match[1];
  } catch { /* Installed packages use nimblemeta.json instead. */ }
  return path.basename(dir).replace(/^eponym-/, "") || "unknown";
}

function sourceAt(dir: string): EponymSource | null {
  return fs.existsSync(path.join(dir, "lsp.nim"))
    ? { kind: "nimble", dir, version: packageVersion(dir) }
    : null;
}

async function nimblePath(workspaceDir: string): Promise<string | null> {
  const suffix = process.platform === "win32" ? ".exe" : "";
  const home = os.homedir();
  const commands = ["nimble", path.join(home, ".nimble", "bin", `nimble${suffix}`),
    `/opt/homebrew/bin/nimble${suffix}`, `/usr/local/bin/nimble${suffix}`, `/opt/nim/bin/nimble${suffix}`];
  for (const command of commands) {
    try {
      const { stdout } = await execFileAsync(command, ["path", "eponym"], {
        cwd: workspaceDir, encoding: "utf8", timeout: 15000,
      });
      const dir = stdout.trim().split(/\r?\n/).map((line) => line.trim()).find(Boolean);
      if (dir) return path.resolve(dir);
    } catch { /* Try the next conventional Nimble location. */ }
  }
  return null;
}

function repoCacheKey(root: string): string {
  const hash = createHash("sha256");
  const dir = path.join(root, "src", "eponym");
  for (const name of fs.readdirSync(dir).filter((entry) => entry.endsWith(".nim")).sort()) {
    hash.update(name);
    hash.update(fs.readFileSync(path.join(dir, name)));
  }
  return hash.digest("hex").slice(0, 16);
}

export async function discoverEponymSource(workspaceDir: string): Promise<EponymSource | null> {
  const root = eponymRepoRoot(workspaceDir);
  if (root) {
    return { kind: "repo", dir: path.join(root, "src", "eponym"), repoRoot: root,
      version: packageVersion(root), cacheKey: repoCacheKey(root) };
  }
  const fromNimble = await nimblePath(workspaceDir);
  if (fromNimble) {
    const source = sourceAt(fromNimble);
    if (source) return source;
  }
  const nimbleDir = process.env.NIMBLE_DIR || path.join(os.homedir(), ".nimble");
  const packagesDir = path.join(nimbleDir, "pkgs2");
  try {
    const candidates = fs.readdirSync(packagesDir)
      .filter((entry) => entry.startsWith("eponym-"))
      .sort((a, b) => b.localeCompare(a, undefined, { numeric: true }));
    for (const entry of candidates) {
      const source = sourceAt(path.join(packagesDir, entry));
      if (source) return source;
    }
  } catch { /* No global Nimble package cache. */ }
  return null;
}

export function serverBinaryPath(storageDir: string, source: EponymSource, platform = process.platform): string {
  const key = source.cacheKey ?? source.version;
  const name = `lsp-${key.replace(/[^A-Za-z0-9._-]/g, "_")}${platform === "win32" ? ".exe" : ""}`;
  return path.join(storageDir, "server", name);
}

export function buildServerBinary(
  nim: string, source: EponymSource, storageDir: string, workspaceDir: string,
): Promise<string> {
  const key = `${source.kind}:${source.cacheKey ?? source.version}:${source.dir}`;
  const running = buildJobs.get(key);
  if (running) return running;
  const job = buildServerBinaryOnce(nim, source, storageDir, workspaceDir);
  buildJobs.set(key, job);
  void job.finally(() => {
    if (buildJobs.get(key) === job) buildJobs.delete(key);
  }).catch(() => undefined);
  return job;
}

async function buildServerBinaryOnce(
  nim: string, source: EponymSource, storageDir: string, workspaceDir: string,
): Promise<string> {
  fs.mkdirSync(path.dirname(serverBinaryPath(storageDir, source)), { recursive: true });
  const binary = serverBinaryPath(storageDir, source);
  const manifest = `${binary}.json`;
  try {
    const cached = JSON.parse(fs.readFileSync(manifest, "utf8"));
    fs.accessSync(binary, fs.constants.X_OK);
    if (cached.version === source.version && cached.sourceKey === (source.cacheKey ?? source.version) &&
        cached.sourceDir === source.dir) return binary;
  } catch { /* Build into extension-owned storage below. */ }

  const args = ["c", "--hints:off"];
  if (source.kind === "repo" && source.repoRoot) {
    args.push(`--path:${path.join(source.repoRoot, "src")}`,
      `--path:${path.join(source.repoRoot, "src", "eponym")}`);
  } else {
    args.push(`--path:${source.dir}`);
  }
  args.push(`--nimcache:${path.join(storageDir, "nimcache", source.cacheKey ?? source.version)}`,
    `--out:${binary}`, path.join(source.dir, "lsp.nim"));
  fs.mkdirSync(path.join(storageDir, "nimcache", source.cacheKey ?? source.version), { recursive: true });
  const cwd = source.repoRoot ?? workspaceDir;
  try {
    await execFileAsync(nim, args, {
      cwd, encoding: "utf8", maxBuffer: 16 * 1024 * 1024,
    });
    fs.writeFileSync(manifest, JSON.stringify({ version: source.version,
      sourceKey: source.cacheKey ?? source.version, sourceDir: source.dir }, null, 2));
    fs.chmodSync(binary, 0o755);
    return binary;
  } catch (error) {
    const e = error as Error & { stdout?: string; stderr?: string };
    throw new Error([e.message, e.stdout, e.stderr].filter(Boolean).join("\n"));
  }
}
