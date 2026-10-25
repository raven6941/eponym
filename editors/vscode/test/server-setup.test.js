"use strict";

const assert = require("assert");
const fs = require("fs");
const os = require("os");
const path = require("path");
const { buildServerBinary, discoverEponymSource, packageVersion, serverBinaryPath } = require("../out/serverSetup");

async function main() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "eponym-server-setup-"));
  try {
    const pkg = path.join(root, "eponym-0.1.0-abc123");
    const storage = path.join(root, "storage");
    fs.mkdirSync(pkg, { recursive: true });
    fs.writeFileSync(path.join(pkg, "nimblemeta.json"), JSON.stringify({
      version: 1,
      metaData: { specialVersions: ["0.1.0"] },
    }));
    assert.strictEqual(packageVersion(pkg), "0.1.0", "uses the package version from Nimble metadata");

    const source = { kind: "nimble", dir: pkg, version: "0.1.0" };
    const binary = serverBinaryPath(storage, source);
    fs.mkdirSync(path.dirname(binary), { recursive: true });
    fs.writeFileSync(binary, "cached server");
    fs.chmodSync(binary, 0o755);
    fs.writeFileSync(`${binary}.json`, JSON.stringify({
      version: "0.1.0", sourceKey: "0.1.0", sourceDir: pkg,
    }));

    const reused = await buildServerBinary("compiler-must-not-run", source, storage, root);
    assert.strictEqual(reused, binary, "reuses the binary for the installed package version");
    assert.strictEqual(fs.readFileSync(reused, "utf8"), "cached server");
    assert.ok(serverBinaryPath(storage, { ...source, version: "0.2.0" }) !== binary,
      "a package upgrade gets a fresh binary path");

    const repo = path.join(root, "repo");
    const repoSource = path.join(repo, "src", "eponym");
    const nestedWorkspace = path.join(repo, "examples", "project");
    fs.mkdirSync(repoSource, { recursive: true });
    fs.mkdirSync(nestedWorkspace, { recursive: true });
    fs.writeFileSync(path.join(repoSource, "lsp.nim"), "server source one");
    const discovered = await discoverEponymSource(nestedWorkspace);
    assert.strictEqual(discovered.kind, "repo", "finds a containing checkout");
    fs.writeFileSync(path.join(repoSource, "lsp.nim"), "server source two");
    const edited = await discoverEponymSource(nestedWorkspace);
    assert.notStrictEqual(edited.cacheKey, discovered.cacheKey,
      "repository edits invalidate the cached build key");
    console.log("--- server setup cache tests passed ---");
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
}

main().catch((error) => { console.error(error); process.exitCode = 1; });
