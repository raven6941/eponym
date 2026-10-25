"use strict";

const assert = require("assert");
const os = require("os");
const path = require("path");
const { shedAtCursor, sidecarCompileArgsForSource } = require("../out/sidecar");

const source = [
  "shedsBlock:",
  "  proc branchDemo(n: Nat): Nat = add ( ![branchLeft] ) ( ![branchRight] )",
].join("\n");
const left = source.indexOf("![branchLeft]");
const right = source.indexOf("![branchRight]");

assert.strictEqual(shedAtCursor(source, left + 4)?.name, "branchLeft");
assert.strictEqual(shedAtCursor(source, right + 4)?.name, "branchRight");
assert.strictEqual(shedAtCursor(source, right + 16)?.name, "branchRight",
  "same-line fallback chooses the nearest shed marker");

const repoRoot = path.resolve(__dirname, "../../..");
const repoArgs = sidecarCompileArgsForSource({
  kind: "repo", dir: path.join(repoRoot, "src", "eponym"), repoRoot, version: "0.1.0",
}, path.join(repoRoot, "demo.nim"));
assert.ok(repoArgs.includes(`--path:${path.join(repoRoot, "src")}`));
assert.ok(repoArgs.includes(`--path:${path.join(repoRoot, "src", "eponym")}`));

const packageDir = path.join(os.tmpdir(), "nimble", "pkgs2", "eponym-0.1.0");
const projectFile = path.join(os.tmpdir(), "library-project", "demo.nim");
const packageArgs = sidecarCompileArgsForSource({
  kind: "nimble", dir: packageDir, version: "0.1.0",
}, projectFile);
assert.deepStrictEqual(packageArgs, [
  "c", "--hints:off", `--path:${packageDir}`, projectFile,
], "installed package compile uses its flat source root");

console.log("--- sidecar cursor selection tests passed ---");
