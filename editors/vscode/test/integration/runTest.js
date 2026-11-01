// Integration test launcher for issue #502.
//
// Launches a real VS Code desktop build (downloaded + cached by
// @vscode/test-electron) under Xvfb, loads this extension from source
// (extensionDevelopmentPath), opens the fixture workspace, and runs
// test/integration/suite inside the extension host.
//
// Usage (headless Linux):
//   EPONYM_TEST_LSP=/path/to/lsp xvfb-run -a npm run test:integration
//
// EPONYM_TEST_LSP: prebuilt LSP server binary. CI builds it with
// `nim c src/eponym/lsp.nim` and points the tests at it via the
// `eponym.lspServerPath` workspace setting written below. When unset,
// scenarios that need a server are skipped with a clear message
// (the extension shows its own error UI in that case).
const path = require("path");
const fs = require("fs");
const { runTests, downloadAndUnzipVSCode } = require("@vscode/test-electron");

// On this dev VM tar cannot chown the archived files to uid 1000, so
// downloadAndUnzipVSCode's extraction exits nonzero even though every file
// lands on disk. This wrapper treats that specific failure as success when
// the extracted binary is actually present, and stamps the is-complete
// marker so later runs skip the download entirely.
async function ensureVSCode(version) {
  const extRoot = path.resolve(__dirname, "../..");
  const cachePath = path.join(extRoot, ".vscode-test");
  try {
    return await downloadAndUnzipVSCode({ version, cachePath });
  } catch (e) {
    const dir = path.join(cachePath, `vscode-linux-x64-${version}`);
    const bin = path.join(dir, "code");
    if (/Failed to (download and )?unzip/.test(String(e && e.message)) && fs.existsSync(bin)) {
      fs.writeFileSync(path.join(dir, "is-complete"), "");
      return bin;
    }
    throw e;
  }
}

async function main() {
  const extensionDevelopmentPath = path.resolve(__dirname, "../..");
  const extensionTestsPath = path.resolve(__dirname, "suite");
  const workspaceFile = path.resolve(__dirname, "fixtures", "workspace.code-workspace");
  const userDataDir = path.resolve(__dirname, ".vscode-test-user-data");
  const extensionsDir = path.resolve(__dirname, ".vscode-test-extensions");

  // The extension reads eponym.lspServerPath; seed it into a FRESH throwaway
  // profile so tests never depend on the developer's real VS Code settings
  // — and so a stale single-instance socket from a previous run cannot
  // crash startup (seen 2026-11-01: ENOENT unlinking 1.85-main.sock).
  fs.rmSync(userDataDir, { recursive: true, force: true });
  const settingsDir = path.join(userDataDir, "User");
  fs.mkdirSync(settingsDir, { recursive: true });
  const lsp = process.env.EPONYM_TEST_LSP || "";
  fs.writeFileSync(
    path.join(settingsDir, "settings.json"),
    JSON.stringify({ "eponym.lspServerPath": lsp }, null, 2)
  );

  // Pin the VS Code version for reproducibility; the archive is cached
  // under .vscode-test/ between runs (CI should cache that directory).
  const version = process.env.EPONYM_TEST_VSCODE_VERSION || "1.85.0";
  const executablePath = await ensureVSCode(version);

  await runTests({
    vscodeExecutablePath: executablePath,
    extensionDevelopmentPath,
    extensionTestsPath,
    launchArgs: [
      workspaceFile,
      "--user-data-dir", userDataDir,
      "--extensions-dir", extensionsDir,
      "--disable-workspace-trust", // fixtures are ours; skip the trust prompt
      "--no-sandbox", // containers lack the user namespaces for the sandbox
      "--disable-setuid-sandbox", // also disable Chromium's setuid helper
      "--disable-gpu", // software rendering under Xvfb
    ],
    extensionTestsEnv: { EPONYM_TEST_LSP: lsp },
  });
}

main().catch((e) => {
  console.error("integration tests failed:", e);
  process.exit(1);
});
