// Scenario 3 (#502): a fixture with a known type error gets diagnostics
// published into the editor. The extension opens an LSP client for .ep
// files on open (extension.ts maybeStartEpClient); the server elaborates
// the .ep text and answers didOpen with textDocument/publishDiagnostics,
// which protocol.ts forwards via the onDiagnostics callback.
const vscode = require("vscode");
const assert = require("assert");
const path = require("path");

async function run() {
  if (!process.env.EPONYM_TEST_LSP) {
    console.log("[integration] SKIP 03-diagnostics.js: EPONYM_TEST_LSP is unset");
    return;
  }
  const fixture = path.join(__dirname, "..", "..", "fixtures", "type-error.ep");
  const doc = await vscode.workspace.openTextDocument(fixture);
  await vscode.languages.setTextDocumentLanguage(doc, "nim");
  await vscode.window.showTextDocument(doc);
  // No command needed: opening the .ep file starts the client, whose
  // didOpen triggers the server's publishDiagnostics notification.
  const deadline = Date.now() + 20000;
  let diagnostics = [];
  while (Date.now() < deadline) {
    diagnostics = vscode.languages.getDiagnostics(doc.uri);
    if (diagnostics.length > 0) break;
    await new Promise((resolve) => setTimeout(resolve, 250));
  }
  assert.ok(
    diagnostics.length > 0,
    "no diagnostics were published for the type-error fixture"
  );
  assert.ok(
    diagnostics.some((d) => d.severity === vscode.DiagnosticSeverity.Error),
    `expected a severity-Error diagnostic, got: ${JSON.stringify(
      diagnostics.map((d) => ({ severity: d.severity, message: d.message }))
    )}`
  );
}

module.exports = { run };
