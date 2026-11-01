// Scenario 1 (#502): the extension activates when a .ep fixture is opened
// with the nim language, and stays active for later scenarios.
const vscode = require("vscode");
const assert = require("assert");
const path = require("path");

const EXT_ID = "raven6941.eponym-sheds";

async function run() {
  const ext = vscode.extensions.getExtension(EXT_ID);
  assert.ok(ext, `extension ${EXT_ID} is not installed in the test host`);

  // Do NOT call ext.activate() directly: the point is that opening a .ep
  // file as nim fires the onLanguage:nim activation event.
  const fixture = path.join(__dirname, "..", "..", "fixtures", "hello.ep");
  const doc = await vscode.workspace.openTextDocument(fixture);
  await vscode.languages.setTextDocumentLanguage(doc, "nim");
  await vscode.window.showTextDocument(doc);

  // Activation is async; poll briefly instead of sleeping a fixed time.
  const deadline = Date.now() + 15000;
  while (!ext.isActive && Date.now() < deadline) {
    await new Promise((r) => setTimeout(r, 250));
  }
  assert.ok(ext.isActive, "extension did not activate on opening a .ep file as nim");
}

module.exports = { run };
