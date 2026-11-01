const vscode = require("vscode");
const assert = require("assert");
const path = require("path");

async function run() {
  if (!process.env.EPONYM_TEST_LSP) {
    console.log("[integration] SKIP 02-server-initialize.js: EPONYM_TEST_LSP is unset");
    return;
  }
  const fixture = path.join(__dirname, "..", "..", "fixtures", "shed_basic.nim");
  const doc = await vscode.workspace.openTextDocument(fixture);
  const editor = await vscode.window.showTextDocument(doc);
  const markerLine = doc.getText().slice(0, doc.getText().indexOf("![basic]")).split("\n").length - 1;
  editor.selection = new vscode.Selection(markerLine, 0, markerLine, 0);
  await vscode.commands.executeCommand("eponym.expandShed");
  const deadline = Date.now() + 15000;
  while (Date.now() < deadline && !vscode.window.activeTextEditor?.document.getText().includes("?0 : Nat")) {
    await new Promise((resolve) => setTimeout(resolve, 100));
  }
  assert.ok(vscode.window.activeTextEditor?.document.getText().includes("?0 : Nat"),
    "the initialized server did not answer the shedLayout request");
  await vscode.commands.executeCommand("eponym.collapseShed");
}

module.exports = { run };
