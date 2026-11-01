const vscode = require("vscode");
const assert = require("assert");
const path = require("path");

async function run() {
  if (!process.env.EPONYM_TEST_LSP) {
    console.log("[integration] SKIP 04-shed-roundtrip.js: EPONYM_TEST_LSP is unset");
    return;
  }
  const fixture = path.join(__dirname, "..", "..", "fixtures", "shed_basic.nim");
  const doc = await vscode.workspace.openTextDocument(fixture);
  const editor = await vscode.window.showTextDocument(doc);
  const original = doc.getText();
  const markerLine = doc.getText().slice(0, doc.getText().indexOf("![basic]")).split("\n").length - 1;
  editor.selection = new vscode.Selection(markerLine, 0, markerLine, 0);
  await vscode.commands.executeCommand("eponym.expandShed");
  assert.notStrictEqual(doc.getText(), original, "expandShed did not insert the inline view");
  assert.ok(doc.getText().includes("?0 : Nat"), "inline shed view was not rendered");
  await vscode.commands.executeCommand("eponym.collapseShed");
  assert.strictEqual(doc.getText(), original, "collapseShed did not restore the source byte-for-byte");
}

module.exports = { run };
