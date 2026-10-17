"use strict";
// Headless tests for the inline shed expand/collapse state machine.
// Runs the real compiled inlineShed.js against a mock vscode API.
// Covers: expand inserts box, cursor inside region keeps it, cursor outside
// collapses it, Escape collapses, double-expand is idempotent.
//
// Does NOT cover: whether VS Code actually fires onDidChangeTextEditorSelection
// (event wiring needs a real extension host).

const assert = require("assert");
const Module = require("module");
const path = require("path");
const { makeMockVscode } = require("./mock-vscode");

function loadInlineShed(mock) {
  const origRequire = Module.prototype.require;
  Module.prototype.require = function (id) {
    if (id === "vscode") return mock.vscode;
    if (id === "./log") return { log: () => {}, initLog: () => {} };
    if (id === "./inlineRender")
      return { renderInlineShed: () => Array(11).fill("boxline").join("\n") };
    if (id === "./sidecar")
      return {
        shedAtCursor: () => ({ name: "shuffleBody", start: 0, end: 10 }),
        sidecarPathFor: () => "",
        readSidecarShedNames: () => [],
      };
    if (id === "./protocol") return {};
    return origRequire.apply(this, arguments);
  };
  // Bust require cache so each test gets a fresh module state.
  const modulePath = path.join(__dirname, "..", "out", "inlineShed.js");
  delete require.cache[modulePath];
  const mod = require(modulePath);
  Module.prototype.require = origRequire;
  return mod;
}

function makeHarness() {
  const mock = makeMockVscode();
  const lines = [];
  for (let i = 0; i < 100; i++) lines.push(`line${i}`);
  lines[70] = "proc shuffle(x: Int): Int = ![shuffleBody]";
  const doc = mock.makeDocument(lines);
  const editor = mock.makeEditor(doc);
  // Marker offset -> line 70.
  editor.document.positionAt = (off) => new mock.vscode.Position(70, 27);
  editor.selection.active = new mock.vscode.Position(70, 5);
  mock.vscode.window.activeTextEditor = editor;
  const inlineShed = loadInlineShed(mock);
  const getClient = async () => ({ shedLayout: async () => ({ box: {} }) });
  return { mock, doc, editor, inlineShed, getClient };
}

async function testExpandInsertsBox() {
  const h = makeHarness();
  await h.inlineShed.expandShed(h.editor, h.getClient, { showButtons: true });
  assert.strictEqual(h.doc._getLines().length, 111, "11 lines inserted");
  assert.ok(h.inlineShed.currentExpanded(), "expanded state set");
  console.log("ok: expand inserts 11-line box");
}

async function testCursorInsideKeepsBox() {
  const h = makeHarness();
  await h.inlineShed.expandShed(h.editor, h.getClient, { showButtons: true });
  h.mock.fireSelection(h.editor, 73); // inside [70,81]
  await new Promise((r) => setTimeout(r, 50));
  assert.strictEqual(h.doc._getLines().length, 111, "box not collapsed");
  assert.ok(h.inlineShed.currentExpanded(), "still expanded");
  console.log("ok: cursor inside region keeps box");
}

async function testCursorOutsideCollapses() {
  const h = makeHarness();
  await h.inlineShed.expandShed(h.editor, h.getClient, { showButtons: true });
  h.mock.fireSelection(h.editor, 90); // outside [70,81]
  await new Promise((r) => setTimeout(r, 50));
  assert.strictEqual(h.doc._getLines().length, 100, "box removed");
  assert.strictEqual(h.inlineShed.currentExpanded(), null, "expanded cleared");
  console.log("ok: cursor outside region collapses box");
}

async function testCollapseCommand() {
  const h = makeHarness();
  await h.inlineShed.expandShed(h.editor, h.getClient, { showButtons: true });
  await h.inlineShed.collapseShed();
  assert.strictEqual(h.doc._getLines().length, 100, "box removed");
  console.log("ok: collapseShed removes box");
}

async function testDoubleExpandIdempotent() {
  const h = makeHarness();
  await h.inlineShed.expandShed(h.editor, h.getClient, { showButtons: true });
  await h.inlineShed.expandShed(h.editor, h.getClient, { showButtons: true });
  assert.strictEqual(h.doc._getLines().length, 111, "exactly one box");
  console.log("ok: double expand is idempotent");
}

(async () => {
  await testExpandInsertsBox();
  await testCursorInsideKeepsBox();
  await testCursorOutsideCollapses();
  await testCollapseCommand();
  await testDoubleExpandIdempotent();
  console.log("--- inline shed headless tests passed ---");
})().catch((e) => {
  console.error("FAIL:", e.message);
  process.exit(1);
});
