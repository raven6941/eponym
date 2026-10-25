"use strict";
// Minimal mock of the vscode API surface used by inlineShed.ts.
// Lets the expand/collapse state machine run headlessly in Node.
// This does NOT test event wiring (whether VS Code actually calls the
// callbacks) — only the handler logic. Wiring needs a real extension host.

function makeMockVscode() {
  const listeners = { selection: [] };

  class Position {
    constructor(line, character) {
      this.line = line;
      this.character = character;
    }
  }
  class Range {
    constructor(start, end) {
      this.start = start;
      this.end = end;
    }
  }
  class ThemeColor {
    constructor(id) { this.id = id; }
  }
  class EventEmitter {
    get event() { return () => ({}); }
    fire() {}
  }

  // Document model: array of lines.
  function makeDocument(initialLines) {
    let lines = [...initialLines];
    const uriStr = "file:///test.nim";
    return {
      uri: { toString: () => uriStr, fsPath: "/test.nim" },
      getText: () => lines.join("\n"),
      lineCount: () => lines.length,
      positionAt: (offset) => {
        let acc = 0;
        for (let i = 0; i < lines.length; i++) {
          if (acc + lines[i].length >= offset) return new Position(i, offset - acc);
          acc += lines[i].length + 1;
        }
        return new Position(lines.length - 1, 0);
      },
      offsetAt: (pos) => {
        let acc = 0;
        for (let i = 0; i < pos.line; i++) acc += lines[i].length + 1;
        return acc + pos.character;
      },
      lineAt: (n) => ({ text: lines[n] || "" }),
      // Test helpers (not part of vscode API):
      _getLines: () => lines,
      _applyEdit: (edits) => {
        for (const e of edits) {
          if (e.type === "insert") {
            const ins = e.text.split("\n");
            if (ins[ins.length - 1] === "") ins.pop();
            lines = [...lines.slice(0, e.pos.line), ...ins, ...lines.slice(e.pos.line)];
          } else {
            lines = [...lines.slice(0, e.range.start.line), ...lines.slice(e.range.end.line)];
          }
        }
      },
    };
  }

  function makeEditor(doc) {
    let nextEditResult = true;
    return {
      document: doc,
      selection: { active: new Position(0, 0) },
      edit: async (fn) => {
        if (!nextEditResult) {
          nextEditResult = true;
          return false;
        }
        const edits = [];
        const eb = {
          insert: (pos, text) => edits.push({ type: "insert", pos, text }),
          delete: (range) => edits.push({ type: "delete", range }),
        };
        fn(eb);
        doc._applyEdit(edits);
        return true;
      },
      _setNextEditResult: (result) => { nextEditResult = result; },
    };
  }

  const vscode = {
    Position, Range, ThemeColor, EventEmitter,
    window: {
      activeTextEditor: null,
      createTextEditorDecorationType: () => ({ dispose: () => {} }),
      onDidChangeTextEditorSelection: (fn) => {
        listeners.selection.push(fn);
        return { dispose: () => {} };
      },
      showInformationMessage: () => {},
      showErrorMessage: () => {},
    },
    workspace: {
      onDidChangeTextDocument: () => ({ dispose: () => {} }),
      onWillSaveTextDocument: () => ({ dispose: () => {} }),
    },
    commands: {
      executeCommand: () => Promise.resolve(),
      registerCommand: () => ({ dispose: () => {} }),
    },
  };

  return {
    vscode, listeners, makeDocument, makeEditor,
    // Fire a synthetic selection-change event through all registered listeners.
    fireSelection: (editor, line, character = 0) => {
      const e = {
        textEditor: editor,
        selections: [{ active: new Position(line, character) }],
      };
      for (const fn of listeners.selection) fn(e);
    },
  };
}

module.exports = { makeMockVscode };
