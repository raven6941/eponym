# Eponym Sheds — VSCode extension (issue #136)

Thin client for the sheds line. The Nim LSP server (`src/eponym/lsp`)
remains the backend; this extension spawns it over stdio and renders the
`shedLayout` box tree in a webview.

## Build

```sh
cd editors/vscode
npm install
npm run build        # tsc -> out/
```

## Install

Package with vsce (`npm i -g @vscode/vsce && vsce package`) and install the
`.vsix` in VSCode, or run the Extension Development Host from this folder.

## Use

See [Working with sheds in VS Code](USER_GUIDE.md) for the inline workflow,
how to read the 2D proof state, and when to use Refine, Give, or Case-split.

In brief: open a Nim file with a `shedsBlock`, place the cursor on a `![name]`
marker, and run **Eponym: Expand inline shed view** (default shortcut
**Ctrl+Shift+S**). A CodeLens above each marker opens that specific shed.
The extension compiles the file with Nim to generate the sidecar; progress
and errors are reported in the **Eponym** Output channel. The inline view is
temporary editor text, removed before save. Refinement actions splice their
result into source and save it so the macro can refresh goals and CodeLens.

### If sidecar generation fails

The compile output goes to the **Eponym** output channel and an error
notification offers to show it. Common causes: Nim not on PATH (set the
`eponym.nimPath` setting to the Nim binary), or the file not being inside
the eponym repo checkout (the extension derives the `--path` flags from
the repo root containing `src/eponym/lsp.nim`).

### Settings

- `eponym.lspServerPath` — path to the compiled `lsp` server binary
  (defaults to `<workspace>/src/eponym/lsp`; build it with
  `nim c --hints:off --path:src --path:src/eponym src/eponym/lsp.nim`).
- `eponym.nimPath` — Nim binary used for automatic sidecar generation
  (defaults to `nim` on PATH).

## Headless smoke test

No VSCode needed; drives the real LSP server:

```sh
# from the repo root:
nim c --hints:off --path:src --path:src/eponym src/eponym/lsp.nim
cd editors/vscode && npm install && npm run build
# NIMBIN= only needed when nim is not on PATH. The smoke test drives the
# extension's own generateSidecar path to produce the sidecar (issue #153),
# so the fresh-checkout case is covered without a manual nim invocation.
LSP=../../src/eponym/lsp DEMO=../../examples/embedded/sheds_demo.nim npm run smoke
```

## Layout

- `src/protocol.ts` — minimal stdio JSON-RPC client (initialize, `eponym/shedLayout`,
  `textDocument/codeAction`). vscode-free.
- `src/render.ts` — `boxToJson` tree → nested HTML/CSS (premises above a rule
  line, hole below); hole click shows the goal. vscode-free.
- `src/sidecar.ts` — shed-block detection, repo-root discovery, and the
  `nim c` invocation that (re)generates the sidecar. vscode-free; used by
  the extension and the smoke test.
- `src/extension.ts` — VSCode glue: command, webview panel, message passing,
  applying code-action edits, automatic sidecar generation on open/save.
- `src/smoke.ts` — node smoke test asserting the full path above.
