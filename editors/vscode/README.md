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

1. Open a `.nim` file containing a `shedsBlock` and compile it once with Nim
   so the macro writes the `<file>.sheds.json` sidecar.
2. Run **Eponym: Show shed layout** (`eponym.showShedLayout`), enter the shed
   name (e.g. `quadBody` in `examples/embedded/sheds_demo.nim`).
3. The webview renders the shed's proof state as Epigram-style 2D boxes.
   Click a hole (`?n`) to see its goal type.

Hole actions (refine / give / case-split) send `textDocument/codeAction`
requests to the server and apply the returned edits, then re-render. For
`.nim` shed docs the round-trip is not yet closed — the server's action path
elaborates the document text as Eponym source, which a `.nim` file is not.
Closing the loop (edit the shed draft, recompile, re-render) is issue #137.

## Headless smoke test

No VSCode needed; drives the real LSP server:

```sh
# from the repo root:
nim c --hints:off --path:src --path:src/eponym --path:src/relational \
  --path:src/staging src/eponym/lsp.nim
nim c -r --hints:off --path:src --path:src/eponym --path:src/relational \
  --path:src/staging examples/embedded/sheds_demo.nim   # writes sidecar
cd editors/vscode && npm run build
LSP=../../src/eponym/lsp DEMO=../../examples/embedded/sheds_demo.nim npm run smoke
```

## Layout

- `src/protocol.ts` — minimal stdio JSON-RPC client (initialize, `eponym/shedLayout`,
  `textDocument/codeAction`). vscode-free.
- `src/render.ts` — `boxToJson` tree → nested HTML/CSS (premises above a rule
  line, hole below); hole click shows the goal. vscode-free.
- `src/extension.ts` — VSCode glue: command, webview panel, message passing,
  applying code-action edits.
- `src/smoke.ts` — node smoke test asserting the full path above.
