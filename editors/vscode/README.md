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
`.vsix` in VSCode. To run the current source in an Extension Development Host,
open `editors/vscode` as the workspace and press **F5**. The launch profile
builds both the extension and the Nim LSP server, opens the repository and
`sheds_walkthrough.nim`, and starts the extension against that workspace. The
server path defaults to the
nearest Eponym repository root, so the extension subdirectory uses the
repository's source. On first use the extension compiles the LSP into its
VS Code global storage. Outside a checkout, it finds the Eponym package from
Nimble; users need Nim and an installed Eponym package (`nimble install
eponym`). `eponym.lspServerPath` can still point at an existing server binary.
Nim must also be available for sidecar generation.

## Use

See [Working with sheds in VS Code](USER_GUIDE.md) for the inline workflow,
how to read the 2D proof state, and when to use Refine, Give, or Case-split.
The inline view also provides goal-directed **Apply**, **Construct**, and
**Rewrite** pickers for local hypotheses, datatype constructors, and equality
transport.
For datatype goals, **Construct** lists constructors whose typed applications
the elaborator accepts for the goal, then opens the constructor's fields as
ordinary sheds. This is goal-directed refinement; case-split remains the
separate action for eliminating a value already in scope.

In brief: open a Nim file with a `shedsBlock`, place the cursor on a `![name]`
marker, and run **Eponym: Expand inline shed view** (default shortcut
**Ctrl+Shift+S**). A CodeLens above each marker opens that specific shed.
The extension compiles the file with Nim to generate the sidecar; progress
and errors are reported in the **Eponym** Output channel. The inline view temporarily inserts preview text below the marker; it is
removed when collapsed and before a normal save. Actions are evaluated from
client-selected Merkle proof states. Refine, Give, Case-split, Intro, Construct,
Apply, and Rewrite return checked successor states without saving the file.
Undo selects a locally known parent immediately, and Redo can select a local
successor branch. Saving persists the selected Nim source and refreshes goals
and CodeLens. If the editor changed independently, source projection is left
untouched while the selected proof-state branch remains available.

### Syntax support and releases

This extension adds the shed editing UI for Nim files. It does not ship a
separate Eponym grammar, snippets, or syntax diagnostics; Eponym parsing and
checking remain in the Nim macro and language-server backend. The extension's
Nim language configuration pairs square brackets, including the explicit
parameter syntax used by current Eponym programs. Its headless smoke test
checks that configuration and compiles a representative `shedsBlock` using
bracketed generic declarations and calls before exercising its sidecar with
the real Eponym language server.

The current surface-syntax changes do not change the extension's UI or
protocol, so they do not require an extension version bump or a separate
Marketplace release. Bump and publish the extension when its own behavior or
the server-extension protocol changes.

### If sidecar generation fails

The compile output goes to the **Eponym** output channel and an error
notification offers to show it. Common causes: Nim not on PATH (set the
`eponym.nimPath` setting to the Nim binary), or the file not being inside
the eponym repo checkout (the extension derives the `--path` flags from
the repo root containing `src/eponym/lsp.nim`).

### Settings

- `eponym.lspServerPath` — path to the compiled `lsp` server binary
  (optional; by default the extension discovers source in the nearest Eponym
  checkout or via Nimble and builds a versioned server in extension storage).
- `eponym.nimPath` — Nim binary used for automatic sidecar generation
  and LSP setup (defaults to `nim` on PATH).

### First-use LSP setup

With no explicit server path, the extension searches a containing Eponym
checkout first, then `nimble path eponym`, then Nimble's package cache. It
compiles `lsp.nim` once into VS Code global storage, keyed by the source package
version, and reuses that binary until the installed version changes. The
compile runs with a progress notification; details are available from the
Eponym output channel if setup fails. A fresh user profile therefore needs
Nim 2.0+ and `nimble install eponym`, but does not need this repository checkout
or a manually built server binary.

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

The inline expand/collapse state machine also has a headless test:

```sh
npm run test:headless
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
