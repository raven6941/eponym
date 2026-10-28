# src/experimental — code not on production paths

This directory holds Eponym code that no production entry point imports.
It is research material, superseded prototypes, and benchmarks — kept for
reference, comparison, and future work, but excluded from release packaging.

## The graduation rule

Code lives here **until a production entry point imports it**. The production
entry points are: `eponym_mac`, `eponym_embed` (the `eponymBlock` macro),
`lsp` (the language server), `repl`, and `kernel_check`.

When experimental code gets used by a real path, it **graduates**: move it to
`src/eponym/` in a commit whose message notes the graduation (e.g.
"`unify.nim` graduates: the Miller unifier is now imported by `elab`").

## What's here

- `relational/` — the relational elaborator, miniKanren engine, and the
  lattice-monotone elaboration prototype (#170). The relational definitions
  are the specification; the direct elaborator in `src/eponym/` is production.
- `staging/` — staging experiments, residual-code pipeline, codegen.
- `eponym.nim` — the finally-tagless ETT encoding (the project's starting
  point; superseded by the elaborator).
- `mac_surf.nim` — front end (b) from Experiment 1 (Nim-AST surface syntax);
  the string parser (`parse_surf`) won.
- `heap.nim`, `qtt_proto.nim` — superseded prototypes.

## Building

Experimental code is not part of the production CI matrix. It builds with
the repo's usual `--path` flags plus `--path:src/experimental`,
`--path:src/experimental/relational`, `--path:src/experimental/staging`
as needed. It must not break the production build: nothing in `src/eponym/`
may import from here.
