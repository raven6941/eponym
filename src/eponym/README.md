# Eponym elaborator (`src/eponym/`)

The dependently-typed language embedded in Nim. This is the product:
user code is ordinary Nim, with Eponym surface syntax in `eponymBlock`
macros elaborated at compile time.

## Pipeline

```
Surface syntax → PreTerm → Elaboration → Core Term → (usage check) → Nim
```

1. **Surface**: `parse_surf.nim` is the canonical front end: the string
   parser for `.ep` files (`examples/ep/`), and `eponymBlock` renders Nim
   AST to Eponym text and feeds it to the same parser (issue #144 — a
   single grammar for both contexts). The old Nim-AST front end
   (`mac_surf.nim`, Experiment 1's losing alternative) lives in
   `src/experimental/`.
2. **Elaboration** (`elab.nim`): bidirectional type checking (`inferTm`,
   `checkTm`) producing core `Term`s. Handles implicits, metavariables,
   unification, and conversion.
3. **Core** (`eponym_init.nim`, eponym.nim): the ETT type theory — `Term` AST
   (de Bruijn), evaluator (NbE-style with explicit environments), and
   the core typechecker. eponym.nim is the finally-tagless alternative
   encoding; `eponym_init.nim` is the initial encoding used by the elaborator.
4. **Usage check** (`usage_check.nim`): post-elaboration pass enforcing
   quantitative binder usage (Issue #64). Linear (`q1`) binders must be
   used exactly once; erased (`q0`) binders must not be used.
5. **Embedding** (`eponym_mac.nim`, `eponym_embed.nim`): the `eponym"..."` and
   `eponymBlock` macros plus runtime support for calling elaborated
   definitions from Nim. (The old `ettEmbed"""..."""` string-embedding
   form was dropped in Issue #115; `eponymBlock` is the single embedding
   form — Eponym code is valid Nim code.)
   `eponymBlock` supports `import "path.ep"` (Issue #131): Eponym-module
   imports resolved relative to the calling Nim file's directory, so
   embedded code shares the `lib/*.ep` prelude instead of redefining
   `Nat`/`Vec`/etc. per file. At runtime the generated wrappers
   re-elaborate through `eponym_embed.callIntFuncDir`, which resolves the
   same imports.

## Files

- `preterm.nim` — `PreTerm` AST, `Quantity` enum (`q0`/`q1`/`qOmega`),
  `mkPi`/`mkLam` smart constructors, `desugarTy`/`desugarTm` (telescope
  to nested binders)
- `parse_surf.nim` — recursive-descent parser; `(1 x : T)` for linear,
  `(0 x : T)` for erased binders
- `unify.nim` — Miller pattern unification for metavariables
- `elab.nim` — the elaborator: context, metas, `inferTm`/`checkTm`,
  `elabDefDecl`, `elabCheck`
- `eponym_init.nim` — core `Term`, `tmPi`/`tmLam`/`tmLet` constructors,
  evaluator, `check`/`infer`/`areEqual`
- `abilities.nim` — ambient abilities (Frank-style), issue #177
- `eponym_mac.nim` — `eponym`, `eponymBlock` macros
- `eponym_embed.nim` — runtime: definition cache, `callIntFunc`
- `egraph.nim` — e-graph conversion cache (Experiment 10)
- `lsp.nim` — language server (Experiment 7)
- `heap.nim` — heap for the evaluator
- `qtt_proto.nim` — standalone QTT prototype (Issue #64 experiment)
- `usage_check.nim` — linear/erased usage verification (Issue #64)

## Design notes

- **Quantities** (Issue #64): `q0` (erased), `q1` (linear), `qOmega`
  (unrestricted, default). Present on `PreTerm` and `Term` binders,
  propagated through elaboration and preserved by `zonk`. The usage
  checker is a post-pass, not part of the typing judgments — full QTT
  integration is tracked in Issue #66.
- **Two front ends, one AST**: the string parser and Nim macro both
  produce `PreTerm`, so `.ep` files and `eponymBlock`s share the elaborator.
- **Metavariables**: elaboration uses metas solved by pattern unification;
  `zonk` substitutes solutions before the core re-check.
