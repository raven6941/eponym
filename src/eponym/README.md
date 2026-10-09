# Eponym elaborator (`src/eponym/`)

The dependently-typed language embedded in Nim. This is the product:
user code is ordinary Nim, with Eponym surface syntax in `ettBlock`
macros elaborated at compile time.

## Pipeline

```
Surface syntax → PreTerm → Elaboration → Core Term → (usage check) → Nim
```

1. **Surface**: Two front ends produce the same `PreTerm` AST:
   - `parse_surf.nim`: string parser for `.ep` files (`examples/ep/`)
   - `mac_surf.nim`: Nim-AST macro for `ettBlock` (embedded use)
2. **Elaboration** (`elab.nim`): bidirectional type checking (`inferTm`,
   `checkTm`) producing core `Term`s. Handles implicits, metavariables,
   unification, and conversion.
3. **Core** (`ett_init.nim`, `ett.nim`): the ETT type theory — `Term` AST
   (de Bruijn), evaluator (NbE-style with explicit environments), and
   the core typechecker. `ett.nim` is the finally-tagless alternative
   encoding; `ett_init.nim` is the initial encoding used by the elaborator.
4. **Usage check** (`usage_check.nim`): post-elaboration pass enforcing
   quantitative binder usage (Issue #64). Linear (`q1`) binders must be
   used exactly once; erased (`q0`) binders must not be used.
5. **Embedding** (`ett_mac.nim`, `ett_embed.nim`): the `ett"..."`,
   `ettEmbed`, and `ettBlock` macros plus runtime support for calling
   elaborated definitions from Nim.

## Files

- `preterm.nim` — `PreTerm` AST, `Quantity` enum (`q0`/`q1`/`qOmega`),
  `mkPi`/`mkLam` smart constructors, `desugarTy`/`desugarTm` (telescope
  to nested binders)
- `parse_surf.nim` — recursive-descent parser; `(1 x : T)` for linear,
  `(0 x : T)` for erased binders
- `mac_surf.nim` — converts Nim AST to `PreTerm` (the `ettBlock` macro)
- `elab.nim` — the elaborator: context, metas, `inferTm`/`checkTm`,
  `elabDefDecl`, `elabCheck`
- `ett_init.nim` — core `Term`, `tmPi`/`tmLam`/`tmLet` constructors,
  evaluator, `check`/`infer`/`areEqual`
- `ett.nim` — finally-tagless ETT (`Sym[R]` interface)
- `ett_mac.nim` — `ett`, `ettBlock`, `ettEmbed` macros
- `ett_embed.nim` — runtime: definition cache, `callIntFunc`
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
  produce `PreTerm`, so `.ep` files and `ettBlock`s share the elaborator.
- **Metavariables**: elaboration uses metas solved by pattern unification;
  `zonk` substitutes solutions before the core re-check.
