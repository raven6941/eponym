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
- `elab_trace.nim` — structured elaboration trace for debugging (issue
  #83); see "Debugging: the elaboration trace" below
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

## Debugging: the elaboration trace (Issue #83)

When elaboration fails on a real program, the `ElabError` is only the
final verdict — it doesn't show what the elaborator tried. The trace
facility (`elab_trace.nim`) logs the decision process:
`check`/`infer` entry and exit (indentation tracks nesting),
unification attempts and failures, metavariable assignments,
implicit-argument insertions, conversion goals and handler discharges,
and quantity checks. It is the dynamic complement to issue #46, which
threads provenance into the errors themselves.

Enable it without code changes via the `EPON_TRACE` environment
variable — a comma-separated category allow-list, or `1`/`all`:

```sh
EPON_TRACE=check,unify nim c -r myprogram.nim
```

or programmatically:

```nim
import elab_trace
setElabTrace(true)                    # all categories, stderr
setElabTrace(true, {tcUnify, tcMeta})  # allow-list filter
```

This works on the `eponym`/`eponymBlock` macro path too: the macro
elaborates at compile time, and the driver reads the variable at
elaboration entry. Trace output is implementer-facing by design
(unlike `ElabError` text, which issue #34 keeps user-facing): payloads
may contain kernel-rendered terms with internal ids.

Categories: `check`, `infer`, `unify`, `meta`, `implicit`, `conv`,
`qty`. Event kinds are dotted (`check.in`, `unify.fail`, ...);
`setElabTrace(true, cats, maxDepth)` also bounds the logged nesting
depth. Tests capture structured events with `startTraceCapture` /
`stopTraceCapture` and assert on (category, kind) pairs, never on
rendered text.

Annotated example — this program fails:

```text
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
proc bad : Pi (x : Nat). Nat =
  lam (x : Type 0). x
```

```sh
$ EPON_TRACE=check,unify nim c -r bad.nim
...
check.in: pkLam <= tPi @5:3
  check.in: pkUniv <= tC @5:12
  check.out:
  unify.in: Type 0  ~  R1
    unify.fail: cannot unify tC with tR
  unify.out:
check.out:
ELABORATION FAILED: line 5, col 3: cannot unify tC with tR
```

The bare error (`cannot unify tC with tR` at 5:3) doesn't say *which*
unification failed. The trace shows it: under the lambda check at 5:3,
the domain annotation `Type 0` (elaborated at 5:12) is unified against the
expected domain `R1` (`Nat`) — the user wrote the wrong domain
annotation. A second example: on the quantity-violation fixture
`tests/error_snapshots/cases/erased-use-neg.ep`,
`EPON_TRACE=check,qty` shows `check.in: pkVar <= tV @4:18` (the body
occurrence of `x`) immediately before `qty.check: x :^q0` inside
`check.in: pkLam <= tPi @4:3` — the offending use is named and located,
where the error alone only points at the lambda.

Cost: tracing disabled adds <1% on the `.ep` example corpus
(measured; `-d:elabTraceStrip` removes the hooks entirely). Enabled
tracing costs ~1.4x, dominated by rendering the trace itself — it is a
debugging tool, not a production mode.

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
