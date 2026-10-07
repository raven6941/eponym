# Eponym examples

Each `.ep` file is a self-contained Eponym program. They're also the
regression suite — `run_examples.nim` elaborates each and checks it
succeeds.

## The examples

- **01-twice-const.ep** — Basic definitions (`twice`, `const`, `pairSwap`).
  Pi types, application.
- **02-myid.ep** — Identity function. Basic `def`.
- **03-let.ep** — Let bindings.
- **04-polyid-implicit.ep** — Polymorphic identity with `{A : ?}` implicit
  args. Tests implicit insertion (Experiment 3).
- **05-id-universe.ep** — Universe-polymorphic identity.
- **06-const-lam.ep** — Constant function via explicit `lam`.
- **07-bool-postulate.ep** — Booleans via `postulate`/`elim`/`red`.
  The eliminator computes (Experiment 4).
- **08-nat-postulate.ep** — Naturals via `postulate`.
- **09-data-nat.ep** — Naturals via `data`. Desugars to
  postulate/elim/red (Experiment 5). `add two two` computes to 4.
- **10-data-vec.ep** — Vectors, the indexed family. The eliminator
  computes over indices; length of a 2-element Vec is 2.
- **11-vec-append-conv.ep** — Vec `append` with `add` in the indices.
  Requires full conversion in `checkTm` (Experiment 5b), not just
  unification.
- **12-eq-plusReducesZ.ep** — Propositional equality: `Eq`, `refl`, J
  (`eqElim`), `cong`, and the `plusReducesZ` benchmark (Experiment 12).
  `refl` typechecks up to conversion.
- **13-primint.ep** — Primitive machine integers: literals and `addInt`,
  `subInt`, `mulInt` compute via host operations (Experiment 11).
  No unary `s(s(z))`.

## Running

```sh
export PATH=$HOME/.nimble/bin:$PATH
nim c -r --path:src tests/run_examples.nim
```
