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

## Running

```sh
export PATH=$HOME/.nimble/bin:$PATH
nim c -r run_examples.nim
```
