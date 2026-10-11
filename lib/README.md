# Eponym common library (`lib/`)

Shared Eponym definitions that would otherwise be copy-pasted into every
example (issue #114). Each module is a `.ep` file in the surface syntax.

## Using the library from an example

Add an `import` declaration with a path relative to the importing file
(issue #49). From `examples/ep/`:

```
import "../../lib/nat.ep"
```

From inside `lib/` itself, a bare filename suffices:

```
import "nat.ep"
```

Imports elaborate recursively and merge **unqualified** into one
environment (decisions.org: flat imports for v1; revisit on the first
name collision). Import cycles are a located error naming the files in
the cycle; a missing file reports the resolved path and the importing
chain. `tests/run_examples.nim` elaborates every file with
`elabCheckFile`, so real `import` declarations are exercised by CI.

## Modules

- **nat.ep** — `Nat` (`data` with `zero`/`suc`), `add`, `mul`.
  `add` recurses on its first argument (Idris's `plus` — `add zero n` ≡ `n`
  definitionally, which `append`'s motive relies on); `mul` is defined via
  `add`.
- **eq.ep** — propositional equality: `Eq` (indexed family), `refl`,
  `cong`, `sym`, `trans`.
- **bool.ep** — `Bool`, `not`/`and`/`or`; lemma `notNot`.
- **list.ep** — `List`, `map`/`append`/`length`; lemmas `mapId`,
  `mapComp` (fusion), `appendAssoc`, `appendNilR`, `lengthAppend`.
- **nat_lemmas.ep** — `addZeroR`/`addSucR` (induction), `addComm`/`addAssoc`
  (`by arith`, #41), `mulZeroR`, plus the computational check
  `twoPlusTwoIsFour` (`by refl` — `add 2 2` really computes to `4`).
- **vec.ep** — `Vec` (length-indexed), `vappend`, `vmap`.
  (`vmapId` omitted: hits an eliminator-motive bug, see the note in
  `vec.ep` and the follow-up issue.)

Import graph: `bool.ep` → `eq`; `list.ep` → `nat`, `eq`;
`nat_lemmas.ep` → `nat`, `eq`; `vec.ep` → `nat`, `eq`.
`Eq` lives in its own module so importing both `nat`-lemmas and
`list`-lemmas never defines it twice.

## Conventions

- Keep modules small and dependency-light; this is a prelude, not a
  package manager.
- Every module must elaborate standalone — `run_examples.nim` walks
  `lib/` as part of the regression suite.
- Examples that *test the mechanism itself* (e.g. `09-data-nat.ep` tests
  `data` desugaring, `08-nat-postulate.ep` tests the postulate form) stay
  self-contained and do not import.
