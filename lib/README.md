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
- **nat_to_int.ep** — explicit `natToInt : Nat -> Int`. Importing it also
  declares the primitive `Int` type and imports `nat.ep`. Use the conversion
  when a checked natural number must be passed to an Int-taking operation;
  Eponym does not insert this conversion implicitly.
- **eq.ep** — propositional equality: `Eq` (indexed family), `refl`,
  `cong`, `sym`, `trans`.
- **bool.ep** — `Bool`, `not`/`and`/`or`; lemma `notNot`.
- **list.ep** — `List`, `map`/`append`/`length`; lemmas `mapId`,
  `mapComp` (fusion), `appendAssoc`, `appendNilR`, `lengthAppend`.
- **nat_lemmas.ep** — `addZeroR`/`addSucR` (induction), `addComm`/`addAssoc`
  (`by arith`, #41), `mulZeroR`, plus the computational check
  `twoPlusTwoIsFour` (`by refl` — `add 2 2` really computes to `4`).
- **vec.ep** — `Vec` (length-indexed), `vappend`, `vmap`, `vmapId`
  (map-identity, by induction — #125 showed the earlier failure was an
  ill-typed repro, not an elaborator bug).
- **schemes.ep** — recursion schemes over Nat/List (#48): `cataNat`,
  `cataList` (the eliminators, renamed), `anaList` (fuel-bounded unfold),
  `replicate`, `pred`, `isZero`; laws `cataNatRefl` (reflection),
  `cataMapFusion` (fold-after-map = fold with composed algebra),
  `hyloLenRepLaw`/`deforestLenRep` (deforestation:
  `length (replicate n x) = n`, fused = `fusedLenRep`).
- **schemes_vec.ep** — recursion schemes over Vec (#48): `cataVec`,
  `vmapFusion` (`vmap g (vmap f xs) = vmap (g . f) xs`). Lives in its own
  module because List's and Vec's `nil`/`cons` collide under unqualified
  import (see below).

Import graph: `bool.ep` → `eq`; `list.ep` → `nat`, `eq`;
`nat_lemmas.ep` → `nat`, `eq`; `vec.ep` → `nat`, `eq`;
`schemes.ep` → `nat`, `bool`, `list`, `eq`;
`schemes_vec.ep` → `nat`, `vec`, `eq`.
`Eq` lives in its own module so importing both `nat`-lemmas and
`list`-lemmas never defines it twice.

## Name collisions under unqualified import

`import` merges unqualified into one environment (decisions.org: flat
imports for v1). The first real collision arrived with #48: `list.ep`
and `vec.ep` both declare `nil`/`cons` constructors, so no single module
can import both — hence `schemes.ep` (Nat/List) and `schemes_vec.ep`
(Vec) are separate modules, and no example imports both. Workaround for
now: split modules along datatype-family lines. Qualified imports would
fix this properly; that is a follow-up, not v1.

## Conventions

- Keep modules small and dependency-light; this is a prelude, not a
  package manager.
- Every module must elaborate standalone — `run_examples.nim` walks
  `lib/` as part of the regression suite.
- Examples that *test the mechanism itself* (e.g. `09-data-nat.ep` tests
  `data` desugaring, `08-nat-postulate.ep` tests the postulate form) stay
  self-contained and do not import.
