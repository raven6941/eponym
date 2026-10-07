# eponym

Experiments in the design space around Epigram's Type Theory (ETT),
following Chapman, Altenkirch & McBride, "Epigram Reloaded: A Standalone
Typechecker for ETT" (TYPES 2006).

## Contents

- **`ett.nim`** — ETT in the finally-tagless style: the language is an
  interface `Sym[R]` over an abstract representation type, with three
  instances:
  1. an evaluator (host closures + β-reduction),
  2. a pretty-printer,
  3. a bidirectional typechecker (`Checked` = term + inferred type,
     neutrals with elimination spines, type-directed conversion with
     proof-irrelevance of `1`/`O` and η for Π/Σ).
- **`ett_init.nim`** — the same language with an *initial* encoding:
  concrete `Term` AST with de Bruijn indices (paper §6.4), glued values
  with an explicit-environment evaluator (§6.6), and `infer` / `check` /
  `areEqual` over closed terms (§§6.5, 6.7). No pretty-printer needed —
  `$` dumps the AST records.

Both share the same example programs (`twice`, `polyId`, `const`,
`pairSwap`, …) and test suites.

## Building

Requires Nim 2.x (built with 2.2.12 via [choosenim](https://github.com/dom96/choosenim)).

```sh
export PATH=$HOME/.nimble/bin:$PATH
nim c -r ett.nim        # finally-tagless: 16 tests
nim c -r ett_init.nim   # initial encoding: 16 tests
```
