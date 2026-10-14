# eponym

Loosely, epigram + nim ~= eponym. What happens if we adapt (a subset of) ideas from McBride & McKinna's influential work from 20+ years ago, as an embedded DSL for Nim? This is an exploratory work currently in progress. "Loosely" and "in progress" show up in at least a few ways.

### Deliberate points of departure

QTT instead of ETT. Idris has demonstrated the 0/1/ω approach taken. This allows support for session types, and opt-in checking of the style popularized by rust.

Linear syntax is notably different to compromise with the macro approach to embedding in Nim.

### Not yet delivered

The 2d shed interactive editing experience. I have some hope that LSP + a vscode plugin may provide an avenue to this.

## Why embedded

Eponym is deliberately *not* a standalone language.
The goal is not to build and grow a full independent compiler, stdlib, package system, community around a new language. Rather, if only _some_ of your program really calls for dependent typing, and some parts are fine with the type facilities already offered by Nim, then an embedded approach allows you to use the dependent types only where needed. I especially hope that libraries can host dependent reasoning, and use cases can get safety benefits whether or not they engage with dependent types directly.


## The elaborator pipeline

Surface text → `PreTerm` (named) → de Bruijn core terms → elaborated
`Term` with metavariables solved → checked against the QTT core.

- **`parse_surf.nim`** — hand-written surface parser (canonical front end;
  `eponymBlock` renders Nim AST to text and feeds it here, issue #144).
- **`preterm.nim`** — named preterm AST, the common interchange.
- **`unify.nim`** — Miller pattern unification for metavariables.
- **`elab.nim`** — bidirectional elaborator: `inferTm`/`checkTm`,
  implicit insertion, `data` desugaring, conversion checking.

All live in `src/eponym/`; experimental code (the old `mac_surf` Nim-AST
front end, the relational/staging work) lives in `src/experimental/`. the per-module notes are in
`src/eponym/README.md`. The interesting part is this pipeline —
the two ETT encodings (`eponym.nim`, `eponym_init.nim`) were the
starting point; the elaborator is where the research lives.

## Experiments (see `plan.org`, `decisions.org`)

1. **Surface syntax** — string parser and Nim-AST macro converge on
   `PreTerm`. Chose thin string-literal macro.
2. **De Bruijn core** — named → de Bruijn, compile-time `eponym"..."`.
3. **Metavariables** — Miller-pattern unification, holes, bidirectional
   elaboration, implicit insertion. (`unify.nim`)
4. **Extensible reduction** — `postulate`/`elim`/`red`; reduction rules
   stored in `wRed` values. Bool and Nat eliminators compute.
5. **Indexed families** — `data` declarations desugar to
   postulate/elim/red. `Vec` with length indices works.
5b. **Conversion** — `checkTm` uses full conversion (not just
   unification), so `Vec append` with `add` in indices elaborates.
6. **Tactics** — basic `refl`/`assumption`; custom tactic API (in progress).
7. **LSP** — diagnostics via Language Server Protocol; holes/goals/actions (in progress).
8. **Staging** — tagless string generation for residual code (basic; full pipeline in progress).
9. **Erasure** — QTT-lite 0-quantity erased binders (superseded by #66:
   QTT is now the core type theory, not a post-pass).
10. **Conversion cache** — exact equality-query memoization (not yet a true e-graph).
11. **Primitive types** — machine `Int` via `wRed`; Nat literal overloading (`3` instead of `suc` chains).
12. **Propositional equality** — `Eq`/`refl`/`J`; `plusReducesZ` proof works.
13. *(future)* **Polynomial functors** — functorial datatypes (Topos PolyTT).
14. **QTT core** — quantities 0/1/ω in the judgments: quantity-aware
    conversion, in-judgment enforcement at lambda/application sites,
    quantity polymorphism (#66; builds on the #64 prototype).
15. **Constructor disjointness** — `noConfusion`/`noCycle` as named
    disequality facts in unification; impossible clauses rejected
    early (#80).

## Writing eponym in Nim code

The `eponymBlock` macro lets you write Eponym directly in Nim:
```nim
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/nat.ep"   # shared prelude, not a per-file redefinition

  data(Session, Univ):
    proc sendD(A: Univ, k: A -> Session): Session
    proc recvD(A: Univ, k: A -> Session): Session
    proc endS(): Session
  ...
```
- `Univ` is `?` (universe); call syntax for declarations
  (`postulate(Int, Univ)`); `proc` not `def`; `=` not `:=` — it reads
  as Nim, and the elaborator typechecks it at compile time.
- Integer literals overload to `Nat` via `checkTm` (or primitive `Int`).
- Two-layer shape: the checked definitions are the proof layer; the
  surrounding Nim is the running layer, calling them through generated
  wrappers.
- The headline demos in `examples/embedded/` are built this way:
  `paxos_session.nim` (Paxos as dependent session types with
  unforgeable promise tickets), `convex_opt_vec.nim` (DCP-checked
  logistic regression with dimension-indexed vectors), `qtt_borrow.nim`
  (Rust-style borrow discipline checked at compile time).

## Track C: Relational × staged interpreters

One relational spec of a small language, many tools
(inference, checking, synthesis) via staging. Lives in
`src/experimental/` (issue #189) — research material, not on production
paths. The direct elaborator (`src/eponym/elab.nim`) is production; the
#143 verdict kept it that way.

- **`src/experimental/relational/minikanren.nim`** — independent
  µKanren-style engine (no elaborator deps): S-expr terms, unification
  with occurs check, explicit `Stream` tree (no call-stack recursion),
  FIFO worklist (fair search — backward `typeo` now enumerates
  all results), `=/=` disequality with a constraint store,
  `setEqo` global set-equality constraint, and
  most-constrained-first branching over constraint-derived
  domains (4×4 Sudoku in ~20ms; was a 30s timeout).
- **`src/experimental/relational/rel_elab.nim`** — `typeo` relation for STLC+Nat, plus
  a `Vec` length-indexed branch.
- **Staged tools** — each direction of the relation staged to
  direct code: inference with zero search; synthesis pruned
  by expected type (~17000x); evaluation as direct recursion
  (61x); a language-specialized engine on top (546x over the
  generic staged version).
- **`tests/lms_staging.nim`** — LMS-style: one `prog` polymorphic
  over `R`; `R = int` executes, `R = Rep` builds IR which
  constant-folds at staging time. No hand-written staged duplicate.
- **`tests/synth_staged.nim`** — `evalo` run backwards (static
  language rules, dynamic target value), staged to a direct
  recursive search (6860x), witnesses verified.

Status: experimental. See `docs/staging-design.md` for the staging architecture.

## Trust model

[docs/trust-model.md](docs/trust-model.md) states what the system checks and
guarantees — and what is your problem: `? : ?` universes (#52), unchecked
positivity of `data` declarations (#33), termination beyond single-function
structural recursion (#42), and arbitrary type-level host programs.

## Installation

Prerequisites: Nim >= 2.0 (built with 2.2.12 via
[choosenim](https://github.com/dom96/choosenim)) and nimble.

```sh
nimble install eponym        # from the nimble package directory (once published)
# or, from a checkout of this repo:
nimble install
```

This installs the production modules (`src/eponym/`, issue #189) and the
Eponym prelude (`lib/*.ep`) into the nimble package directory. Experimental
code under `src/experimental/` is deliberately not installed.

To use Eponym in your own project:

```nim
import eponym_mac   # eponymBlock macro

eponymBlock:
  import "nat.ep"   # resolves relative to THIS Nim file
  ...
```

`import "x.ep"` inside `eponymBlock` resolves relative to the Nim file
containing the block, so vendor the prelude files you need next to your
project — copy them from the installed package's `lib/` directory
(`~/.nimble/pkgs2/eponym-*/lib/`). See `examples/embedded/` for complete
examples of ordinary Nim programs using Eponym-checked definitions.

Note: on first install nimble may prompt about a package-list download or
about `src/eponym/lib` — answer yes / continue; the prelude is installed
from the package root's `lib/` directory.

## Building

Requires Nim 2.x (built with 2.2.12 via
[choosenim](https://github.com/dom96/choosenim)).

```sh
export PATH=$HOME/.nimble/bin:$PATH
P="--path:src --path:src/eponym --path:src/relational --path:src/staging"
for f in eponym eponym_init preterm parse_surf mac_surf elab eponym_mac egraph eponym_embed; do
  nim c -r --hints:off $P src/eponym/$f.nim   # build + run each test suite
done
nim c -r --hints:off $P tests/run_examples.nim            # 36 .ep examples
nim c -r --hints:off $P tests/fuzz_soundness.nim -- --seed 424242 -n 1000
# (src/eponym/lsp.nim is built but not run: it is a server that blocks on stdin.)
```

## REPL

An interactive read-eval loop — the fastest edit-check cycle for trying a
definition, querying a type, or evaluating a term:

```sh
P="--path:src --path:src/eponym --path:src/relational --path:src/staging"
nim c --hints:off $P src/repl.nim
./src/repl
```

```
eponym> :load lib/nat.ep
add : Pi(Nat, m. Pi(Nat, n. Nat))
...
eponym> proc two : Nat = suc (suc zero)
two : Nat
eponym> :type (add two two)
Nat
eponym> :eval (add (suc zero) two)
(suc (suc (suc zero)))
eponym> :quit
```

Commands: `:type <tm>`, `:eval <tm>` (weak-head normal form), `:load
<file.ep>`, `:help`, `:quit`. Anything else is Eponym source: declarations
elaborate into the persistent session and stay in scope; multi-line
declarations work, and errors print as located messages without killing the
session. A scripted session is exercised in CI (`tests/repl_session.sh`).

## Examples

Three kinds, reflecting the project's dual nature as both a standalone
elaborator and an embedded Nim library:

- **`examples/ep/`** — 36 documented `.ep` surface-syntax programs,
  the elaborator's regression suite (run by `tests/run_examples.nim`),
  from basic `twice` through indexed `Vec` with `append` to
  negative cases for the session-type and borrow demos.
- **`lib/`** — the shared prelude: `nat.ep`, `bool.ep`, `list.ep`,
  `vec.ep`, `eq.ep`, `schemes.ep`, `schemes_vec.ep` (+ machine-checked
  `nat_lemmas.ep`).
  Pulled in with `# import` header directives.
- **`examples/embedded/`** — ordinary Nim programs whose Eponym-checked
  definitions are elaborated by `eponymBlock` at compile time, then used
  from plain Nim: Paxos, DCP convex optimization, QTT borrow-checking,
  session types, sensor fusion. Each has header comments explaining
  what the dependent types are buying.

## Layout

- `src/eponym/elab.nim`, `unify.nim`, `preterm.nim`, `parse_surf.nim`,
  `mac_surf.nim` — the elaborator.
- `src/eponym/eponym.nim` — finally-tagless ETT (evaluator, printer, checker).
- `src/eponym/eponym_init.nim` — initial-encoding ETT (de Bruijn AST,
  evaluator, `infer`/`check`/`areEqual`). The elaborator's target.
- `src/eponym/lsp.nim` — language server (Experiment 7).
- `plan.org` — experiment plan and research tracks.
- `decisions.org` — design decision log.
- `research.org` — the driving question.
