# [Eponym](https://github.com/raven6941/eponym)

Loosely, Epigram + Nim ~= Eponym. 
What if we took the influential system built by McBride and McKinna some 20 years ago, and implemented (some of) its ideas in Nim macros/metaprogramming?
Eponym brings dependent types and quantitative type checking to Nim as an embedded DSL, so you can check the parts of a Nim program that benefit from stronger guarantees.

**New here?** Start with the [tutorial](docs/tutorial.md) (from an installed
Nim toolchain to your first checked dependent type, ~15 minutes), look up any
language form in the [surface-syntax reference](docs/surface-syntax-reference.md), and read the
[trust model](docs/trust-model.md) to see what the system checks — and what
is your problem.

See [known limitations](docs/known-limitations.md) for the current Nim
runtime boundary, supported embedding surface, and code-generation gaps.
See the [release notes](docs/release-notes.md) for user-visible behavior
changes.

### Deliberate points of departure

QTT instead of ETT. Idris has demonstrated the 0/1/ω approach taken. This allows support for session types, and opt-in checking of the style popularized by rust.

Linear syntax is notably different to compromise with the macro approach to embedding in Nim.

## Use cases

Eponym can encode and check correctness properties on just the libraries and pathways that need it, while code for specific use cases can remain in normal Nim. The examples
show a few useful patterns:

- **Protocol state and message order** — model a session as a type and make
  invalid operations, such as sending after close or accepting a value that
  was not promised, fail during compilation. See
  [`session_types.nim`](examples/embedded/session_types.nim) and
  [`paxos_session.nim`](examples/embedded/paxos_session.nim). The smaller
  [`session_runtime_bindings.nim`](examples/embedded/session_runtime_bindings.nim)
  demo also runs checked sender/receiver roles through Nim channel adapters
  with a small Nat message codec. [`session_tcp_bindings.nim`](examples/embedded/session_tcp_bindings.nim)
  applies the same roles and codec to a loopback TCP socket, returning
  transport and codec failures as explicit result values.
- **Dimensions and shapes** — index vectors and matrices by their dimensions
  so operations like dot product and matrix-vector multiplication require
  compatible sizes. See [`convex_opt_vec.nim`](examples/embedded/convex_opt_vec.nim).
- **Mathematical certificates** — require a proof that an expression follows
  convexity rules before passing it to an optimizer. See
  [`convex_opt.nim`](examples/embedded/convex_opt.nim) and
  [`convex_opt_vec.nim`](examples/embedded/convex_opt_vec.nim).
- **Resource use and borrowing** — check that a borrow is used exactly once,
  that its owner is not used while borrowed, and that the borrow does not
  escape its scope. See [`qtt_borrow.nim`](examples/embedded/qtt_borrow.nim).
- **Interactive proof development** — explore goals and contexts in the
  editor, then refine, finish, or split a proof into cases. See the
  [shed walkthrough](examples/embedded/sheds_walkthrough.nim).

Most examples show compile-time checking of Eponym models. The runtime bridge
generates typed Nim wrappers across the codec coverage documented on the
[known limitations](docs/known-limitations.md) page: primitive `Int`, `Nat`,
and `Bool`, explicitly mapped opaque postulated types, non-dependent `Sig`
pairs, named records, the standard `Vec`, `List`, and `Option` types, and —
with codecs registered — nested and indexed structures, dynamic values, and
callbacks. The new session runtime demo connects checked roles to Nim
adapters, and `paxos_session.nim` runs its checked proposer and acceptor
through bound TCP adapters. `qtt_borrow.nim` calls the checked
`borrowClient(Buffer)` through bound Nim postulates; the adapter still owns
buffer aliasing and lifetime. The convex optimization examples interpret the
exact checked objective through the runtime Value bridge, then use a
host-side solver. The buffer adapter, objective interpreters, solver, and
numerical behavior remain trusted Nim responsibilities. The
[known limitations](docs/known-limitations.md) page summarizes what Eponym
checks, which definitions have generated runtime wrappers, and which parts
of the Nim boundary remain trusted or disconnected.

## Why embedded

Eponym is deliberately *not* a standalone language.
The goal is not to build and grow a full independent compiler, stdlib, package system, community around a new language. Rather, if only _some_ of your program really calls for dependent typing, and some parts are fine with the type facilities already offered by Nim, then an embedded approach allows you to use the dependent types only where needed. I especially hope that libraries can host dependent reasoning, and use cases can get safety benefits whether or not they engage with dependent types directly.

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
- The block uses Eponym's language through Nim-shaped syntax; it does not
  execute arbitrary Nim code. The current accepted forms and the proposed
  pure-Nim-subset experiment are described in the
  [surface-syntax reference](docs/surface-syntax-reference.md) and
  [experiment note](docs/pure-nim-subset-experiment.md).
- `Univ` maps to `Type 0`; `?` introduces holes and `_` discards; call syntax for declarations
  (`postulate(Int, Univ)`); `proc` not `def`; `=` not `:=` — it reads
  as Nim, and the elaborator typechecks it at compile time.
- Integer literals overload to `Nat` via `checkTm` (or primitive `Int`).
- Two-layer shape: the checked definitions are the proof layer; the
  surrounding Nim is the running layer. Checked definitions compile to
  native Nim procs, per definition: the Value backend (boxed runtime
  values) covers everything in the compiled fragment, including
  dependent and indexed definitions such as the Paxos session roles;
  the representation backend emits direct host code where a
  representation mapping applies (`Int`/`Nat`/`Bool` as `int`,
  `Vec`/`List` as `seq[int]`, `Option` as `Option[int]`, with
  destination-passing folds for sequence eliminators). Definitions
  outside the fragment keep an interpreter fallback.
  `-d:eponymCodegenReport` names each definition's backend and why it
  did not reach a higher one, and `requireCompiled()` makes a block
  fail at macro time unless every local definition and call compiles
  without the interpreter or the `Value` layer. The
  [known limitations](docs/known-limitations.md) page carries the
  current backend coverage and the trust boundary.
- The headline demos in `examples/embedded/` are built this way:
  `paxos_session.nim` (Paxos as dependent session types with
  unforgeable promise tickets), `convex_opt_vec.nim` (DCP-checked
  logistic regression with dimension-indexed vectors), `qtt_borrow.nim`
  (Rust-style borrow discipline checked at compile time).


## Installation

Prerequisites: Nim 2.2 (tested with 2.2.12 via
[choosenim](https://github.com/dom96/choosenim)) and nimble. Older
2.x versions may work but are untested.

```sh
nimble install https://github.com/raven6941/eponym   # until the package is published
nimble install eponym        # from the nimble package directory (once published)
# or, from a checkout of this repo:
nimble install
```

Note: installing from the URL tracks the default branch until the
first release is tagged, so repeat installs can move under you.

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

Relative `import "x.ep"` paths first resolve beside the Nim file containing
the block, then fall back to the installed package's `lib/` directory. You
can use a project-local `.ep` file to override a prelude by keeping the same
relative path, or use an absolute import path for an explicit location. See
`examples/embedded/` for complete examples of ordinary Nim programs using
Eponym-checked definitions.

Note: on first install nimble may prompt about a package-list download or
about `src/eponym/lib` — answer yes / continue; the prelude is installed
from the package root's `lib/` directory. Eponym's property-test library is
not needed to install or use Eponym; the CI script installs it separately.

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

Commands:
- `:type <tm>`,
- `:eval <tm>` (weak-head normal form),
- `:load<file.ep>`,
- `:help`,
- `:quit`. 

Anything else is Eponym source: declarations
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

## Editor support

Eponym includes a Language Server Protocol (LSP) server and a [VS Code
extension](https://marketplace.visualstudio.com/items?itemName=raven6941.eponym-sheds) for interactive development with sheds. The extension shows each
goal with its context in an inline 2D view, and provides seven checked actions
that create client-selected proof-state branches. Undo selects a known prior
state immediately; save the chosen source projection to persist it and refresh
the sidecar.

- Try the [shed walkthrough](examples/embedded/sheds_walkthrough.nim) for
  guided examples of the editor actions.
- Find setup and usage instructions in the [VS Code extension guide](editors/vscode/README.md)
  and [user guide](editors/vscode/USER_GUIDE.md).
- Browse the [extension source](editors/vscode/).
- The Nim LSP implementation is in [`src/eponym/lsp.nim`](src/eponym/lsp.nim).

<img width="520" height="289" alt="Screenshot 2026-10-17 at 9 44 08 AM" src="https://github.com/user-attachments/assets/cab4c01c-d761-4d11-9f9a-2bc5c9e2e54f" />
*example shed view*

## Trust model

[docs/trust-model.md](docs/trust-model.md) states what the system checks and
guarantees — and what is your problem: explicit `Type l` universes (#52), unchecked
positivity of `data` declarations (#33), termination beyond single-function
structural recursion (#42), and arbitrary type-level host programs.  

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
- [`.github/ISSUE_TRIAGE.md`](.github/ISSUE_TRIAGE.md) — issue labels, evidence
  status, and claiming conventions.
