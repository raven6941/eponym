# Eponym examples

Three kinds of examples, reflecting Eponym's dual nature as both a
standalone elaborator and an embedded Nim library.

## `../lib/` — Common library (Issue #114)

Shared definitions that would otherwise be copy-pasted into every
example — currently `nat.ep` (`Nat`, `add`, `mul`). An example pulls a
module in with a header directive:

```
# import nat
```

`run_examples.nim` prepends the module's source before elaboration, so
each `.ep` file is still a single standalone elaboration unit. Examples
that test the definition mechanism itself (`08-nat-postulate.ep`,
`09-data-nat.ep`) stay self-contained and do not import.

## `ep/` — Elaborator regression tests

Each `.ep` file is a self-contained Eponym program in the surface syntax.
They're the regression suite — `run_examples.nim` elaborates each and
checks it succeeds. These test the elaborator in isolation.

- **01-twice-const.ep** — Basic definitions (`twice`, `const`, `pairSwap`).
  Pi types, application.
- **02-myid.ep** — Identity function. Basic `def`.
- **03-let.ep** — Let bindings.
- **04-polyid-implicit.ep** — Polymorphic identity with `{A : Type 0}` implicit
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
- **14-tactics.ep** — Tactics: `by refl` proves equalities by reflexivity,
  `by assumption` finds a matching hypothesis (Experiment 6).
- **15-session-types.ep** — Session types with linear channels (Issue #28,
  #64). The `(1 ch : Chan ...)` binders ensure channels are used exactly
  once; the affinity hole is closed.
- **15b-session-types-neg.ep** — Negative test: double use of a linear
  channel is rejected.
- **15c-session-types-neg.ep** — Negative test: recv before send (wrong
  protocol order) is rejected.
- **15d-session-types-neg.ep** — Negative test: send on a closed channel
  is rejected.
- **16a-paxos-wrong-order-neg.ep** — Negative test for the Paxos protocol
  (Issues #101, #120): receiving the promise before sending prepare is
  rejected (`Chan propProto` vs `Chan (propAfterPrepare zero)`).
- **16b-paxos-wrong-value-neg.ep** — Negative test for the Paxos protocol
  (Issues #101, #120): forging a ticket for `suc X` when `AcceptMsg X` is
  demanded is rejected (`AcceptMsg (suc X)` vs `AcceptMsg X`).
- **17a-convex-neg.ep** — Negative test for the DCP-checked convex library
  (Issue #101): `minimize` of `x*x` with a bogus certificate is rejected
  (`Convex (eSq eVar)` vs `Convex (eMul eVar eVar)` — `eMul` admits no
  DCP rule, the classic CVXPY DCPError, here a compile-time error).
- **18a-vecdim-neg.ep** — Negative test for the dimension-indexed DCP
  library (Issue #110): `vDot` of a 1-vector with a 0-vector is rejected
  (`VExpr zero` vs `VExpr (suc zero)` — a compile-time shape error).
- **18b-vecdim-neg.ep** — Negative test (Issue #110): `quadForm` with a
  2x2 matrix but a 1-vector is rejected (square matrix must match the
  vector dimension).
- **18c-vecdim-neg.ep** — Negative test (Issue #110): non-DCP vector
  objective — `vMul` (elementwise product of variables) admits no
  certificate rule, so a bogus `vLogSum`-of-`vMul` proof is rejected
  (the vector analog of 17a's `x*x`).
- **21-borrow-ok.ep** — Positive test for QTT borrow checking (Issue
  #122): a well-bracketed unique borrow (read, bump, write, read) with
  every borrow binder used exactly once.
- **21a-borrow-double-use-neg.ep** — Negative test (Issue #122): a borrow
  used twice is rejected (`linear variable 'b2' used 2 times`).
- **21b-borrow-owner-use-neg.ep** — Negative test (Issue #122): the owner
  used while borrowed is rejected (`linear variable 'r' used 2 times`) —
  the borrow checker's exclusive-access rule.
- **21c-borrow-drop-neg.ep** — Negative test (Issue #122): a dropped
  borrow is rejected (`linear variable 'b' not used`).

## `embedded/` — Embedded Nim library use

These are ordinary Nim programs that embed dependently-typed code via
the `eponymBlock` macro. This is the *primary* use case: Eponym as a library
for verified components inside a larger Nim application.

- **sensor_fusion.nim** — Verified 3-element vector dot product for sensor
  fusion. The `eponymBlock` elaborates at compile time; the surrounding Nim
  handles IO and orchestration.
- **session_types.nim** — Session-typed channels as an embedded DSL
  (Issue #28): the protocol is stated once as indexed Eponym types, the
  client/server are ordinary-looking Nim, and protocol violations
  (wrong order, send on closed channel, double use, dropped channel)
  are compile-time errors.
- **paxos_session.nim** — Paxos prepare/promise/accept/accepted as dependent
  session types (Issues #101, #120): two roles, four messages each, with
  continuations that are functions of the communicated value (Issue #113).
  The value discipline is enforced by *unforgeable promise tickets*
  (`AcceptMsg` is postulated with no constructors, so the proposer can only
  accept the value the acceptor promised); the dependent session binds the
  received promise and indexes the continuation by it. The checked proposer
  and acceptor run in separate processes through bound loopback TCP adapters;
  the wire codec and promise/ticket mapping remain trusted. Wrong-order and
  wrong-value violations are compile-time errors (see 16a/16b negative
  tests above).
- **convex_opt.nim** — Disciplined convex programming as a compile-time
  check (Issue #101): the DCP rule table (curvature composition rules)
  as `Affine`/`Convex` proof families over a small expression language;
  `minimize` demands a `Convex` certificate in the objective position.
  The example proves `2*(x-3)^2 + x` convex by construction, then passes the
  same checked `prob()` expression to a Nim interpreter and ternary search.
  The search remains a trusted local optimizer, licensed by the compile-time
  convexity proof. Non-DCP objectives
  (`x*x`) are compile-time errors (see 17a above), where CVXPY would
  raise DCPError at solve() time.
- **convex_opt_vec.nim** — DCP with dimension-indexed vector variables
  (Issue #110): the case that actually requires dependent types. `VExpr n`
  tracks vector dimension in the type; `vDot` demands equal dimensions,
  `quadForm` demands a square `Mat n n` matching the vector, and
  `vMatVec` threads dimensions through linear maps. Headline demo is
  logistic regression (`vLogSum` of an affine residual — convexity via
  the softplus composition rule, non-obvious unlike least squares),
  plus a two-variable objective with different dimensions and a
  portfolio risk term (`quadForm` with a PSD side condition). The Nim
  driver interprets the exact checked logistic objective, including its
  concrete matrix and label vector, and derives a finite-difference gradient
  from it. Dimension
  mismatches and non-DCP vector products (`vMul`) are compile-time
  errors (see 18a/18b/18c above).
- **qtt_borrow.nim** — QTT borrow checking as an embedded DSL (Issue
  #122): a unique borrow of a buffer, scoped by `withBorrow` (bracket
  semantics — the linear resource is fully consumed, so it cannot leak).
  The borrow threads through `readB`/`writeB`/`endB` in
  continuation-passing style so every borrow is a lambda binder, and the
  quantity checker fires at every step; unannotated lambdas inherit the
  linear quantity from the expected `Pi` (Idris 2 behaviour). The
  checked `borrowClient` runs through bound Nim postulates against a real
  buffer. The raw-Value callback adapters invoke the checked continuations;
  the backend is responsible for excluding aliases and ending the borrow
  scope. Double-use, owner-use-while-borrowed, and dropped borrows are
  compile-time errors (see 21a/21b/21c above).

### The embedded pattern

```nim
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  data(Nat, Univ):
    proc zero(): Nat
    proc suc(n: Nat): Nat
  proc add(a: Nat, b: Nat): Nat = ...

# Ordinary Nim code; calls the verified `add` like any proc.
let x = add(2, 3)
```

The `eponymBlock` macro takes Nim AST (not a string), converts it to Eponym
surface syntax at compile time, elaborates it (type-checking), and
generates callable Nim wrappers. If elaboration fails, compilation stops
with the type error.

Nim-friendly syntax (vs `.ep` surface syntax):
- `postulate(Int, Univ)` — call syntax; `Univ` maps to `Type 0` (Nim cannot spell the universe token)
- `data(Nat, Univ):` — block with indented `proc` constructors
- `Vec(A, n)` — call syntax for type application
- `proc` / `=` — Nim keywords (Eponym `.ep` also uses these now)

## Running

```sh
export PATH=$HOME/.nimble/bin:$PATH
# Elaborator regression tests:
nim c -r --path:src tests/run_examples.nim
# Embedded examples (each is a standalone Nim program):
nim c -r --path:src --path:src/eponym --path:src/relational --path:src/staging examples/embedded/sensor_fusion.nim
nim c -r --path:src --path:src/eponym --path:src/relational --path:src/staging examples/embedded/session_types.nim
nim c -r --path:src --path:src/eponym --path:src/relational --path:src/staging examples/embedded/paxos_session.nim
nim c -r --path:src --path:src/eponym --path:src/relational --path:src/staging examples/embedded/qtt_borrow.nim
```
