# Known limitations

This page records current limits that affect how Eponym can be used. It is
not a statement that each item is a soundness bug; some are missing runtime
or user-facing features. The links below point to the implementation or the
design notes where the limit comes from.

## Embedding and runtime

### Callable definitions have a partial runtime bridge

`eponymBlock` checks definitions at Nim compile time, then generates Nim
wrappers for them. Top-level non-generic definitions whose parameters and
result use primitive `Int` or `Nat` get fixed-arity Nim `proc` wrappers with
`int` parameters and results. Explicit `runtimeType` mappings add opaque
postulated types and indexed families. `Nat` conversions reject negative
values. An explicit `proc` declaration with an unsupported signature remains
checked but emits a targeted compile-time error if called. Generated names
without a matching `proc` declaration retain the compatibility
`varargs[int] -> int` wrapper in
[`eponym_mac.nim`](../src/eponym/eponym_mac.nim). At runtime,
[`eponym_embed.nim`](../src/eponym/eponym_embed.nim) converts Nim integers to
Eponym's primitive `Int`, applies the checked term, and converts an `Int`
result back. This means the checker can accept definitions over `Nat`,
vectors, records, session types, and other Eponym types, but those definitions
do not thereby become callable from ordinary Nim with a faithful typed
signature.

The low-level `Value` call path (`callValueFunc` / `callValueFuncDir`) now
supports primitive Int/Nat values and opaque boxes for arbitrary Nim payload
types. Typed adapters support unary `T -> T`, `T -> U`, `T -> Nat`,
`Nat -> A -> B`, binary `A -> B -> C`, and ternary `A -> B -> C -> D`
postulate contracts.
They can pass Nim objects, references, strings, or other values through
explicitly mapped Eponym types without exposing their representation.
`eponymBlock` can generate typed wrappers for first-order definitions over
mapped opaque types that correspond to named Eponym postulates. Tests exercise
user-defined values through checked definitions and generated wrappers. A
mapped `Future[T]` can pass through as an opaque postulate result, but Eponym
does not await it or define async failure and cancellation semantics.
Nim closures can be passed into checked roles as opaque callback arguments,
where a bound Nim postulate may invoke them; Eponym does not inspect their
bodies. Returning closures from generated wrappers remains unsupported.
Structural codecs for records or collections, dependent or generic signatures,
callback shapes with more than three curried opaque arguments, and structural
inspection of closures remain unsupported. The session runtime demo includes a
hand-written Nat LEB128 message codec, and the TCP adapter demo uses it over a
loopback socket, but there is no reusable structural codec framework.
Nim's type checker checks the concrete adapter signature, but the mapping to
the Eponym type and the adapter behavior remain trusted. Neither compiler
proves that the host value satisfies a dependent index.

This is an ABI/runtime limitation, not an elaborator restriction. The
`eponymBlock` macro supports `bindPostulate` for unary `Int -> Int`, unary
opaque `T -> T`, opaque `T -> U`, `T -> Nat`, `Nat -> A -> B`,
curried binary opaque `A -> B -> C`, and curried ternary opaque
`A -> B -> C -> D` postulates.
Opaque bindings require explicit `runtimeType(EponymType, NimType)` mappings
to postulated Eponym types or
type families. Nim checks adapter and generated wrapper signatures;
the implementation and mapping remain trusted. Synchronous exceptions from a
Nim adapter propagate unchanged to the caller. An invoked but unbound
postulate raises a `ValueError` naming the postulate. `eponymBlock` rejects a
binding that no checked proc body references, but does not determine whether
that proc is reachable from an application entry point. Call-graph
reachability, callbacks longer than three opaque arguments, and structural
codecs remain unsupported. The TCP demo returns transport and codec failures
through a mapped `TransportResult` value. Other adapters may still propagate
synchronous exceptions. See the
[postulate binding experiment](postulate-nim-binding-experiment.md) for the
supported prototype and remaining work.

### Nim code is not evaluated inside checked blocks

Nim-shaped syntax inside `eponymBlock` denotes Eponym syntax. The macro
translates supported AST forms to Eponym source; it does not execute
arbitrary Nim procedures, library calls, IO, mutation, or control flow inside
the checked definition. Ordinary Nim code remains available around the
block. See the [Nim boundary](surface-syntax-reference.md#the-nim-boundary)
and the [pure subset experiment](pure-nim-subset-experiment.md).

## Checking and code generation

### QTT quantities are checked, not used for mutable code generation

Linear and erased quantities constrain usage during elaboration and
typechecking. The current runtime bridge does not use linearity to generate
in-place mutation, destination-passing code, or other ownership-based
optimizations.

### Host implementations remain trusted

When a postulate is eventually connected to a Nim implementation, Eponym can
check callers against the postulated type and Nim can check the adapter's
Nim signature. Neither check proves that arbitrary Nim code obeys a dependent
protocol, preserves a linear resource, or returns a value satisfying a
dependent index. Such implementations remain part of the trust boundary.
See the [trust model](trust-model.md).

### Nim ownership and lifetime at the runtime boundary

The current adapters take and return Nim values by value. `toHostValue[T]`
stores a Nim value in a rooted box for the runtime call. Ordinary object
values follow Nim's copy and destructor rules; `ref` values, pointers, and
closures still refer to their existing storage or captured environment, so
boxing them does not remove aliases. The host adapter may retain or duplicate
those references, and raw pointer validity remains the adapter author's
responsibility. There is no adapter form that accepts `var`/`lent` parameters
or transfers ownership explicitly.

Eponym enforces a linear channel's use in checked Eponym terms. It does not
make a Nim `ref` or closure single-use, detect aliases held elsewhere, or
prevent the adapter from retaining a handle. Generated wrappers create a
call-local binding environment; synchronous adapter exceptions propagate
unchanged. A mapped `Future[T]` is returned as an opaque Nim value and remains
owned by the caller and Nim's normal lifetime rules; Eponym does not await or
cancel it.

### Some checked roles still have separate Nim drivers

`session_runtime_bindings.nim` and `session_tcp_bindings.nim` run checked
sender/receiver roles through typed Nim adapters; the latter uses a loopback
TCP socket. The larger `paxos_session.nim` still checks `proposer` and
`acceptor`, while `runPaxosRound` manually repeats the message sequence using
mailboxes and assertions. `qtt_borrow.nim` checks a linear borrow API, while
its buffer driver mirrors the operations separately.

The integrated session examples establish that the checked roles execute
through their bound postulates, but the adapter and transport remain trusted.
The Eponym checker does not establish network ordering or inspect aliases in
ordinary Nim. Paxos and buffer execution still require manual synchronization
with their checked Eponym descriptions.

### Some examples certify a model, not the runtime computation

The convex optimization demos check a reified objective and a certificate
against DCP-style constructors at compile time. The Nim optimizer does not
consume that checked Eponym value: `convex_opt.nim` separately implements
the formula as `f`, while `convex_opt_vec.nim` separately implements the
loss and gradient over Nim `seq[float]`. The examples illustrate how a
dependent certificate can validate a model, but they do not yet connect that
certificate to or generate the optimizer's runtime calculation. Keeping
those two representations synchronized is currently the user's
responsibility; the checker does not establish that the numerical driver
implements the certified symbolic expression.

### Linear checks apply to modeled Eponym values

The borrow example checks use of explicitly modeled Eponym variables and
postulated operations. It does not inspect Nim references, discover aliases,
or enforce Rust-like ownership on surrounding Nim code. Its separate Nim
buffer driver is hand-written to mirror the checked sequence.

## First-use setup

The tutorial's short completion estimate covers the Eponym concepts, but a
new project currently has to vendor the `.ep` prelude files beside the Nim
source. A released nimble package does not yet make those Eponym imports
resolve automatically from the installed package. See
[installation](../README.md#installation).

## Surface syntax

The embedded syntax is Nim-shaped but is not ordinary Nim semantics. For
example, explicit Eponym parameters currently use call-style forms such as
`Vec(A, n)` and `cons(A, n, x, xs)`, rather than Nim's generic bracket
convention. A proposal to investigate brackets for explicit Eponym binders
is tracked separately; this page should be updated when a concrete syntax
decision is made.
