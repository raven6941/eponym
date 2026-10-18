# Known limitations

This page records current limits that affect how Eponym can be used. It is
not a statement that each item is a soundness bug; some are missing runtime
or user-facing features. The links below point to the implementation or the
design notes where the limit comes from.

## Embedding and runtime

### What each layer establishes

| Example or boundary | Checked by Eponym | Checked by Nim | Trusted or separate |
|---|---|---|---|
| `session_runtime_bindings.nim`, `session_tcp_bindings.nim` | The sender/receiver role and its session-indexed postulate calls | Generated wrapper and adapter signatures | Adapter behavior, message codec, and TCP transport |
| `paxos_session.nim` | Proposer/acceptor roles, dependent promise ticket use, and indexed channel transitions | Generated wrapper and Nim TCP adapter signatures | Wire codec, TCP behavior, and host promise/ticket correspondence |
| `qtt_borrow.nim` | `borrowClient` and its linear continuation use | Generated `Buffer -> int` wrapper; Nim raw-Value adapters type-check | The adapter's decoding, exclusive access, alias discipline, and lifetime |
| `convex_opt.nim` | The reified objective and DCP certificate | Nim interpreter and ternary search consume the runtime value of checked `prob()` | Integer interpreter and search are trusted |
| `convex_opt_vec.nim` | The data-indexed logistic objective and DCP certificate | Nim interprets the checked expression and derives a finite-difference gradient | Raw Value argument construction, expression interpreter, floating point, and optimizer are trusted |
| `bindPostulate` runtime bridge | Checked callers match the Eponym postulate type | Generated wrapper and Nim adapter signatures match declared mappings | Adapter implementation and opaque mappings uphold the postulate semantics |

“Checked” in this table means the Eponym layer elaborates the definition and
the kernel accepts its proof obligations. It does not imply that a separate
Nim driver calls that definition or that the host implementation satisfies
the postulated behavior.

### Callable definitions have a partial runtime bridge

`eponymBlock` checks definitions at Nim compile time, then generates Nim
wrappers for them. Top-level definitions whose parameters and
result use primitive `Int` or `Nat` get fixed-arity Nim `proc` wrappers with
`int` parameters and results. Definitions over `Bool` get Nim `bool` wrappers
when `bool.ep` is imported; the codec uses the checked `true` and `false`
constructors and rejects noncanonical Bool runtime values. Explicit
`runtimeType` mappings add opaque postulated types and indexed families.
Type-level generic binders written `[A: Univ]` also support generated Nim
generic wrappers when `A` appears only in the checked signature and the
remaining shape has codecs. Nim's concrete `A` values cross as opaque boxes;
the runtime does not inspect their representation. Value-indexed binders and
generic type parameters used by the runtime body still need explicit runtime
representations.
`Nat` conversions reject negative values. An explicit `proc` declaration with
an unsupported signature remains
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
supports primitive Int/Nat values, canonical Bool constructors, and opaque
boxes for arbitrary Nim payload types. Typed adapters support unary
`T -> T`, `T -> U`, `T -> Nat`,
`Nat -> A -> B`, and opaque postulate contracts with up to four curried
arguments.
They can pass Nim objects, references, strings, or other values through
explicitly mapped Eponym types without exposing their representation.
`eponymBlock` can generate typed wrappers for first-order definitions over
mapped opaque types that correspond to named Eponym postulates. Tests exercise
user-defined values through checked definitions and generated wrappers. A
`runtimeValue(name)` request inside `eponymBlock` exposes a checked definition
as its runtime `Value` together with the checked globals,
for host-side interpreters of reified data. Zero-argument definitions get a
no-argument helper. When every parameter has a runtime codec, parameterized
definitions also get a Nim-typed overload that converts arguments and returns
the result as a `Value`. Mapped host values are not checked against dependent
indices. A raw `openArray[Value]` overload remains available and checks only
argument count; callers must construct those values correctly. The helper
applies the block's declared `bindPostulate` adapters; unbound postulates
remain neutral. It does not generate a structural Nim result type, so callers
must handle unsupported constructors and neutral values explicitly. A
non-dependent `Sig(A, B)` runtime type is structurally mapped to a two-element
Nim tuple, recursively supporting `Int`, `Nat`, and explicitly mapped opaque
leaves. Named non-dependent `record` declarations map to Nim objects via
`runtimeType`, using the same recursive codecs in declaration order. Property
tests cover primitive and opaque tuple fields and mixed primitive and opaque
record fields. Dependent `Sig` types and records with dependent fields remain
unsupported. A
mapped `Future[T]` can pass through an opaque postulate adapter as either an
argument or result; the bridge preserves the same Nim future value. Eponym
has no async effect, await, or cancellation operation. Completion, failure,
and cancellation remain Nim runtime behavior: Eponym does not observe or
transform them. The runtime bridge tests identity pass-through for a future
argument and the existing future-result case.
Nim closures can be passed into checked roles as opaque callback arguments,
where a bound Nim postulate may invoke them; Eponym does not inspect their
bodies. Returning closures from generated wrappers remains unsupported.
Structural codecs for collections beyond non-dependent two-field `Sig` tuples
and named non-dependent records, dependent signatures, value-indexed generic
signatures, and generic binders used in runtime bodies,
callback shapes with more than four curried opaque arguments, and structural
inspection of closures remain unsupported. The session runtime demo includes a
hand-written Nat LEB128 message codec, and the TCP adapter demo uses it over a
loopback socket, but there is no reusable structural codec framework.
Nim's type checker checks the concrete adapter signature, but the mapping to
the Eponym type and the adapter behavior remain trusted. Neither compiler
proves that the host value satisfies a dependent index.

This is an ABI/runtime limitation, not an elaborator restriction. The
`eponymBlock` macro supports `bindPostulate` for unary `Int -> Int`, unary
opaque `T -> T`, opaque `T -> U`, `T -> Nat`, `Nat -> A -> B`, and curried
opaque postulates with up to four arguments.
`bindPostulatePair` additionally binds one to three codec-supported named
arguments to a non-dependent `Sig(B, C)` result using recursive tuple codecs.
It checks the declared argument type heads and tuple field type heads; indices
on mapped type families remain trusted. `bindPostulatePair` rejects dependent
Sigma results. `bindPostulatePairTrusted` permits them when the declared fields
have codecs, but the host adapter must uphold the relationship between a field
and its index.
Opaque bindings require explicit `runtimeType(EponymType, NimType)` mappings
to postulated Eponym types or
type families. Nim checks adapter and generated wrapper signatures;
the implementation and mapping remain trusted. Synchronous exceptions from a
Nim adapter propagate unchanged to the caller. An invoked but unbound
postulate raises a `ValueError` naming the postulate. `eponymBlock` rejects a
binding that no checked proc body references, but does not determine whether
that proc is reachable from an application entry point. Call-graph
reachability, callbacks with more than four opaque arguments, and structural
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

### The borrow example uses a trusted raw-Value callback adapter

`session_runtime_bindings.nim` and `session_tcp_bindings.nim` run checked
sender/receiver roles through typed Nim adapters. `paxos_session.nim` runs its
checked proposer and acceptor in separate processes through a loopback TCP
adapter; `runPaxosRound` starts the acceptor and invokes the checked proposer
rather than repeating their message sequence. `qtt_borrow.nim` now runs the
checked `borrowClient` through bound postulates. Its host adapter receives raw
Eponym `Value`s so it can invoke the Eponym continuations in CPS order.

The `bindPostulateValue` form is an explicit low-level escape hatch. Eponym
checks the postulated operation types at call sites and the adapter arity;
Nim checks only the adapter's `seq[Value] -> Value` signature. The adapter
must uphold the full value contract. For borrowing, Nim enforces a scoped
active flag and releases it in `finally`, while arbitrary aliases held by
other Nim code remain outside Eponym's guarantee. TCP transports and all
adapter behavior remain trusted as well.

### Some examples certify a model, not the runtime computation

Both convex examples now feed their checked objective to a Nim interpreter.
`convex_opt.nim` interprets the value of `prob()`; `convex_opt_vec.nim`
interprets `lrProb(m, n, A, b)`, including its concrete host matrix and label
vector. Gradient descent estimates derivatives from that interpreted
objective instead of maintaining a second gradient formula. Properties
compare 200 randomized vector objectives and gradients against a separate
numeric oracle, and verify a checked objective mutation changes the result.
The interpreters support only the constructors used by these examples and
fail on unknown constructors. Raw `Value` arguments, arithmetic precision,
finite-difference error, and optimizer behavior remain trusted host code.

### Linear checks apply to modeled Eponym values

The borrow example checks use of explicitly modeled Eponym variables and
postulated operations. It does not inspect Nim references, discover aliases,
or enforce Rust-like ownership on surrounding Nim code. Its separate Nim
buffer driver is hand-written to mirror the checked sequence.

## First-use setup

Relative prelude imports now fall back to the installed package's `lib/`
directory after checking beside the importing Nim source. Project-local
preludes can override the package copy, and absolute paths select a specific
file. Clean-install resolution is covered by a separate-project test. See
[installation](../README.md#installation).

## Surface syntax

The embedded syntax is Nim-shaped but is not ordinary Nim semantics. Explicit
Eponym parameters can use Nim square brackets, as in `Vec[A, n]` and
`cons[A, n](x, xs)`; legacy call-style forms remain accepted. Generic Eponym
definitions can be checked, but the generated Nim runtime wrapper for a
generic definition is not implemented yet.

Pure `if`/`elif`/`else` expressions lower to nested checked `ifThenElse`
calls when `lib/bool.ep` is imported. Each condition must have type `Bool`,
and each branch must be one Eponym expression. This does not enable ordinary
effectful Nim control flow inside the block.
