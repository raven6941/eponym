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
Nullary, unindexed `data` declarations can map to Nim enums with the same
constructor names; constructor values are translated through their checked
runtime identities. Data constructors with arguments or indexed results do
not have an enum codec.
Type-level generic binders written `[A: Univ]` support generated Nim generic
wrappers when `A` appears only in the checked signature and the remaining
shape has codecs. Nim's concrete `A` values cross as opaque boxes; the runtime
does not inspect their representation. Value-indexed Nat binders written
`[n: Nat]` map to Nim `static[int]` parameters and cross as canonical checked
Nat constructors when the Nat prelude is available. These binders can appear
in signatures and checked runtime bodies; tests cover typed wrappers and both
typed and raw `runtimeValue` overloads. Bool binders `[b: Bool]` map to Nim
`static[bool]` and are encoded with the checked `true` and `false` constructors;
typed wrappers and both typed and raw `runtimeValue` overloads are covered.
Int binders `[i: Int]` map to Nim `static[int]` and cross as integer values;
typed wrappers and typed/raw `runtimeValue` overloads are covered, including
negative indices. A binder over an explicitly mapped runtime type uses
`static[NimType]` and crosses through that type's runtime codec; tests cover
opaque object and nullary enum values. The value must be representable as a
Nim compile-time constant. Dynamic wrappers also support generic value binders
whose domain is an indexed `Vec` with a registered `runtimeVector` codec: the
wrapper takes the corresponding Nim `seq` and checks its length while encoding.
Generic binders over non-dependent Sigma values are also supported when each
field has a runtime codec; nested Vec fields retain their length checks.
Dependent Sigma generic binders, other structural values without a registered
codec, and unmapped Eponym values remain unsupported by typed dynamic wrappers.
Dynamic generic Vec and non-dependent Sigma codecs can evaluate conditional Nat
indices of the form `if b: n else: m` when `b` is a Bool generic parameter and
both branches use supported Nat-index expressions. Compound Boolean conditions
remain unsupported in runtime type/index evaluation.
When a generic type appears in both a callback parameter and a later ordinary
value parameter, generated wrappers let Nim infer the type from the value,
including when a later `Vec[A, n]` argument maps to `seq[A]`. The callback's
concrete signature is still checked when the wrapper invokes or returns it,
so an incompatible callback fails compilation.
`Nat` conversions reject negative values. Explicit Nim `proc` declarations
with unsupported signatures remain checked but emit a targeted compile-time
error if called. Local clause-style definitions whose checked Pi signatures
can be reconstructed receive the same typed wrappers as explicit procedures;
unsupported signatures emit a compile-time diagnostic instead of an
integer-shaped fallback. When requested, `runtimeValue(name)` still exposes
the raw `Value` interface. Runtime application preserves the applied term so
clause eliminators substitute their arguments correctly. Definitions without
a supported runtime codec still need an explicit mapping or the raw `Value`
interface.

Nim default parameter values are preserved on generated typed wrappers and
typed `RuntimeValue` overloads, so callers can omit those arguments or
override them positionally or by name.

Inside `eponymBlock`, named term arguments are reordered for calls to known
local and imported declarations. Unknown names, duplicate arguments, and
omitted required arguments produce compile-time diagnostics. Calls through
arbitrary callable aliases still need signature metadata to support names.
Known local procedures also apply Nim defaults at checked call sites, including
when named arguments skip a preceding defaulted parameter.
Named calls through Nim callback parameters use the parameter names declared in
their `proc` type. Simple local `let` aliases of known procedures and callbacks
retain that signature metadata. More complex aliases, such as partial
applications and conditional callees, still need explicit callable metadata.

The low-level `Value` call path (`callValueFunc` / `callValueFuncDir`) now
supports primitive Int/Nat values, canonical Bool constructors, nullary
unindexed data constructors mapped to Nim enums, and opaque boxes for arbitrary
Nim payload types. Typed adapters support unary
`T -> T`, `T -> U`, `T -> Nat`,
`Nat -> A -> B`, and typed curried postulate contracts of arbitrary arity
when every argument and result type has a runtime codec.
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
argument count for definitions with a local Nim signature; callers must
construct those values correctly. `runtimeValue(importedDefinition)` also
works for definitions imported from `.ep` files without a local Nim signature
and exposes only the raw Value interface. Imported checked bodies can invoke
postulates bound by `bindPostulate` in the same block. The helper applies the
block's declared adapters; unbound postulates remain neutral. It does not
generate a structural Nim result type, but checks the imported definition's
fixed argument count from its checked lambda telescope. Callers still supply
well-formed Values. Callers
must handle unsupported constructors and neutral values explicitly. A
non-dependent `Sig(A, B)` runtime type is structurally mapped to a two-element
Nim tuple, recursively supporting `Int`, `Nat`, and explicitly mapped opaque
leaves. Named non-dependent `record` declarations map to Nim objects via
`runtimeType`, using the same recursive codecs in declaration order. Property
tests cover primitive and opaque tuple fields and mixed primitive and opaque
record fields. Dependent records can opt in with
`runtimeRecordTrusted(Record)` when every field has a codec. Earlier field
names are substituted into later field codecs; for example, a `Vec` field is
checked against its preceding Nat length field. Relationships not checked by
the selected field codecs remain trusted. Without the opt-in, dependent record
wrappers remain unsupported. A dependent `Sig` can also be exposed by a typed
wrapper when that definition opts in with `runtimePairTrusted(definition)`; its
field codecs are checked recursively, while correspondence between host field
values and their indices remains trusted. Without the opt-in, dependent `Sig` wrapper
signatures remain unsupported. The canonical length-indexed `Vec` family has
an explicit
`runtimeVector(Vec)` codec that maps `Vec[A, n]` to `seq[A]`. It checks the
host sequence length and the runtime Nat index at each `cons` cell; the
element type uses its recursive runtime codec, including nested vectors such
as `Vec[Vec[Int, m], n]` mapped to `seq[seq[int]]`. The codec accepts Nat length
expressions made from a static index, `zero`, `suc`, `add`, and `mul`. It
requires the standard `nil` and `cons` constructor shape from `lib/vec.ep`.
Generated runtime `Vec`, `List`, and `Option` values retain concrete element
type witnesses, including recursively nested built-in collection types. When an
element type is a type-level generic, generated wrappers can derive its
Eponym type witness from a unique `runtimeType` mapping for an unindexed Eponym
type and the concrete Nim type. Opaque host boxes retain that witness for
runtime type inference, so a `Vec[A, n]` can be checked with mapped Nim
elements. Generic types with no mapping, multiple Eponym mappings for the same
Nim type, or only an indexed-family mapping remain opaque and cannot support
full runtime type validation in that context. Raw `toHostValue` values also
remain untyped unless the caller supplies them through a mapped generated
codec.
The standard unindexed `List[A]` family also has a `runtimeList(List)` codec
that maps to `seq[A]`, checks constructor identities and spines, and recursively
uses the element codec. A unary family with canonical `none` and `some`
constructors can opt into `runtimeOption(Option)`, which maps recursively
codec-supported payloads to `std/options.Option[A]`. Other collections and
payload-bearing data types need an explicit codec when no built-in mapping is
available.
A mapped `Future[T]` can pass through an opaque postulate adapter as either an
argument or result; the bridge preserves the same Nim future value. Eponym
has no async effect, await, or cancellation operation. Completion, failure,
and cancellation remain Nim runtime behavior: Eponym does not observe or
transform them. The runtime bridge tests identity pass-through for a future
argument and the existing future-result case.
Nim closures can be passed into checked roles as opaque callback arguments,
where a bound Nim postulate may invoke them; Eponym does not inspect their
bodies. Nim proc types with supported leaf codecs also bridge to and from
Eponym function values. A multi-argument Nim proc is represented as a curried
chain of Eponym functions; arguments and results use the same recursive codecs
as generated wrappers. A 200-case property covers multi-argument callbacks
with primitive and mapped opaque values in both directions. Returned callback
types must use Nim's `{.closure.}` calling convention. Callback effects and
behavior remain trusted host semantics.
Dynamic generic wrappers accept unmapped named Eponym value binders as `Value`
parameters and validate that each value inhabits its declared named type
before checked evaluation. `nameRuntimeValueDynamic` returns the checked
result and globals without requiring a result codec. The generated signatures
use the public `RuntimeValue`, `RuntimeGlobals`, and `RuntimeValueResult`
aliases from `eponym_embed`, so callers need not import internal runtime types.
Applied family domains are checked when their type expressions use named
references, earlier
generic indices, applications, and integer literals. More complex type
expressions remain unsupported. A 200-case `SizedTree[length]` property checks
raw `Value` and mapped `RuntimeVariant` arguments and rejects an embedded
length that differs from the generic index. Direct Bool-controlled conditional
Nat indices are also supported in applied generic domains; a 200-case
`SizedTree[if b: n else: m]` property covers both branches and rejects values
whose embedded index does not match the selected branch.

The low-level `RuntimeVariant` API provides a checked structural view for any
declared data family when the caller supplies its constructor names. It
preserves constructor identity and raw argument `Value`s, checking family
membership, constructor arity, and spine shape. This handles payload-bearing
and indexed constructors without a custom constructor switch. Use
`runtimeVariant(Family)` to have generated wrappers select this representation
automatically. Callers still decode payload fields themselves because the
generic representation stores them as raw `Value`s.

Typed structural codecs are currently limited to `Vec`, `List`, `Option`, two-field
`Sig` tuples, and named records. Records with dependent fields
and dependent `Sig` results are available only through their explicit trusted
opt-ins described above. Other payload-bearing data constructors have no
built-in typed field codec and require an explicit `runtimeCodec` mapping or
manual decoding through `RuntimeVariant`.
Non-Nat value-indexed generic signatures without a supported runtime mapping
and structural inspection of closures are unsupported.
The session runtime demo includes a hand-written Nat LEB128 message codec, and
the TCP adapter demo uses it over a loopback socket, but there is no general
derived structural codec framework. A user can provide a codec for a named
Eponym type or family with `runtimeCodec(Type, NimType, encode, decode)`.
Encoder and decoder procedures receive `Globals` and translate between the
Nim representation and runtime `Value`s. The Nim compiler checks their
concrete signatures when a wrapper or typed postulate binding uses them; the
codec implementation and any dependent-index correspondence remain trusted.
Nim's type checker checks the concrete adapter signature, but the mapping to
the Eponym type and the adapter behavior remain trusted. Neither compiler
proves that the host value satisfies a dependent index.

Distinct Eponym names may share one Nim representation, for example
`RequestId` and `Sample` both mapped to `int`. Checked Eponym identities stay
distinct at the bridge boundary, but a Nim adapter signature sees only `int`
and cannot prevent adapter code from confusing their semantic roles. Use
distinct Nim newtypes when Nim should enforce that distinction.

This is an ABI/runtime limitation, not an elaborator restriction. The
`eponymBlock` macro supports `bindPostulate` for unary `Int -> Int`, unary
opaque `T -> T`, opaque `T -> U`, `T -> Nat`, `Nat -> A -> B`, and curried
opaque postulates with typed runtime codecs for every argument and result.
`bindPostulatePair` additionally binds one to three codec-supported named
arguments to a non-dependent `Sig(B, C)` result using recursive tuple codecs.
It checks the declared argument type heads and tuple field type heads; indices
on mapped type families remain trusted. `bindPostulatePair` rejects dependent
Sigma results. `bindPostulatePairTrusted` permits them when the declared fields
have codecs, but the host adapter must uphold the relationship between a field
and its index. A generated wrapper can expose a dependent Sigma result as a
Nim tuple when that checked definition is explicitly marked
`runtimePairTrusted(definition)`. The recursive codecs check each field's Nim
representation, while the relationship between the field values and dependent
indices remains trusted. Without this marker, generated wrappers continue to
reject dependent Sigma signatures.
Opaque bindings require explicit `runtimeType(EponymType, NimType)` mappings
to postulated Eponym types or
type families. Nim checks adapter and generated wrapper signatures;
the implementation and mapping remain trusted. Synchronous exceptions from a
Nim adapter propagate unchanged to the caller. An invoked but unbound
postulate raises a `ValueError` naming the postulate. `eponymBlock` rejects a
binding that no checked proc body references, but does not determine whether
that proc is reachable from an application entry point. Call-graph
reachability and structural codecs remain unsupported. The TCP demo returns
transport and codec failures through a mapped `TransportResult` value. Other
adapters may still propagate synchronous exceptions. See the
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
`cons[A, n](x, xs)`; recognized legacy call-style explicit applications now fail with a migration
diagnostic, including local Nat `let` aliases and conditional Nat expressions.
Direct callback parameters with explicit Pi type binders also receive this
check. Returned-function aliases, callback aliases, and other function-valued
paths still need a complete audit. Generic Eponym definitions can be checked,
but the generated Nim runtime wrapper for a generic definition is not
implemented yet.

Pure `if`/`elif`/`else` expressions lower to nested checked `ifThenElse`
calls when `lib/bool.ep` is imported. Each condition must have type `Bool`,
and each branch must be one Eponym expression. The branches are delayed with
unit lambdas and only the selected branch is evaluated, matching Nim's
conditional evaluation even when a branch calls a bound postulate. This does
not enable ordinary effectful Nim control flow inside the block. The Nim
integer literal `1` is emitted using Eponym's unambiguous `01` spelling, so
expected-type checking can select `Int` or `Nat`.
