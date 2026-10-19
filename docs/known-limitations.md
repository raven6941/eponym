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
opaque object and nullary enum values. These wrappers require a Nim
compile-time constant. A sibling `nameDynamic` wrapper is generated for
value-indexed Nat, Bool, Int, and explicitly mapped binders; it takes those
generic values as ordinary Nim parameters. Property tests cover dynamic Int,
Bool, mapped object, and Nat-indexed Vec values. Binder types without a runtime
mapping remain available through `nameRuntimeValueRaw` for callers that
construct the Eponym generic argument as a `Value` themselves. When
`runtimeValue(name)` is requested, supported dynamic generic binders also get a
`nameRuntimeValueDynamic` sibling. It accepts those binders as ordinary Nim
values and returns `(Value, Globals)` without requiring a codec for the result.
`Nat` conversions reject negative values. An explicit `proc` declaration with
an unsupported signature remains
checked but emits a targeted compile-time error if called. Local clause-style
definitions whose checked Pi signatures can be reconstructed also get typed
wrappers. If reconstruction fails, calling the generated name produces a
compile-time diagnostic; a requested `runtimeValue(name)` still exposes the
raw `Value` interface. Runtime applications retain their applied syntax so
clause eliminators can substitute arguments correctly. At runtime,
[`eponym_embed.nim`](../src/eponym/eponym_embed.nim) converts Nim integers to
Eponym's primitive `Int`, applies the checked term, and converts an `Int`
result back. Definitions with unsupported codecs still need a mapped runtime
representation or the raw `Value` interface.

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
simple named `runtimeType(Postulate, NimType)` mapping carries an Eponym type
witness with opaque runtime boxes. A typed wrapper rejects a returned box that
lacks the witness or carries a different Eponym type, in addition to checking
its Nim box type. Property tests reject both a missing witness and a witness
for a different mapped Eponym type. This does not prove that the Nim payload
semantically represents that Eponym value: the mapping and host implementation
remain trusted. Mapped values are checked against the represented Eponym type,
including family indices the runtime can represent, before decoding or after
encoding.
`runtimeValue(name)` request inside `eponymBlock` exposes a checked definition
as its runtime `Value` together with the checked globals,
for host-side interpreters of reified data. Zero-argument definitions get a
no-argument helper. When every parameter has a runtime codec, parameterized
definitions also get a Nim-typed overload that converts arguments and returns
the result as a `Value`. Its typed arguments pass through the same recursive
codecs as generated wrappers, so represented dependent indices are checked.
A raw `openArray[Value]` overload remains available; it validates supported
argument types recursively, including dependent structures and callback
arguments/results when their runtime shape is supported. Unsupported type
expressions and the semantic correspondence between opaque host payloads and
their Eponym types remain trusted.
Structural `Vec`, `List`, and `Option` values are checked in one traversal for
shape, represented indices, and element types. Nested vectors and recursive
payload-bearing data variants are checked through their constructor
telescopes, including fields nested in those structures. Named records and
Sigma pairs are checked field by field, substituting earlier values into later
field types. Mapped opaque host boxes are checked against their declared Nim
box type. Typed mappings and recursive structural codecs also carry and check
an Eponym type witness when the type expression, including its indices, has a
runtime term representation. The semantic correspondence between the Nim
payload and its Eponym type remains trusted. Raw host boxes and indices whose
values cannot be represented as Eponym terms remain trusted. Erased type-level
element witnesses cannot be recovered from a raw runtime value; unsupported
type expressions still require caller-side validation. For data variants, each
constructor's instantiated result type is compared with the expected indexed
type. Generic local definitions also get
`nameRuntimeValueRaw(genericArgs, valueArgs)`, which accepts all generic
arguments and ordinary arguments as `openArray[Value]`. It checks generic
values against supported binder type expressions, including applied domains
that refer to earlier generic arguments. Ordinary raw values containing
unsupported type expressions still need caller-side validation. Mapped
opaque boxes are checked against their Nim box type; their Eponym semantics
remain trusted.
`runtimeValue(importedDefinition)` also works for definitions imported
from `.ep` files without a local Nim signature. When the checked Pi signature
has runtime codecs, the macro derives a typed Nim wrapper and typed
`RuntimeValue` overload from the checked globals; otherwise it exposes only the
raw Value interface. When its Pi signature can be reconstructed, the raw
interface also validates arguments against that signature, including
dependent Vec lengths. Generic imported signatures with explicit type binders
are checked by instantiating the checked Pi telescope at runtime. Explicit
and implicit `Type 0` binders also generate Nim generic wrappers, with the
type inferred from ordinary value arguments. Their raw `Value` entry point is
named `nameRuntimeValueRaw` to avoid ambiguity with Nim's inferred generic
overload. Supported implicit Nat, Bool, Int, and explicitly mapped binders
generate static and dynamic wrappers. Properties cover length-indexed vectors
and scalar values through typed, dynamic, `RuntimeValue`, and raw `Value`
paths. Higher-order signatures with supported Nim callback leaf codecs generate
typed closure wrappers.
Unsupported implicit binder domains and callback signatures
without codecs retain the raw interface. Raw-Value callback arguments and
results are checked against their Eponym function type when the runtime shape
is supported, including recursive data and dependent Vec indices; unsupported
type expressions remain trusted. Unmapped host boxes remain a trusted escape
hatch. Imported checked bodies can
invoke postulates bound by `bindPostulate` in the same block. Tests cover
typed and raw imported identity calls, a typed call through a bound imported
postulate, and an imported length-indexed Vec wrapper that rejects the wrong
length through both typed and raw interfaces. Imported callback wrappers also
preserve dependent Vec result lengths derived from a callback's Nat argument;
wrong-length callback results are rejected. Imported definitions can also
return callable Nim closures when callback leaf types have codecs; a property
covers typed wrappers and raw `RuntimeValue` closures. Callers must handle unsupported
constructors and neutral values explicitly. A
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
values and their indices remains trusted. The opt-in works for local
definitions and imported definitions whose signatures can be reconstructed;
an imported dependent-pair identity is property-tested through typed and
`RuntimeValue` wrappers, including rejection of a mismatched Vec length.
Without the opt-in, dependent `Sig` wrapper signatures remain unsupported.
The canonical length-indexed `Vec` family has
an explicit
`runtimeVector(Vec)` codec that maps `Vec[A, n]` to `seq[A]`. It checks the
host sequence length and the runtime Nat index at each `cons` cell; the
element type uses its recursive runtime codec, including nested vectors such
as `Vec[Vec[Int, m], n]` mapped to `seq[seq[int]]`. The codec accepts Nat length
expressions made from a static index, `zero`, `suc`, `add`, and `mul`. It
requires the standard `nil` and `cons` constructor shape from `lib/vec.ep`.
The standard unindexed `List[A]` family also has a `runtimeList(List)` codec
that maps to `seq[A]`, checks constructor identities and spines, and recursively
uses the element codec. A unary family with canonical `none` and `some`
constructors can opt into `runtimeOption(Option)`, which maps recursively
codec-supported payloads to `std/options.Option[A]`. Custom `runtimeCodec`
leaves are property-tested through all three codecs, including generated
wrappers and typed and raw `RuntimeValue` calls. Other collections and
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
Eponym function values. Named noncapturing Nim procedures with the default
`nimcall` convention can be passed where a generated wrapper expects a
closure proc type; Nim converts the procedure value. A 200-case embedded
property checks this through the runtime bridge. A multi-argument Nim proc is represented as a curried
chain of Eponym functions; arguments and results use the same recursive codecs
as generated wrappers. A 200-case property covers multi-argument callbacks
with primitive and mapped opaque values in both directions. Add `{.rawValue.}`
alongside `{.closure.}` on a proc type to expose its arguments and result as
raw `Value`s instead. This supports callback signatures whose Eponym leaf types
have no Nim codec; the callback implementation is responsible for interpreting
those Values. A 200-case property covers an unmapped `Token -> Token` callback
through a generated wrapper and a reified runtime callback. Codec-backed
callback results can depend on an earlier callback argument: a Nim
`proc(length: int): seq[int]` can implement Eponym's
`Nat -> Vec[Int, length]` when the Eponym proc type names that binder. The
bridge carries the runtime argument into the recursive result codec, which
checks the vector length. Earlier callback arguments also flow into later
argument codecs, so `Nat -> Vec[Int, length] -> Nat` validates both input and
output. 200-case properties cover these paths through generated and reified
wrappers, and negative checks reject mismatched Vec lengths. Returned callback
types must use Nim's `{.closure.}` calling convention. Callback effects and
behavior remain trusted host semantics.
Dynamic generic wrappers accept unmapped value-indexed binders as `Value`
parameters; `nameRuntimeValueDynamic` returns the checked result and globals.
This lets a caller pass an existing Eponym value, including a payload-bearing
constructor, through an index and retrieve it from the checked body. The bridge
checks membership when the binder domain is a named Eponym type. A property
test exercises a payload-bearing token and rejects an Int supplied at the
Token index. Applied family domains are also checked by evaluating supported
type expressions built from named references, applications, earlier generic
indices, and integer literals. A 200-case `SizedTree[length]` property checks
both raw `Value` and mapped `RuntimeStructuredVariant` arguments, and rejects an
embedded index that differs from `length`. More complex binder type
expressions remain unsupported. Results remain raw `Value`s when no host
representation is mapped.

The low-level `RuntimeVariant` API provides a checked structural view for any
declared data family when the caller supplies its constructor names. It
preserves constructor identity and raw argument `Value`s, checking family
membership, constructor arity, and spine shape. This handles payload-bearing
and indexed constructors without a custom constructor switch. Use
`runtimeVariant(Family)` to have generated wrappers select this representation
automatically. Callers still decode payload fields themselves because the
generic representation stores them as raw `Value`s.

For recursive decoding, `runtimeDataVariant(Family)` maps Int, Nat, and Bool
payloads to Nim values, nested data constructors to
`RuntimeStructuredVariant`, and opaque leaves through matching `runtimeType`
or `runtimeCodec` mappings. It follows each constructor's checked Pi type and
validates structural payload fields, including dependent indices. Opaque host
codecs now carry a runtime Eponym type witness when the field type can be
represented; decoding checks named types and applied indices against the
constructor telescope. The mapping still trusts that the Nim payload
semantically represents the indexed value. Properties cover opaque
`ChannelHandle` fields beside an integer and reject both a different named
witness and a mismatched index on an opaque family field. Custom codec values
are checked against the field's Eponym type on both encode and decode;
wrong-type custom encodings and malformed decoded fields are rejected.

Typed structural codecs include `Vec`, `List`, `Option`, two-field `Sig`
tuples, named records, and recursive `runtimeDataVariant` values. Records with
dependent fields and dependent `Sig` results are available only through their
explicit trusted opt-ins described above.
More complex generic domain expressions outside the supported type-expression
forms and structural inspection of closures are unsupported.
The session runtime demo includes a hand-written Nat LEB128 message codec, and
the TCP adapter demo uses it over a loopback socket. The structural codecs
cover common recursive shapes; a user can provide a codec for a named
Eponym type or family with `runtimeCodec(Type, NimType, encode, decode)`.
Encoder and decoder procedures receive `Globals` and translate between the
Nim representation and runtime `Value`s. The Nim compiler checks their
concrete signatures when a wrapper or typed postulate binding uses them.
Generated wrappers also validate custom encoded and decoded Values against the
checked Eponym type when its runtime shape is checkable, including supported
dependent indices. The codec's semantic relationship between the Nim payload
and Eponym value remains trusted, as do indices the runtime shape cannot
represent. Nim's type checker checks the concrete adapter signature but does
not prove that host code obeys the Eponym contract.

This is an ABI/runtime limitation, not an elaborator restriction. The
`eponymBlock` macro supports `bindPostulate` for unary `Int -> Int`, unary
opaque `T -> T`, opaque `T -> U`, `T -> Nat`, `Nat -> A -> B`, and curried
opaque postulates with typed runtime codecs for every argument and result.
`bindPostulatePair` additionally binds one to three codec-supported named
arguments to a non-dependent `Sig(B, C)` result using recursive tuple codecs.
It checks the declared argument type heads and tuple field type heads; indices
on mapped type families remain trusted. `bindPostulatePair` rejects dependent
Sigma results. `bindPostulatePairTrusted` permits them when the declared fields
have codecs. For a postulate declared in the same `eponymBlock`, the macro
retains its full result Sigma type, allowing recursive codecs to check
represented constraints such as a Vec length against the first field. The
host adapter must still uphold index relationships those codecs cannot
represent. Imported postulates use their checked `Globals` type to recover
the same result shape. A generated wrapper can expose a dependent Sigma result as a
Nim tuple when that checked definition is explicitly marked
`runtimePairTrusted(definition)`. The recursive codecs check each field's Nim
representation, while the relationship between the field values and dependent
indices remains trusted. Nested dependent Sigma values propagate named
indices through recursive codecs; supported field codecs such as `Vec` still
check their represented constraints (for example, sequence length against the
bound Nat). A trusted record opt-in also carries through dependent Sigma
fields, and shadowed binder names resolve to the innermost Sigma binder.
Typed wrapper arguments are encoded in declaration order, so a later Vec
argument and the dependent result can use an earlier named Nat argument. A
trusted pair adapter for a locally declared Pi signature uses those same
argument values when encoding its dependent result.
Without the required pair or record marker, generated wrappers continue to
reject dependent signatures.
Opaque bindings require explicit `runtimeType(EponymType, NimType)` mappings
to postulated Eponym types or
type families. Nim checks adapter and generated wrapper signatures;
the implementation and mapping remain trusted. Synchronous exceptions from a
Nim adapter propagate unchanged to the caller. An invoked but unbound
postulate raises a `ValueError` naming the postulate. `eponymBlock` rejects a
binding that no checked proc body references, but does not determine whether
that proc is reachable from an application entry point. Call-graph
reachability remains unsupported. The TCP demo returns
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

### QTT-guided code generation has a narrow opt-in path

`runtimeDps(name)` emits an additional `<name>Dps` Nim procedure for a checked,
non-generic Int function whose parameters are all marked `{.linear.}` and whose
body uses each exactly once. The current compiler handles Int literals,
parameters, and primitive `+`, `-`, `*` expressions. It lowers the checked term
through the destination-passing IR in
[`src/eponym/qtt_dps.nim`](../src/eponym/qtt_dps.nim), after checking the QTT
quantities, Int representation, supported term shape, and exclusive-tree
ownership. Generated code writes into a reusable destination slot, inlines
literal and parameter leaves, and reuses a small slot pool. Because this
language contains only pure arithmetic, it can evaluate either operand first
while preserving operator order; it chooses the order that needs fewer live
slots. The 200-case generated-code properties use one slot for right-skewed
four-argument arithmetic, two for a balanced four-argument expression, and
three for a balanced eight-argument expression. It also reports zero
heap-backed Eponym value cells (generated-code counts, not a process-wide
allocation profiler); properties compare its results with the regular checked
evaluator. Other term forms, generic functions, and non-Int values remain on
the normal wrapper/evaluator path. This opt-in does not change QTT acceptance
or claim unique ownership for arbitrary Nim objects.

### Host implementations remain trusted

When a postulate is eventually connected to a Nim implementation, Eponym can
check callers against the postulated type and Nim can check the adapter's
Nim signature. Neither check proves that arbitrary Nim code obeys a dependent
protocol, preserves a linear resource, or returns a value satisfying a
dependent index. Such implementations remain part of the trust boundary.
See the [trust model](trust-model.md).

### Nim ownership and lifetime at the runtime boundary

Typed postulate adapters may declare Nim `var` parameters. The bridge decodes
each Eponym argument into a mutable call-local Nim variable before invoking
the adapter. A mutation to an ordinary object value crosses back only if the
adapter returns the updated object; mutation through a `ref` value is visible
through other aliases to the same referenced storage. Ordinary adapter
parameters remain by value. `toHostValue[T]` stores a Nim value in a rooted
box for the runtime call. `ref` values, pointers, and closures still refer to
their existing storage or captured environment, so boxing them does not
remove aliases. The host adapter may retain or duplicate those references,
and raw pointer validity remains the adapter author's responsibility. There
is no explicit ownership-transfer adapter form.

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
`cons[A, n](x, xs)`; legacy call-style forms remain accepted. Supported
generic definitions have generated Nim wrappers for type parameters, Nat and
Int indices, Bool indices, and values with explicit runtime mappings. Other
value-indexed binders and unsupported argument/result codecs still lack
wrappers and produce compile-time diagnostics when explicitly requested.

Pure `if`/`elif`/`else` expressions lower to nested checked `ifThenElse`
calls when `lib/bool.ep` is imported. Each condition must have type `Bool`,
and each branch must be one Eponym expression. Boolean `and` and `or` lower
through checked Bool elimination with unit thunks, preserving Nim's
short-circuit behavior even if the right side calls a bound postulate. These
forms do not enable ordinary effectful Nim control flow inside the block.
