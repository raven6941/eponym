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
wrappers when the remaining signature has codecs. Nim values of generic type
`A` cross as opaque boxes. If the checked runtime body uses `A` as a type
argument, the wrapper passes its Eponym type witness when the concrete Nim
type has a unique direct `runtimeType` or `runtimeCodec` mapping; generic
values use the selected codec. 200-case properties cover constructing a Vec
inside such a generic body through both the generated wrapper and typed
`RuntimeValue` API, for opaque and custom-codec host types. Unmapped,
ambiguous, and indexed-family mappings remain unsupported. A scalar Nim type
can be used when the block has a unique explicit direct mapping, such as
`runtimeType(UserToken, int)`; a generic wrapper reports a compile-time
ambiguity if multiple Eponym types map to the same Nim type. A 200-case property
covers an imported generic function returning `Vec[RuntimeScalar, 1]` through that
mapping and both generated and `RuntimeValue` wrappers.
Value-indexed Nat binders written
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
Imported definitions whose sole argument is Eponym's unit type also generate
zero-argument Nim procedures; typed and `RuntimeValue` wrappers supply the unit
internally.
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
covers typed wrappers and raw `RuntimeValue` closures. Imported generic
definitions can accept typed Nim callbacks when the generic Nim type has a
direct `runtimeType` or `runtimeCodec` mapping; a 200-case property covers an
`A -> A` callback over a mapped Nim enum through generated and `RuntimeValue`
wrappers and another covers a custom-`runtimeCodec` mapped Nim object. A
third 200-case property exercises `Option[int]` callbacks through the
recursive structural codec, including `none` and `some`. A compile-time check
rejects a mismatched callback signature.
Callers must handle unsupported constructors and neutral values explicitly. A
Right-nested `Sig` values map to flat Nim tuples with the same field order and
arity, while their runtime representation remains right-associated pairs.
Recursive codecs support `Int`, `Nat`, Bool, and explicitly mapped opaque
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
Non-dependent record fields may also contain function values. When the field
type has supported runtime codecs and the Nim field is a closure, generated
record codecs pass that closure into checked Eponym code; a 200-case property
tests both the typed call and `RuntimeValue` wrapper.
The canonical length-indexed `Vec` family has
an explicit
`runtimeVector(Vec)` codec that maps `Vec[A, n]` to `seq[A]`. It checks the
host sequence length and the runtime Nat index at each `cons` cell; the
element type uses its recursive runtime codec, including nested vectors such
as `Vec[Vec[Int, m], n]` mapped to `seq[seq[int]]`. The codec accepts Nat length
expressions made from a static index, `zero`, `suc`, `add`, and `mul`. It
requires the standard `nil` and `cons` constructor shape from `lib/vec.ep`.
For fixed-size Nim data, `runtimeVectorArray(Vec)` instead maps
`Vec[A,n]` to `array[n,A]`; the array size must be statically known to Nim.
Static Nat generic binders are inferred from the array argument. Dynamic
siblings are not generated when their runtime Nat argument would have to
change a Nim type. Arrays can also cross supported checked Nim closure
arguments and results, including nested fixed-size arrays such as
`array[3, array[2, int]]`. Primitive and explicitly mapped opaque elements
are covered by tests. The same element codecs and Eponym tail-index checks
apply recursively.
The standard unindexed `List[A]` family also has a `runtimeList(List)` codec
that maps to `seq[A]`, checks constructor identities and spines, and recursively
uses the element codec. A unary family with canonical `none` and `some`
constructors can opt into `runtimeOption(Option)`, which maps recursively
codec-supported payloads to `std/options.Option[A]`. Custom `runtimeCodec`
leaves are property-tested through all three codecs, including generated
wrappers and typed and raw `RuntimeValue` calls. Other collections and
payload-bearing data types need an explicit codec when no built-in mapping is
available.
Recursive Vec and Option encoders preserve their represented Eponym element
types, including nested vectors and fixed Nat lengths; the bridge no longer
uses `Type 0` as the encoded element type when it can reconstruct the declared
type.
A mapped `Future[T]` can pass through an opaque postulate adapter as either an
argument or result; the bridge preserves the same Nim future value. Eponym
has no async effect, await, or cancellation operation. Completion, failure,
and cancellation remain Nim runtime behavior: Eponym does not observe or
transform them. Future values can also be the result of a Nim callback passed
through a typed postulate adapter; a property checks that the same Future
object crosses generated and typed `RuntimeValue` calls without being awaited.
The same opaque result can cross a callback supplied to a dynamic generic
binder; a 200-case property checks that generated and `RuntimeValue` dynamic
wrappers return the exact Future object unchanged.
Nim `{.async.}` procedures returning that mapped `Future[T]` also satisfy
typed postulate adapters and dynamic generic callback parameters. A 200-case
property invokes an async procedure through generated and `RuntimeValue`
wrappers for both paths and confirms each result after Nim awaits the Future.
Async scheduling and failure behavior remain owned by Nim.
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
These function values can also cross into typed Nim `bindPostulate` adapters,
including adapters for imported postulates. The host adapter can invoke the
callback, while macro expansion checks its full function signature; a property
covers captured callbacks and a compile-error fixture rejects mismatched leaf
types. Outer Pi indices also reach the callback codec: a host adapter can
invoke a callback returning `Vec[Int, length]`, and the bridge rejects a
wrong-length result. A Nim callback with an omitted `void` result maps to
Eponym unit; its side effects run at the host boundary and the checked result is
validated as unit.
Nullary Nim callbacks map to Eponym functions from unit (`1`) to the callback
result. The adapter supplies a unit argument when invoking a checked Eponym
function and validates that unit when a host callback enters the evaluator.
The checked Pi signature is compared with the nullary Nim proc type; a unary
callback cannot satisfy it.
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

Typed structural codecs include `Vec`, `List`, `Option`, nested `Sig` tuples,
named records, and recursive `runtimeDataVariant` values. The general typed
`bindPostulate` codec path supports these tuples at arbitrary field arity; the
convenience `bindPostulatePair` form remains specialized to two result fields.
Records with dependent fields and dependent `Sig` results are available only through their
explicit trusted opt-ins described above.
Imported generic definitions can also accept callbacks whose generic leaf type
appears inside a mapped `Vec`, `List`, or `Option`, or a supported nondependent
`Sig` tuple or a `runtimeDataVariant` family; the direct leaf `runtimeType` or
`runtimeCodec` mapping is carried into the recursive callback adapter.
Separate 200-case properties cover these shapes over a custom mapped object.
When a generic host type appears in both a callback parameter and a separate
value parameter, Nim can infer the generic type from the value even if the
callback comes first in the call. The generated adapter invokes that callback
using the codec-derived concrete signature, so an incompatible callback still
fails Nim compilation. This works for local and imported definitions, through
generated wrappers and typed `RuntimeValue` overloads.
An imported dependent `Sig` callback can opt into typed tuple codecs with
`runtimePairTrusted`; recursive Vec codecs still check represented lengths.
Properties reject wrong Vec lengths in both callback inputs and results.
For fixed vector lengths, the same generic callback bridge also supports Nim
arrays through `runtimeVectorArray(Vec)`.
Other structural callback families and generic leaf types without a unique
direct mapping remain unsupported.
`runtimeValueTypeOf(value, globals)` recovers the checked type of a runtime
Value, including represented family indices. Imported generic callback
wrappers can use a direct value argument of the same generic type to infer the
erased type argument and check callback inputs/results. Both
`runtimeDataVariant` and indexed `runtimeCodec` mappings are covered by
properties, including rejection of a callback result with the wrong index.
When the only representative is nested in a structural value, or no
representative exists (`none` or an empty collection), callers still need an
explicit witness, with these supported paths: a direct `Option.some(value)`
argument with a mapped indexed payload; nonempty `Vec[A,n]` or `List[A]`
values, directly or nested in `Option`; and a direct generic field in a
nondependent `Sig` tuple. A `some(value)` Option field in a supported Sigma
tuple can also provide an indexed payload witness, and a nonempty mapped
`Vec[A,n]` field can provide the generic witness inside a `runtimePairTrusted`
dependent Sigma. The wrappers infer the payload's index and validate callback
inputs/results. `none` reports that it cannot infer an Option witness and
directs callers to use `some(value)` or the raw generic `RuntimeValue`
interface with an explicit type Value. Empty Vec and List values still need an
explicit witness. For indexed container witnesses, the runtime bridge projects
the element type from the outer constructor and validates the structure against
that expected type, avoiding recursive type inference over the complete
container. A vector with the wrong declared length is rejected by the ordinary
length check.
A `some(value)` at any depth of nested Option layers can provide an indexed
witness, as long as every layer contains a value. Empty layers cannot provide
the witness and raise a `ValueError` directing callers to supply an explicit
type argument through the raw generic `RuntimeValue` interface.
A property covers an indexed `SizedTree` identity through the raw generic
`RuntimeValue` interface.
More complex generic domain expressions outside the supported type-expression
forms and structural inspection of closures are unsupported.
Non-dependent function domains written with `->` are now supported for dynamic
generic binders: the runtime bridge infers a checked Eponym closure's function
type, validates it against the declared arrow type, and permits calling it.
Typed Nim callback adapters retain their checked Eponym arrow type as a runtime
witness, so these callbacks can also be supplied to dynamic generic binders and
checked before invocation. A 200-case property covers both checked and host
callbacks through generated and raw runtime APIs. Nested non-dependent arrows
are represented recursively. Named dependent `Pi` telescopes are also
reified, including callback domains such as `Pi(n: Nat, Vec[Int,n])`; a
200-case property exercises both generated and raw runtime calls and rejects a
callback with the wrong Vec element type. Computed indices that apply checked
library definitions are supported too: a 200-case property checks a Nim
callback with type `Nat -> Vec[Int, add(n, 1)]` through generated and
`RuntimeValue` wrappers and rejects a result with the wrong computed length.
Multiple named binders also work in computed result indices, such as
`Pi(left: Nat, right: Nat, Vec[Int, add(left, right)])`. Both callback
parameters receive distinct runtime references and the result length is
checked through generated and `RuntimeValue` wrappers. Other dependent type
expressions outside the supported runtime type grammar, and hand-built host
closures without an Eponym type witness, still cannot be checked this way. For
supported callback binders, generated `nameDynamic` and `nameRuntimeValueDynamic`
overloads accept the corresponding Nim closure type directly; a `Value`
overload remains available for callers using the low-level runtime API. Nim
multi-argument callbacks map to their curried Pi telescope and are property-
tested through both generated dynamic entry points. Named noncapturing
`nimcall` procedures also pass directly to the synthesized closure parameter
for generic callback binders, and are covered through both dynamic APIs.
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
not prove that host code obeys the Eponym contract. A property test covers a
custom codec on both sides of a bound typed postulate through generated,
typed `RuntimeValue`, and raw `RuntimeValue` calls.

This is an ABI/runtime limitation, not an elaborator restriction. The
`eponymBlock` macro supports `bindPostulate` for unary `Int -> Int`, unary
opaque `T -> T`, opaque `T -> U`, `T -> Nat`, `Nat -> A -> B`, and curried
opaque postulates with typed runtime codecs for every argument and result.
Typed adapter annotations also accept applied structural types such as
`Option[RuntimeHandle]`; for locally declared postulates, the macro checks the
full annotated signature against the postulate. Imported postulate types are
reconstructed from checked globals and receive the same comparison, including
applied family arguments. For named Pi binders, typed adapters carry earlier
decoded arguments into later codecs: a bound `Nat -> Vec[Int, length] ->
Vec[Int, length]` operation checks the Vec length on input and output. The same
path is property-tested with a custom `runtimeCodec` for Vec elements, including
mismatched-length rejection through typed and raw runtime calls. Indices that a
codec cannot represent remain the adapter author's responsibility. A checked
Eponym function argument can also cross this adapter boundary as a Nim closure
proc type; the adapter can invoke it, while the closure body remains host
behavior. A 200-case property exercises a captured callback through a checked
role and its typed `RuntimeValue` wrapper.
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
The usage checker does not automatically select this backend, even when it
proves a term linear; users must request it explicitly with `runtimeDps(name)`.

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
Eponym parameters use square brackets, as in `Vec[A, n]` and
`cons[A, n](x, xs)`. Calls to known Eponym signatures with required explicit
binders are compile-time errors; Nim command-style applications are checked
too. The guard follows known signatures through local and imported definitions,
returned calls, callback parameters, local aliases, conditionals, type
ascriptions, and typed record-field projections. Implicit binders can still be
inferred in ordinary value calls. Unambiguous legacy applications with excess
arguments or a type name in the explicit position are rejected. The guard is
metadata-driven: where overloaded or ambiguous Nim field/callable shapes do not
identify one Eponym signature, it avoids guessing. Unsupported Nim AST forms
are rejected by the converter rather than treated as Nim computations.
Supported
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
Boolean `xor` is also supported and evaluates each operand once before the
checked Bool case split, matching Nim's eager operand evaluation.
The integer literal `1` is emitted as Eponym's unambiguous `01` spelling in
term and type positions so it can be overloaded by the checked expected type
as either `Int` or `Nat`; it does not become a Nat successor unconditionally.
