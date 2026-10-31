# Known limitations

## Staged runtime type injection (#499)

The `{.runtimeType.}` annotation is recognized on embedded checked
definitions and retained in compile-time metadata. The production dynamic
residual emitter and codec-factory integration are not yet enabled; annotated
definitions therefore continue through the ordinary strict compiled-wrapper
path. No evaluator-free `TypeRep` residual is promised until that integration
lands.

<!-- Maintainer note (#372, 2026-10-21): a codegen or interop merge must update
this page in the same PR when it changes runtime behavior, tiering, or
wrapper/codec coverage. Re-sync passes are not deferred "for later". -->

Eponym checks a small dependent language embedded in Nim. It is useful when
you want a compile-time guarantee about a protocol, shape, or resource use;
it does not turn an `eponymBlock` into an ordinary Nim procedure body. This
page summarizes the practical boundary. The
[surface syntax reference](surface-syntax-reference.md) lists accepted forms,
and the [trust model](trust-model.md) covers guarantees and soundness
assumptions.

## Nim-shaped syntax is still Eponym

The `eponymBlock` macro translates supported Nim syntax to Eponym and checks
it during Nim compilation. It does not run Nim code inside the block:

```nim
proc addOne(x: Int): Int = x + 1       # Eponym expression; supported
proc read(s: Socket): string = s.recv  # Nim library call; not supported here
```

Put IO, loops, mutation, and calls to Nim libraries in ordinary Nim code
outside the block. Pure `if`/`elif`/`else` expressions are supported when
`lib/bool.ep` is imported; only the selected branch runs. Supported operators
and expression forms are listed in the syntax reference.

The Nim AST translator supports selected expression shapes rather than all
Nim expressions. A direct `nil` result or a typed local such as
`let xs: List[Int] = nil` maps to the Eponym empty `List` or `Vec` constructor;
other nested `nil` expressions are not translated yet. Other unsupported
shapes now report their Nim AST kind and suggest expressing the operation in
Eponym syntax or moving host code outside the block and binding it as a
postulate. String literals, for example, are not Eponym string values.

## `Nat` and `Int` conversions are explicit

`Nat` and primitive `Int` are distinct Eponym types. A `Nat` is not silently
accepted where `Int` is expected. Import `lib/nat_to_int.ep` and call
`natToInt(n)` to convert it. The direction is total for values represented by
the runtime's Nim `int`; larger Nat values cannot fit in primitive `Int`.
`high(int)` is the runtime boundary and depends on the host architecture.
The interpreter and Phase 1 use unary `Value` constructors and can form a
larger Nat while memory permits, but `valueToNat` raises
`ValueError("runtime Nat does not fit Nim int")` when decoding it. Phase 2
stores Nat directly as `int`; its generated successor raises the same
`ValueError` at the boundary, even with Nim overflow checks disabled. No tier
silently wraps. The Phase 2 `natElim` fold is iterative but remains O(n), so
values close to `high(int)` are representable but impractical to fold. The
interpreter's constructor-based folds can also run slowly or exhaust the
stack on large inputs.
The partial direction is available through `lib/int_to_nat.ep`. Bind its
postulate to the provided `intToNatHost` Nim adapter:

```nim
eponymBlock:
  import "lib/int_to_nat.ep"
  bindPostulate(intToNat, intToNatHost, Int, Nat)
  proc checkedCount(count: Int): Nat = intToNat(count)
```

The adapter raises `ValueError("cannot convert negative Int to Nat")` for a
negative input. Conversion stays explicit because postulates can hide host
effects that their Eponym type does not prove absent. Legacy Value-bridge
tests build the imported `zero`/`suc` constructor chain; strict representation
code uses the existing host `int` after the negativity check. In a
runtime-compiled block, declare `runtimeType(Int, int)` and
`runtimeType(Nat, int)` to select those representations. Large conversions
through the legacy Value path therefore take linear time and space.

For typed runtime wrappers, `runtimeType(Int, int)`,
`runtimeType(Nat, int)`, and `runtimeType(Bool, bool)` select the Nim boundary
types while preserving each built-in Eponym value encoding. For example,
`Nat` arguments are converted to Eponym Nat values before checked code runs,
and returned Nat values are decoded back to Nim `int`:

```nim
eponymBlock:
  import "lib/nat.ep"
  runtimeType(Nat, int)
  proc doubleNat(n: Nat): Nat = add(n, n)

doAssert doubleNat(21) == 42
```

This differs from mapping a user-defined Eponym type to a Nim type, which
passes an opaque host value through the checked program. Use `runtimeCodec`
when checked code needs to inspect the structure of a user-defined mapped
value.

## Scalar host values are opaque

Import `lib/float.ep` for the checked type `Float`, and `lib/text.ep` for
`String` and `Char`. Map them with `runtimeType(Float, float64)`,
`runtimeType(String, string)`, and `runtimeType(Char, char)`. Eponym checks
that values flow through definitions and postulate signatures with those
types. Values are constructed in Nim and cross through the runtime mapping;
Eponym has no Float/String/Char literals, arithmetic, or built-in equality.
Declare operations as postulates and bind them to Nim procedures. Eponym
checks the declared signatures, while the host operations' behavior remains
trusted. This matters especially for Float equality, whose behavior around
NaN and signed zero must be chosen by the host API.

```nim
eponymBlock:
  import "lib/float.ep"
  runtimeType(Float, float64)
  postulate(scaleFloat, Float -> Float)
  bindPostulate(scaleFloat, scaleFloatNim, Float, Float)
  proc checkedScale(value: Float): Float = scaleFloat(value)
```

This is the intended v1 boundary, not a missing set of built-in operators.
Eponym's core computes over portable language values; Nim `string` and `char`
are host values (byte sequences and bytes), while floating-point results and
comparisons depend on the host's representation and runtime behavior. Adding
literals would also require choosing a portable encoding and runtime
representation. Keep these operations in Nim and expose each one through a
typed postulate. The Eponym signature is checked, and the Nim adapter
signature is checked against its codec, but the adapter's behavior is
trusted. Checked code can call a string comparison or Float operation without
losing type checking, but cannot normalize or prove facts about its result.

## Checked definitions need a runtime path

Eponym checks definitions at compile time. A checked definition is callable
from Nim only when its generated wrapper can convert arguments and results to
runtime values. Common runtime representations include:

- `Int`, `Nat`, and `Bool` (`Bool` requires `lib/bool.ep`);
- opaque Nim types registered with `runtimeType` or `runtimeCodec`;
- non-dependent `Sig` pairs, named records, and the standard `Vec`, `List`,
  and `Option` types.

For example, `runtimeVector(Vec)` maps `Vec[Int, n]` to `seq[int]` and checks
that the sequence length matches `n`. Nested vectors and vectors of mapped
opaque values work when their element type has a codec. Dynamic generic value
binders also support `Vec`, non-dependent `Sig`, `List`, and `Option` when the
corresponding codecs are registered.
For a Nat index known at runtime, pass it as an ordinary function argument
(`proc get(n: Nat, values: Vec[Int, n]): ...`). The representation backend
checks the sequence length against that argument. An erased generic index
requires runtime-computed type structure, which strict codegen does not
support. `runtimeValue`-generated dynamic siblings and raw `RuntimeValue`
wrappers are rejected inside `eponymBlock`.

Dependent Sigma binders and results are supported only when their components
have representations the backend can select while erasing the dependent
index; when no direct representation exists, the containing runtime
definition is a compile-time error. A checked but intentionally non-runtime
proof can use `compileTimeOnly(name)`. That marker does not make a runtime
codec or Value wrapper available.

Other types can still be checked by Eponym but may have no representation-tier
runtime form. A runtime definition using one is rejected; use a supported
`runtimeType` mapping or mark a proof-only definition with
`compileTimeOnly(name)`. Some dependent records and pairs need explicit
opt-ins such as `runtimeRecordTrusted` or `runtimePairTrusted`; these check
field representations but trust relationships the selected field codecs
cannot check. Generic binders over dependent records need no opt-in when earlier
fields are `Nat` and every use in later fields is checked by a structural codec,
such as a Vec length check. Other dependent record shapes can use
`runtimeRecordTrusted(Record)` to enable typed dynamic wrappers; registered
field codecs still enforce the constraints they represent. `RuntimeVariant`
preserves constructor identity and raw payload `Value`s,
while checking family membership, constructor arity, and spine shape. Encoding
validates each payload against the constructor's checked Pi domain, including
dependent domains that use earlier fields. Decoded payloads remain raw values
for callers to decode.
Imported `.ep` definitions can get typed wrappers when their Pi signature is
within the reconstruction subset, including `Univ` type parameters and
callback arrows with closure types and codec-supported leaves. Callback
arguments and results may depend on earlier outer parameters or earlier
callback arguments when their types have supported codecs. For example,
`(length: Nat, values: Vec[Int, length]) -> Vec[Int, length]` checks vector
lengths on callback input and output. Other dependent callback shapes without
supported Nim codecs and other unsupported imported signatures use the raw
`Value` interface, which checks argument count while callers supply well-typed
values. Imported checked bodies can call postulates bound in the same block.

Generic type parameters can pass values through as opaque host values when
their wrapper shape is supported; Eponym does not inspect the host
representation. Structural and indexed values need codecs to inspect their
shape. Runtime evaluation of type and index expressions supports a subset;
arbitrary type-level Nim computation and every possible Eponym index
expression are not supported by generated codecs.

### Interpreter-free generated wrappers

Every `eponymBlock` requires the representation backend for its runtime
closure: macro expansion fails unless each runtime definition and call is
compiled to direct Nim representation code and its typed wrapper is direct
too. Unsupported definitions never fall back to the interpreter or `Value`
runtime. `requireCompiled()` remains accepted as a redundant compatibility
marker. The backend supports
`int`, `seq[int]` (`Vec`/`List`), and `Option[int]` representations, plus —
since #401 — opaque identity representations and dependent `Sig` tuples:

```nim
eponymBlock:
  import "lib/vec.ep"
  postulate(Int, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  proc doubleVector(n: Nat, values: Vec[Int, n]): Vec[Int, n] = ...
```

A concrete `runtimeType` mapping whose Nim type is not `int` becomes an
identity representation: the compiled proc takes and returns the declared
host type directly, with no conversion. (A mapping for a type with a
`runtimeCodec` or `runtimeRecordTrusted` codec is excluded: the codec
defines the boundary semantics, including dependent-index checks, so the
type is outside the representation fragment until the backend can emit the
codec conversion directly.) An applied family with such a mapping
(`Chan s`, `AcceptMsg n`) denotes the one declared host type for every index
tuple — the indices are dropped from the host signature, exactly as
`Vec A n` maps to one `seq[int]`. Declaring one host type for a whole family
asserts the host layout is index-independent; the checker cannot verify host
layout, so this is trusted (see the trust model). A dependent
`Sig(x: A, B)` over representable components maps to the host tuple of the
components; the second component's representation is selected with its
index-dependence erased, which is sound precisely for index-independent
mappings. A `Vec` length index mentioning the bound Sigma value is rejected
rather than silently erased.

An index may be erased beneath a plain opaque family mapping when its host
representation is index-independent. For example, a nominal family
`Qty : Vec Int 3 -> Univ` can keep dimensions in checked types while
`runtimeType(Qty, float64)` gives every quantity the same host representation.
A dependent `Sig(d: Vec Int 3, Qty d)` can then cross the boundary as a pair
of a dimension sequence and a `float64`. The checker preserves and compares
the Eponym indices; it cannot prove that the host magnitude corresponds to
the dimension returned beside it. `bindPostulatePair` makes that adapter
contract trusted, as it is for other opaque indexed families.

In the units example, parsing and scalar quantity arithmetic are host
bindings. Their Eponym signatures are checked, but the parser and numeric
callbacks must honor those signatures. Pointwise dimension
addition/subtraction and `scaleDim` are checked Eponym Vec code; representation
codegen compiles Sigma pairs used to unpack the fixed three-coordinate vectors.
The runtime power result shares the input quantity's opaque `float64`
representation.

Postulates bound with `bindPostulate` / `bindPostulatePair[Trusted]` whose
types are fully representable get direct-call forwarders, so compiled bodies
never route postulate calls through the interpreter. Definitions referenced
only from type positions — for example `Session`-valued protocol constructors
consumed solely as `Chan` indices — are classified compile-time-only and
excluded from the runtime closure; they get no Nim wrapper, since no Nim proc
could take or return their unrepresentable types. `compileTimeOnly(name)`
explicitly marks a checked definition intended only for elaboration or proof
normalization. Such definitions get an error wrapper at the Nim boundary, and
the macro rejects any runtime definition that calls one. An unrepresentable
definition that is neither type-level nor explicitly marked compile-time-only
(for example a higher-order runtime argument or a definition referenced from
nowhere) is rejected with its representation reason instead of being silently
dropped. The tier
report (`-d:eponymCodegenReport`) names the new kinds and says why each
definition did or did not reach them.

The strict wrapper uses no `Value` runtime and rejects dynamic `runtimeValue`
entrypoints. A regression inspects the compiled artifact and confirms it has
no interpreter symbols. This guarantee applies to every `eponymBlock`.
Runtime startup can still elaborate globals; generated `Value`s retain
approximate syntax trees. Imported `.ep`
definitions are included through their transitive call closure when the
representation backend can compile them; unsupported imported code is rejected.
For an indexed `Vec`, an index that exists only in an erased binder cannot be
checked by the representation backend and causes a compile-time error.

When several `eponymBlock`s in one Nim module import the same `.ep` file,
the first block to expand publishes its compiled import-origin definitions
into a compile-time registry, and later blocks call those already-emitted
procs directly instead of re-emitting them (emitted proc names are
deterministic, so re-emission would be a redefinition error). Exports flow
in source order, so the exporting block must come first in the file. The
value tier reuses unconditionally; the representation tier reuses only when
the importing block computes the same representation signature, and only
when the definition's transitive closure references no postulate bound in
the exporting block — otherwise the later block would silently inherit the
earlier block's host implementation. The tier report
(`-d:eponymCodegenReport`) names reused definitions and their origin.

### Derived representation mappings (#402)

Representation mappings can be *derived* from the checked type structure
instead of declared by hand (`src/eponym/derive_repr.nim`). Derivation walks
the elaborated `Term` and synthesizes the host layout: products (records /
`Sig`) become host tuples, `data` families become tagged variants with
per-constructor payloads, quantity-0 binders are erased, and hand-written
`runtimeType`/`runtimeVector`/`runtimeOption` mappings are the base cases
(the analogue of hand-written `given`s in Scala 3 derivation). The derived
registration is structurally identical to the hand-written declaration it
replaces, and boundary codecs are generated componentwise, with vector
lengths over bound indices becoming codec *factories*
(`Π (idx : I) -> Codec (T idx)`; the O(1) length check is the boundary
obligation). Derivation fails loudly, naming the field and the reason, for:
leaves with no mapping, type- or function-typed fields (no honest runtime
representation exists), genuinely indexed families, and components whose
representation *kind* depends on a bound value.

Manual-only (not derivable): `runtimeOption` (traversal not landed yet), and
opaque host codecs for non-structural representations. Postulate/opaque
families are derivable with the host type declared: the block form is
`runtimeDerive(EponymType)` (issue #402, slice 3) or
`runtimeDerive(EponymType, HostType)` (slice 4) for opaque families whose
host type derivation cannot invent — derivation verifies the family is
genuinely opaque (no data constructors, not a record, type `Univ` or a
Pi-chain over `Univ`; a derivable structure is a compile error directing
at the one-arg form) and registers exactly what the hand-written
`runtimeType(EponymType, HostType)` produces. The Paxos block's
`Chan`/`Promise`/`AcceptMsg` mappings are derived this way. The
block form runs the same
derivation inside `eponymBlock`, registers the mapping alongside the manual
declarations, and emits the generated encoder/decoder procs with the block's
wrappers. Derived products register as `isRuntimeCodec` mappings (the
generated procs are the codec); derived variants register as
`isRuntimeVariant` (the existing structural conversion applies, no emission);
atoms and vectors register exactly as their manual counterparts. Products
with index-dependent vector components get the codec factory plus thin
`Encode`/`Decode` adapters that read each length index from the host tuple
field (encode) or the value's corresponding component (decode). Vector
lengths must be a single bound field or a literal — computed indices are a
compile-time error, as are duplicate declarations and derivations naming a
type with a manual mapping. `Int`/`Nat`/`Bool` are primitive base cases (no
manual declaration needed); canonical `Nat`/`Bool` use the `natToValue` /
`boolToValue` converters, matching the wrapper layer.

### Compile-time performance

Eponym checks embedded definitions during Nim compilation, so elaborator and
kernel changes affect build time. The CI benchmark compares `dependent_indices`,
the checked Paxos example, and `lib/nat_lemmas.ep` against the pull request's
target commit on the same Nim 2.2.12 runner. It reports median wall time per
corpus and flags growth above both 30% and 0.5 seconds. Smaller changes remain
visible in the report without failing CI. The lemma corpus uses a larger Nim
VM loop limit because it exceeds Nim's default; the benchmark includes that
limit in its recorded corpus definition. A first macOS 14.5 arm64 reference is
checked in at `bench/compile_time_reference.json`; CI comparisons use the PR
target on the same runner instead of comparing its absolute times with this
machine-specific snapshot.

These are regression guardrails, not promises of a fixed compile time across
machines. Existing profiles show evaluation dominates numeral-heavy checking,
while evidence-heavy arithmetic spends most of its time in the bare-core
evidence check. Preserve the kernel re-check: investigate phase costs and
optimize them without weakening the trusted boundary. If a feature warrants a
material compile-time increase, include the measured tradeoff and rationale in
its PR; change the budget only with that evidence.

The core QTT erasure pass (`eraseQ0Arguments`) replaces a checked quantity-0
application's argument with an inert unit witness, so the argument computation
is not evaluated. Public generated and interpreted runtime entrypoints both
apply erasure; the lower-level `evalWithBindings` evaluator can still evaluate
the unerased source. The type system does not track Nim effects or enforce
purity, so an operation that must run cannot be placed in a q0 argument.
Generated typed wrappers and compiled-proc computational
argument vectors omit quantity-0 values. A separate witness vector may carry a
q0 value only to instantiate a dependent runtime type, such as a Vec length;
the compiled body never receives it as a computational argument. The scalar
representation backend also omits q0 formals and local-call arguments.
Generated higher-order `Value` code represents q0 lambdas as nullary
closures; the interpreter keeps its unary representation. Differential tests
check that generated and interpreted runtime entrypoints erase q0 arguments
and run only the retained closure body. Erasure requires a closed, zonked term
whose function types can be recovered by the core inferencer.

For `eponymBlock`s without Eponym module imports, elaboration and parse errors
include the source filename, line, and column of the nearest Nim definition
body expression. Errors in imported `.ep` files report that file's path, line,
and column. The `eponym"..."` form reports positions within its Eponym string,
not Nim source expressions.

## Sheds expose semantic state in-process

The LSP can inspect a hole as a typed metavariable with a zonked goal,
structured binder context, and Pi binders. Hover uses this state. The
`.sheds.json` sidecar still stores rendered goal and context strings for the
cross-process presentation path; those strings are not parsed back into
terms. Refinement edits generated source and re-elaborates it. Draft text
in an `eponymBlock` shed is checked at macro time (issue #478): a draft
that checks fills the shed and the definition becomes ordinary; a
missing or failing draft leaves the definition use-gated — it elaborates,
but calling it (directly or through another compiled definition) is a
compile error naming the shed. A persisted semantic editing session
would need a versioned structural term codec and is not implemented.
Goal-directed Intro is available for leading Pi binders; it introduces one
binder per action.

VS Code uses client-selected, immutable Merkle proof states for all seven shed
actions: Intro, Construct, Apply, Rewrite, Refine, Give, and Case-split. Each
state-dependent query names a state ID and goal ID. The server evaluates the
action hypothetically, checks the generated proof state, and returns a
successor state and changed nodes; it does not track a selected state or wait
for a client commit. The client can switch roots and undo locally without an
LSP request. Every open goal is addressable by its stable goal ID, and
untouched sibling goals remain in successor states.

The LSP verifies node hashes and rechecks goal metadata against the checked
generated source. Its node cache is bounded by an LRU limit of 4096 nodes.
Eviction or server restart loses cache acceleration only; the client resends
missing nodes on demand. The cache is bounded by node count rather than bytes,
and nodes are not pinned during a request, so very large states may require
extra transfers. This changes transfer cost, not proof-state validity.

The editor keeps local parent/successor roots and action metadata. Undo and
Redo select roots locally; Redo can choose among branches. Writing a selected
state into the shared document is guarded by a compare against the editor text
and revision captured for that state. If intervening edits conflict, the
selected proof state remains available locally and the editor is left intact.
The extension does not save or compile after each transition; save the Nim
file to persist the source and regenerate its sidecar. A newly opened document
bootstraps from its saved source and sidecar. Session history is local to the
extension host and is cleared when the document closes or the host restarts.

Goal-directed Apply searches local hypotheses and checks their applications
against the goal. The VS Code picker is filterable; named global definitions
are not searched. Arguments fixed by the expected result are filled in, while
remaining arguments become typed sheds. Candidate discovery is bounded to
the hypotheses currently in scope and the unification the elaborator can
establish.

Goal-directed equality Rewrite uses in-scope proofs of the `Eq` family and
checks the generated eliminator transport before editing. It offers direction
and exact structural occurrence choices; definitional-but-not-structural
matches are not discovered. The `Eq`, `eqElim`, and `sym` definitions must be
in scope (for example, from `lib/eq.ep`). Goals whose motive cannot be rendered
in the current shed syntax are reported as unsupported.

Goal-directed Construct is available for datatype goals in a Nim shed. It
tries each constructor by elaborating an application with typed field holes
against the goal, then offers the constructors that check. Any unresolved
index constraints remain as ordinary field goals; feasibility is limited to
what the current elaborator can establish.

Case-splitting in a Nim shed supports parameterized and indexed datatype
families. It constructs a motive generalized over every index and carries
exact occurrences of actual index expressions from the goal into that motive.
For example, splitting `xs: Vec[Nat, suc(n)]` can generalize a target of type
`Vec[Nat, suc(n)]` to `Vec[Nat, i]` while preserving separate uses of `n` in
the outer context. The completed eliminator is re-elaborated before the splice
is returned. Parameters, index types, and targets must be renderable in the
supported Nim shed syntax.

Checked definitions can emit a runtime debug trace by importing
`lib/debug.ep` and binding its generic `debugEcho` postulate to
`debugEchoRuntimeValue` (or a custom `bindPostulateValue` adapter). It returns
the value unchanged and prints its Eponym representation when the checked
wrapper runs. This is an explicit, trusted Nim effect; checking or compiling
the definition does not print. Opaque host payloads are shown only by Nim type
name. Every application of a `bindPostulateValue`-bound postulate inside a
compiled definition must instantiate the postulate's type arguments at
statically known types; the macro then emits one typed adapter per distinct
instantiation and routes each matching call site to a direct call of the host
procedure (no per-call bindings-table lookup, no per-argument application
fold — values in the Value tier need no codecs). A call site whose type
arguments are not statically known is a compile-time error rather than a
silent slow path. When every value argument and the result of an
instantiation denote the `int` representation (e.g. `debugEcho[Int]` with
`runtimeType(Int, int)` declared), the macro additionally emits a
representation-tier adapter with the representation signature
(`int -> int`): it encodes each argument, calls the Value-tier adapter,
and decodes the result, so representation-compiled callers never allocate
a `Value` and the adapter's signature contains no `RuntimeValue`.
Instantiations outside the int fragment keep the Value-tier adapter; their
representation-tier callers fall back to the Value backend as before.

A `runtimeCodec` mapping for an unindexed Eponym type can also supply the
runtime type witness and encoder/decoder for a generic type parameter. This
lets generic wrappers and callbacks process mapped values inside containers,
such as `Vec[Tree, n]` represented as `seq[seq[int]]`. Automatic witness
inference requires one unambiguous mapping for the Nim type; a raw host value
without a generated codec still has no Eponym type witness.

Custom codecs for indexed families can also validate a dynamic generic value
against its full Eponym type, including its index. For example, a
`SizedTree[length]` codec rejects a value whose encoded tree length differs
from `length`.

Host code can build Pi and Sigma runtime type witnesses with
`runtimeArrowType`, `runtimeDependentArrowType`, `runtimeSigmaType`, and
`runtimeDependentSigmaType`; `validateRuntimeValueAgainstType` checks values
against them. `runtimeValueTypeOf(value, globals)` can infer types from runtime
syntax or checked globals, but not from opaque host values without a stored
witness. Generated wrappers can check named Pi domains and nested Sigma
fields indexed by earlier binders, such as `Sig(length: Nat, Vec[Int,
length])`. Broader dependent type expressions and arbitrary dependent generic
wrappers remain unsupported.

## Postulates connect checked code to host code

A `postulate` gives Eponym a typed operation to reason about. `bindPostulate`
connects it to a Nim procedure:

```nim
postulate(Channel, Univ)
runtimeType(Channel, ChannelHandle)
postulate(rotate, Channel -> Channel)
bindPostulate(rotate, rotateNim, Channel, Channel)
```

The binding applies to calls throughout this `eponymBlock`, including calls
from imported `.ep` definitions. Checked definitions use the postulate name;
they do not repeat the Nim implementation at each call site, and the generated
wrapper signature does not reveal which Nim procedure fulfills an internal
postulate. Keep the binding next to its postulate and review it as part of the
block's trusted code.

The Eponym checker verifies calls against `rotate`'s Eponym type. Nim checks
that `rotateNim` has the mapped Nim signature. Neither checker proves that
the Nim implementation behaves as promised, or that an opaque host value
satisfies a dependent index. Codecs, mappings, adapters, and their behavior
are trusted at that boundary.

Ordinary `bindPostulate` bindings expect Nim value parameters. When an
existing Nim adapter accepts a `var` parameter, use the explicit
`bindPostulateMutable` form. It decodes each argument into a mutable local,
calls the Nim procedure, and encodes its return value as the postulate result:

```nim
proc updateBufferNim(buffer: var seq[byte], amount: int): seq[byte] =
  buffer.add(byte(amount))
  buffer

eponymBlock:
  postulate(Buffer, Univ)
  runtimeType(Buffer, seq[byte])
  postulate(updateBuffer, Buffer -> Int -> Buffer)
  bindPostulateMutable(updateBuffer, updateBufferNim, Buffer, Int, Buffer)
  proc checkedUpdate(buffer: Buffer, amount: Int): Buffer =
    updateBuffer(buffer, amount)
```

The host procedure may take its buffer as `var seq[byte]` and return the
updated sequence. The adapter passes a decoded local as `var` and converts the
returned value back to Eponym; it does not pass the wrapper caller's Nim
variable itself by reference or transfer ownership. However, an opaque
mapping can be shallow or contain references, so mutation through shared
storage may still be visible to other Nim aliases. Eponym promises neither
isolation nor caller-variable mutation here. If you need caller-visible
mutation, keep that operation in ordinary Nim code and model the checked
result explicitly. Nim's
[`lent T`](https://nim-lang.org/docs/destructors.html#lent-type) is a borrowed
return type, not a parameter type; use an ordinary value parameter for a
read-only adapter. The adapter is trusted to preserve
the declared type and any indexed relationships, just like other bound
postulates.

Compile with `-d:eponymTrustReport` to print a per-`eponymBlock` inventory of
postulate adapters, opaque/custom runtime mappings, and dependent-pair or
record opt-ins, with the guarantee each leaves to the host. The report is
diagnostic text for code review, not a machine-readable API. The checked
`{.linear.}` annotation still applies only inside Eponym: the checker cannot
see two Nim references aliasing the same resource.

Nim proc values with supported codecs can cross as callback arguments;
noncapturing callbacks with the default `nimcall` convention are supported.
Callbacks returned to Nim must use `{.closure.}`, since checked functions can
capture runtime state. Eponym checks callback types, not Nim bodies or effects.
Async values such as `Future[T]` may pass through as opaque mapped values;
Eponym does not await, observe failure, cancel, or track async effects. Nim
exceptions from adapters propagate unchanged to the caller.

Dynamic generic binders whose Eponym type is a Pi function also get a typed
Nim `{.closure.}` overload when all callback argument and result types have
codecs. Nim checks the proc signature, and the bridge checks the value against
the checked Pi type; the raw `RuntimeValue` overload remains available.
Supported Pi types can nest, so a callback may itself receive a callback or
return one. Dynamic Pi wrappers can also accept noncapturing `nimcall` or
`cdecl` procedures; Nim checks their concrete signatures at the call site.
Dependent callback indices also flow through argument and result codecs: a
callback taking `Nat` and `Vec[Int, length]` and returning
`Vec[Int, length]` checks both vector lengths. Explicitly mapped opaque types
can also serve as callback arguments or results. Computed indices such as
`add(left, right)` are checked too when the expression has a runtime codec.
Custom codecs for indexed families are checked against dependent callback
indices on both input and output.

## Static checks do not manage Nim resources

Linear and erased quantities apply to variables inside checked Eponym terms.
They do not inspect aliases or ownership in surrounding Nim code. For
example, Eponym can check that a modeled channel is consumed once, but it
cannot tell whether two Nim references alias the same socket.

Conditional usage is path-sensitive for Nim `if` expressions and generated
data eliminators. For unindexed, first-order recursive data with a ground
result motive, usage profiles cover all finite recursive shapes. Each
generated case rule is checked against its constructor fields and recursive
calls before the analysis treats its cases as alternatives. Unannotated
binders infer quantity `1` only when the analysis proves exactly one runtime
use on every path. A `let`-bound intermediate is checked under both counts
(#484): its value evaluates once, so the value's uses count unconditionally,
and the value's context is also scaled by the bound variable's use count in
the body — so dropping or double-using a let-bound linear-derived value is
an error, as is passing it to a `q0` parameter. Pair components projected
through a let are tracked by projection path: using `fst p` and `snd p` is
one substitution use of the pair, while using `fst p` twice counts as two
uses of that component. Known global and primitive call signatures distinguish
type arguments and erased (`q0`) arguments from runtime values. If a value is
also used at runtime and passed to a `q0` argument, inference stays
unrestricted so it cannot be silently discarded as linear.

Indexed recursive families, higher-order recursive fields, closure-valued
result motives, and user-written eliminators still use conservative counting
for branch-dependent usage and can reject valid programs. For a complete
generated eliminator, a value used only as its scrutinee is known to be
consumed once; if that value also appears in another eliminator argument, the
profile stays conservative. Applications whose callable signature is not
available to the usage analyzer are counted syntactically, so erased
arguments there can prevent q1 inference. A body with unresolved holes or an
unsupported branch shape also stays conservative.

An implementation with quantity `0` or `1` may satisfy a function contract
with quantity `ω` when the quantity occurs in a covariant Pi codomain.
Function domains and nominal type arguments are compared exactly. Postulates
have no bodies to analyze, so write their required quantity explicitly.

Quantitative checking already drives code generation where the
representation choice follows the quantity: erasure (#328) and the
representation tier (#330) omit quantity-0 formals and use plain host
representations wherever the block's `runtimeType` mapping permits them.
What quantitative checking does *not* yet do is turn linear (quantity-1)
values into in-place mutation — that half of Phase 3 (#331) is still
guarantees-only. Destination-passing itself has landed in a
quantity-independent form: `vecElim`/`listElim` folds whose cons case
rebuilds (`cons xHead ih` with the accumulator as the tail and a head
that mentions neither the accumulator nor the materialized tail) compile
to a single preallocated destination instead of per-step allocation (one
`newSeq`, O(n) writes). The conditional-cons (filter) shape — a
`boolElim` cons case with a cons-rebuild true branch, the accumulator as
the false branch, and a condition mentioning only the head (and, for
`vecElim`, the index) — compiles to the same destination with a write
pointer: the condition is tested per iteration and only kept heads are
written (capacity `xs.len + acc0.len`, truncated afterwards). In-place
reuse of linear buffers has landed in its first form (#413): a chain of
linear `let` bindings over `seq[int]` (List) representations compiles to
one Nim `var` that each step moves through (`move` at the step sites),
instead of one fresh buffer per step — a length-n chain costs one
allocation plus O(total work), not O(n) buffer copies. Chains of linear
`int` bindings compile to one reassigned `var acc: int`. Qualification is
conservative and syntactic: each binding used exactly once in straight-line
position (a use under a closure-forming binder does not qualify — a single
syntactic occurrence there is not an exactly-once runtime use), the chain
representation-uniform (`Vec` excluded: in-place length changes would
falsify the length index), and, for buffers, the chain head freshly
produced rather than aliasing a caller-retained buffer. Non-qualifying
shapes keep ordinary `let` emission with identical value semantics.

### Wrapper-boundary ownership rule (#413)

Quantity-1 `seq` parameters of compiled repr procs are `sink`: the caller
moves the buffer in instead of sharing it. `sink` is a move hint only —
value semantics are unchanged, and an lvalue argument is still copied by
the caller under Nim's rules, so the boundary never aliases a
caller-retained buffer. The typed wrapper therefore copies once at entry
when the Nim caller may retain its buffer, or takes `sink` itself and
documents the ownership transfer. Never mutate a buffer the caller may
still hold: in-place mutation through a retained Nim reference would leak
through Nim value semantics. `Vec` parameters are never mutated in place
(length invariant); quantity-1 `int` parameters are plain values (`sink`
is meaningless on `int`).

Checked definitions compile to native Nim procs per definition:
in-fragment definitions run compiled `eponymCompiled_<name>` procs (Phase 1
`Value` backend) or, when their signature maps to plain host types,
`eponymCompiledRepr_<name>` procs (Phase 2 representation tier, emitting
direct host code such as Nim arithmetic). The repr tier currently covers the
scalar fragment (`Int`/`Nat`/`Bool`) plus `Vec`/`List` over int-fragment
elements (as `seq[int]`) and `Option` (as `Option[int]`). Eliminators compile to
sequence folds or `isSome` branches; each `Vec A n` parameter gets an entry
length check that raises `ValueError` on mismatch, preserving the interpreter
codec's loud failure. In the Phase 1 `Value` backend, a partially-applied or
bare eliminator eta-expands at macro time into nested `vHostFunc` closures
over the missing arguments whose innermost body is the saturated eliminator
dispatch call (#407) — the closure is an ordinary first-class function value,
so such definitions compile at the `Value` tier instead of falling back to the
interpreter. The repr tier also generates closures: a partially-applied
eliminator whose case arguments are present eta-expands at macro time into a
typed `{.closure.}` Nim proc over the missing arguments (at
representation-backend types), with the provided value arguments evaluated
left-to-right at the creation site and captured, and the saturated
eliminator match-compiled as the body (#407) — so such definitions compile
at the repr tier instead of falling back to Phase 1. Case arguments are
inlined, never passed as values: a partial application missing its step /
cons / some case is honestly rejected by the repr tier with a named
diagnostic and falls back to the Phase 1 `Value` backend (which still
eta-expands it). A bare eliminator reference has no motive, so the closure
result representation cannot be established there either. Function types
themselves are representable (#407 slice 3): a (non-dependent) function
type maps to a `{.closure.}` Nim proc type, flattened across curried binders
(`Pi x:A. Pi y:B. C` is `proc (x: reprA, y: reprB): reprC {.closure.}`), so a
closure value — a partially-applied eliminator, or a compiled definition
whose uncurried host arity matches the flattened shape — can be stored in a
`let`, passed to another compiled definition, and applied there, all at the
repr tier. Dependency of a codomain on the bound value is erased: a live
index position (a `Vec` length) mentioning it is honestly rejected, as is a
quantity-0 function domain (its argument is erased at every call site).
Passing a compiled definition whose host arity does not match the flattened
formal — e.g. after quantity inference erases an unused parameter — is
rejected with a representation error (`needs eta-expansion`). A `let`-bound
definition reference flowing into an incompatible curried formal is also
rejected; the general application path does not track the formal's expected
shape there. Nested collections, non-`int` elements, indices mentioning
quantity-0-erased binders, and declared wrapper types that disagree with the
compiled representation are likewise compile-time errors. No accepted
`eponymBlock` call falls back to Phase 1 or the interpreter. See the
[pipeline trace](paxos-pipeline-trace.md) for the stage layout. Ordinary Nim
code remains the place to choose data structures and performance strategies
the compiler does not yet exploit.

To inspect backend selection during a Nim build, pass
`-d:eponymCodegenReport`. The compile-time report names each block-local
definition's highest emitted tier, why it did not reach a higher tier, and
definition calls that still use a runtime slow path (including definitions
from other blocks or imported `.ep` files). This reports code emitted for
the definition; typed wrapper eligibility can impose an additional boundary.

## Some demos still have host-side parts

The session and Paxos examples call checked roles through representation-tier
bound Nim adapters. `linear_handles.nim` keeps its direct and omega runtime
clients; the bracket callback is checked but explicitly compile-time-only
because host postulate adapters cannot yet accept representation-compiled
closures. `qtt_borrow.nim` is also a compile-time checking example: its former
raw callback adapter invoked the Value interpreter, so its runtime buffer
backend is deferred until strict codegen supports compiled closures. The
convex examples still elaborate and check their DCP certificates, but their
custom expression trees are compile-time-only until the backend can lower
them to host variants; the Nim solver examples were removed rather than
interpreting a Value tree at runtime. The [README](../README.md#use-cases)
links to each example and summarizes these boundaries.

## Platform support

Eponym is developed and CI-tested on Linux (Ubuntu) with Nim 2.2.12.
Windows and macOS are untested: the toolchain route (building the LSP
from nimble-installed sources on first use) should work wherever Nim
and nimble run, but no Windows or macOS testing has been done. If you
try either, please report what you find.
