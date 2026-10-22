# Known limitations

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
There is no `Int -> Nat` conversion helper yet; any such conversion must
reject negative integers. Conversion stays explicit because postulates can
hide host effects that their Eponym type does not prove absent, so implicit
insertion could hide a call to user code.

```nim
eponymBlock:
  import "lib/nat_to_int.ep"
  proc sendCount(count: Nat): Int = natToInt(count)
```

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
For a Nat index known only at runtime, `runtimeValue(definition)` also emits a
typed `definitionDynamic(index, value)` sibling when its codecs support the
signature. It takes indices as Nim `int`, checks indexed values against them,
and returns a typed Nim result. Use the raw `definitionRuntimeValueDynamic`
overload when the value has no Nim codec; the tutorial shows a Vec example.
Dependent Sigma binders can also be passed as raw `RuntimeValue`s and checked
against generated witnesses. When the field codecs can reconstruct and check
the generated Sigma witness, Eponym also generates a typed Nim tuple wrapper
without `runtimePairTrusted`; it rejects a tuple whose Vec field disagrees
with its Nat field. Other dependent tuple shapes still need the explicit trust
opt-in and codecs that can check their fields. Generic dependent Sigma binders
can use `runtimePairTrusted(definition)` to enable typed dynamic wrappers; the
opt-in trusts correspondence with the dependent index while available codecs
still check their fields. Without that opt-in, Eponym accepts a dependency only
when every occurrence is inside a registered structural codec that checks it,
including nested Vec length constraints. Other dependent shapes remain
unsupported without the explicit opt-in.

Other types can still be checked by Eponym but may have no typed Nim wrapper.
Use `runtimeValue(name)` for the lower-level `Value` interface, or register a
`runtimeCodec`. Some dependent records and pairs need explicit opt-ins such as
`runtimeRecordTrusted` or `runtimePairTrusted`; these check field
representations but trust relationships the selected field codecs cannot
check. Generic binders over dependent records need no opt-in when earlier
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

Checked definitions can emit a runtime debug trace by importing
`lib/debug.ep` and binding its generic `debugEcho` postulate to
`debugEchoRuntimeValue` (or a custom `bindPostulateValue` adapter). It returns
the value unchanged and prints its Eponym representation when the checked
wrapper runs. This is an explicit, trusted Nim effect; checking or compiling
the definition does not print. Opaque host payloads are shown only by Nim type
name.

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

Quantitative checking already drives code generation where the
representation choice follows the quantity: erasure (#328) and the
representation tier (#330) omit quantity-0 formals and use plain host
representations wherever the block's `runtimeType` mapping permits them.
What quantitative checking does *not* yet do is turn linear (quantity-1)
values into in-place mutation or destination-passing Nim code — that is
Phase 3 (#331), still guarantees-only.

Checked definitions compile to native Nim procs per definition:
in-fragment definitions run compiled `eponymCompiled_<name>` procs (Phase 1
`Value` backend) or, when their signature maps to plain host types,
`eponymCompiledRepr_<name>` procs (Phase 2 representation tier, emitting
direct host code such as Nim arithmetic). Definitions outside the compiled
fragments keep the interpreter as a per-definition fallback. See the
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

The session and Paxos examples call checked roles through bound Nim adapters.
Other examples demonstrate checked certificates or borrowing rules, while
their optimizer or buffer driver is still ordinary Nim code. The
[README](../README.md#use-cases) links to each example and describes which
parts are connected.
