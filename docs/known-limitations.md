# Known limitations

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

## `Nat` and `Int` conversions are explicit

`Nat` and primitive `Int` are distinct Eponym types. A `Nat` is not silently
accepted where `Int` is expected. Import `lib/nat_to_int.ep` and call
`natToInt(n)` to convert it. The direction is total for values represented by
the runtime's Nim `int`; larger Nat values cannot fit in primitive `Int`.
There is no `Int -> Nat` conversion helper yet; any such conversion must
reject negative integers. Conversion stays explicit because postulates can
hide host effects that their Eponym type does not prove absent, so implicit
insertion could hide a call to user code. The current interpreter evaluates
Nat folds recursively, which can limit performance and stack depth for large
runtime values.

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

The core QTT erasure pass (`eraseQ0Arguments`) replaces a checked quantity-0
application's argument with an inert unit witness, so the argument computation
is not evaluated. The current interpreter and host-call ABI still retain the
parameter/application slot; full ABI erasure and generated native code are
future codegen work. Erasure requires a closed, zonked term whose function
types can be recovered by the core inferencer.

For `eponymBlock`s without Eponym module imports, elaboration and parse errors
include the source filename, line, and column of the nearest Nim definition
body expression. Blocks that import `.ep` files still report generated
Eponym-source positions; tracking positions through imported files remains
open. The `eponym"..."` form reports positions within its Eponym string, not
Nim source expressions.

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

The Eponym checker verifies calls against `rotate`'s Eponym type. Nim checks
that `rotateNim` has the mapped Nim signature. Neither checker proves that
the Nim implementation behaves as promised, or that an opaque host value
satisfies a dependent index. Codecs, mappings, adapters, and their behavior
are trusted at that boundary.

Nim proc values with supported codecs can cross as callback arguments;
noncapturing callbacks with the default `nimcall` convention are supported.
Callbacks returned to Nim must use `{.closure.}`, since checked functions can
capture runtime state. Eponym checks callback types, not Nim bodies or effects.
Async values such as `Future[T]` may pass through as opaque mapped values, but
Eponym has no `await`, cancellation, or async effect system. Nim exceptions
from adapters propagate to the caller.

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

## Static checks do not manage Nim resources or optimize code

Linear and erased quantities apply to variables inside checked Eponym terms.
They do not inspect aliases or ownership in surrounding Nim code. For
example, Eponym can check that a modeled channel is consumed once, but it
cannot tell whether two Nim references alias the same socket.

Quantitative checking currently provides guarantees, not a general code
generation optimization: Eponym does not automatically turn linear values
into in-place mutation or destination-passing Nim code. Runtime wrappers
evaluate checked Eponym values through the runtime bridge; ordinary Nim code
remains the place to choose data structures and performance strategies.

## Some demos still have host-side parts

The session and Paxos examples call checked roles through bound Nim adapters.
Other examples demonstrate checked certificates or borrowing rules, while
their optimizer or buffer driver is still ordinary Nim code. The
[README](../README.md#use-cases) links to each example and describes which
parts are connected.
