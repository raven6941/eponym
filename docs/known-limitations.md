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
against generated witnesses. Typed Nim tuples require `runtimePairTrusted`
and codecs that can check the dependent fields.

Other types can still be checked by Eponym but may have no typed Nim wrapper.
Use `runtimeValue(name)` for the lower-level `Value` interface, or register a
`runtimeCodec`. Some dependent records and pairs need explicit opt-ins such as
`runtimeRecordTrusted` or `runtimePairTrusted`; these check field
representations but trust relationships the selected field codecs cannot
check. `RuntimeVariant` checks constructor identity, family membership, arity,
and spine shape, but leaves payloads as raw `Value`s for the caller to decode.
Imported `.ep` definitions can get typed wrappers when their Pi signature is
within the reconstruction subset, including `Univ` type parameters and
callback arrows with closure types and codec-supported leaves. Callback
arguments and results may use indices from earlier outer parameters, such as
`Vec[Int, length]`; the host codec checks the vector length. Callback-local
dependent signatures and other unsupported imported signatures use the raw
`Value` interface, which checks argument count while callers supply well-typed
values. Imported checked bodies can call postulates bound in the same block.

Generic type parameters can pass values through as opaque host values when
their wrapper shape is supported; Eponym does not inspect the host
representation. Structural and indexed values need codecs to inspect their
shape. Runtime evaluation of type and index expressions supports a subset;
arbitrary type-level Nim computation and every possible Eponym index
expression are not supported by generated codecs.

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

Callback values can cross when their Nim proc type has supported codecs;
returned callbacks must use `{.closure.}`. Eponym checks the callback type,
not its Nim body or effects. Async values such as `Future[T]` may pass through
as opaque mapped values, but Eponym has no `await`, cancellation, or async
effect system. Nim exceptions from adapters propagate to the caller.

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
