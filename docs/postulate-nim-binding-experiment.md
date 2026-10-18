# Experiment: bind Eponym postulates to Nim procedures

**Status:** unary Int `eponymBlock` binding prototype implemented; other Nim
value shapes and arbitrary postulate signatures remain unimplemented. This
work is tracked in [known limitations](known-limitations.md).

## Goal

Let a checked Eponym definition call an operation declared as a `postulate`,
while a Nim procedure supplies the runtime implementation. The first use
case is a protocol role calling transport operations whose backend uses a
Nim networking library.

The desired boundary is:

```nim
proc sendNatImpl(ch: Channel, n: int): Channel = ...

eponymBlock:
  postulate(sendNat,
    Pi(ch: Channel, n: Int, Channel))
  bindPostulate(sendNat, sendNatImpl)
  # checked role definitions may call sendNat
```

This is illustrative only. The exact surface syntax and supported Nim ABI
types remain open.

## Separate guarantees

1. **Eponym checks the declared contract.** A role using the postulate must
   satisfy its Eponym type, including dependent indices and quantities.
2. **Nim checks the adapter signature.** The generated registration or
   wrapper must refer to a Nim procedure with an accepted parameter and
   result signature. A raw TCP API will usually need a typed adapter that
   converts messages and channel state to the Eponym runtime representation.
3. **The implementation remains trusted.** Nim's type checker cannot prove
   that the procedure obeys the dependent protocol contract, preserves
   linear resources, or sends the bytes its declared result claims. A
   postulate binding is an explicit trust boundary.

## Current implementation and remaining obstacle

`eponymBlock` now accepts `bindPostulate(name, nimProc)` for postulates whose
exact Eponym type is `Int -> Int`. Generated wrappers use a call-local runtime
binding table keyed by the checked postulate reference ID; cached definitions
are not mutated. This works through imported definitions too. The Nim
adapter has the concrete signature `proc(x: int): int`, and Eponym's
postulate type is checked during macro expansion. The adapter's behavior
remains trusted.

The current low-level API looks like this:

```nim
let globals = getGlobalsDir(baseDir, source)
var bindings = initRuntimeBindings()
bindings.bindHostIntUnary(globals, "hostStep", hostStepNim)
let result = callValueFuncDir(baseDir, source, "checkedRole", args, bindings)
```

The low-level API is also available directly to callers. Property tests
exercise direct and imported checked definitions, multiple independent
binding environments, incompatible Nim proc types, mismatched Eponym
postulate shapes, and duplicate bindings.

For opaque Nim values, pair `toHostValue` / `valueToHost[T]` with a typed
adapter. Unary `bindHostOpaqueUnary[T]` handles `E -> E`; the low-level
`bindHostOpaqueBinary[A, B, C]` handles curried `E1 -> E2 -> E3` contracts.
The adapter declares which named Eponym types the Nim types represent:

```nim
bindHostOpaqueUnary[ChannelHandle](bindings, globals, "rotateChannel",
  "Channel", rotateChannelNim)
let result = callValueFuncDir(baseDir, source, "checkedRole",
  @[toHostValue(channel)], bindings)
let channelAfter = valueToHost[ChannelHandle](result)
```

This passes an opaque payload through the checked definition and back to Nim.
Eponym cannot inspect the payload or establish that it obeys a dependent
index. The mapping and callback behavior are trusted. `eponymBlock` also
accepts these mappings through `runtimeType(EponymType, NimType)` and can
generate typed wrappers for supported first-order definitions.

The binary form takes explicit mappings for both arguments and the result:

```nim
bindHostOpaqueBinary[ChannelHandle, string, ChannelHandle](bindings, globals,
  "routeChannel", "Channel", "Message", "Channel", routeChannelNim)
```

It checks the curried Eponym signature and lets Nim check the callback's
concrete `proc(ChannelHandle, string): ChannelHandle` type. Runtime property
coverage sends generated handle/message pairs through checked roles and
receives the callback result. The generated wrapper and binding support is
limited to these documented first-order forms.

A Nim closure can also be an explicitly mapped opaque argument. For example,
a postulate may take a mapped callback type and a mapped value type, while the
Nim adapter invokes the callback. Nim checks the callback's concrete proc type
at the generated wrapper; Eponym treats its body as opaque and trusted.
Returning closures from generated wrappers is not supported.

Generated `eponymBlock` wrappers support first-order primitive `Int` and
`Nat` signatures and explicitly mapped opaque types or indexed families.
`bindPostulate` supports unary `Int -> Int`, opaque `T -> T`, opaque `T -> U`,
`T -> Nat`, `Nat -> A -> B`, and curried opaque postulates with up to four
arguments. A mapped `Future[T]` may be
returned opaquely; it is not awaited and async failure/cancellation semantics
are undefined. Longer callback signatures, structural codecs, and call-graph
reachability checks remain unsupported. A binding unused by all checked proc bodies is rejected during
macro expansion. An invoked unbound
postulate raises a runtime `ValueError` naming the postulate. Exceptions raised
by a synchronous Nim adapter propagate to the caller without wrapping.

## Suggested first vertical slice

1. Define the target as arbitrary *user-defined* Nim values, with an
   explicit typed adapter/codec boundary. A Nim object or socket should be
   passable opaquely even when Eponym cannot inspect its representation.
2. Add explicit binding syntax associating one declared postulate with one
   typed Nim adapter. Reject missing, duplicate, or unbound runtime bindings
   when a reachable role is invoked.
3. Generate a typed Nim adapter at macro expansion time so incompatible Nim
   signatures fail in the Nim compiler. Keep the Eponym declaration as the
   source of the checked type; check supported structural correspondences
   and make any opaque representation mapping explicit.
4. Add a runtime host-callable value to the evaluator (or compile a callable
   Nim wrapper) and verify that evaluating a checked definition actually
   invokes the bound implementation.
5. Cover a first-order scalar example, then a user-defined channel/message
   type and an async result. Keep type-level dependent indices statically
   checked even when the runtime value is opaque.
6. Add negative coverage for a wrong Nim signature and for an Eponym role
   that violates the postulate's type.

### Initial runnable slice

The first implementation should use an explicit binding record whose fields
are concrete Nim proc values, plus an Eponym evaluator environment that maps
the checked postulate reference to a host-callable value. The macro should
generate or type-check an adapter against the declared Eponym arity and
supported runtime codecs. Calls to that postulate then dispatch through the
record at runtime. This keeps symbol lookup lexical to one embedding block
and avoids a process-global registry keyed by names or unstable reference
IDs.

Start with a first-order `Int -> Int` callback so the evaluator dispatch can
be tested independently of the ABI work. The next shape should pass an opaque
user-defined Nim handle through a callback without exposing its fields to
Eponym. A codec is required only when Eponym needs to inspect or construct a
structured value. Do not treat an opaque value's runtime representation as
evidence for a dependent index.

Nim should validate the actual proc value via an assignment to the generated
adapter type. The adapter type must reflect the Eponym contract's supported
runtime mapping; it must not merely accept an arbitrary callback and postpone
signature errors to runtime. Eponym continues to validate each checked caller
against the postulate type. The callback body remains trusted.

## Open questions

- Is binding lexical to one `eponymBlock`, or can a library export a
  postulate contract and let each importing application provide the backend?
- Are bindings direct Nim symbols, explicit adapter closures, or a generated
  record of operations?
- How are exceptions and async results represented at the checked boundary?
- Does a linear channel token have a runtime representation that prevents
  accidental aliasing, or is linearity only a static contract?
- What codecs are required for structured data whose values must be
  inspected or serialized, versus opaque values that are only passed to and
  returned from a postulate?
- How should errors distinguish the checked declaration, adapter signature,
  and trusted implementation behavior?
