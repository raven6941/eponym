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

This is a runtime API, not yet a declaration accepted inside `eponymBlock`.
Property tests exercise direct and imported checked definitions, multiple
independent binding environments, incompatible Nim proc types, mismatched
Eponym postulate shapes, and duplicate bindings.

Generated `eponymBlock` wrappers still use the integer-only ABI
(`varargs[int] -> int`). The binding syntax currently accepts only unary
`Int -> Int` postulates; there is no support yet for opaque user-defined Nim
values, multi-argument callback signatures, async results, structured codecs,
or missing-binding checks before invocation.

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
