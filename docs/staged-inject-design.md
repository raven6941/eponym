# Staged `inject` for runtime type structure

Status: Phase 2 bounded residual-emitter slice for issue #499. The generic
family API is evaluator-free and strict, but automatic block wiring and codec
factory integration remain future work.

## Problem and boundary

Ordinary runtime codecs need only a value representation for an already-known
type. A `Vec` index, for example, is erased from the Nim element type and
checked against the sequence length at the wrapper boundary. Tier 2 is the
rarer case where a runtime value selects the *shape* of a type that a runtime
consumer must then inspect. `PrintfType format` is a small example: a runtime
`Format` value selects a chain of argument types and ultimately `String`.

The interpreter must not cross this boundary. `inject` is a compile-time
stager that takes an elaborated type-level term and produces ordinary Nim code
for the dynamic part of its computation. The resulting `TypeRep` is an
internal descriptor consumed by generated wrappers or codecs. Eponym programs
do not get to inspect arbitrary Nim type objects, and unsupported residuals
are compile errors.

## Binding-time and staging rule

At a call site that opts into injection:

1. Elaborate the annotated family definition and its dependencies as usual.
2. Mark the type-level program and all known arguments static. Mark runtime
   indices and values dynamic.
3. Evaluate beta-redexes, constructor tests, and recursive calls whose inputs
   are static. Emit the selected result as static data.
4. When a case split or recursive call depends on a dynamic value, emit a Nim
   branch or recursive call. Stage each branch under its constructor pattern;
   static branch work is reduced before it is emitted.
5. Return the residual function with a family-specific `TypeRep` result.

The initial trigger should be explicit on the *type-level family* (the issue
uses `{.runtimeType.}` as a candidate spelling). An unannotated definition
keeps current erasure behavior. The trigger is transitive over calls from the
annotated family, but does not mark unrelated definitions for residualization.
No supported-subset promise is needed: the stager either residualizes the
checked term or reports the first unsupported operation with its Eponym
source location. It must never emit a call to `evalWhnf`, `evalWithBindings`,
or another interpreter entry point.

Large elimination is a separate prerequisite from runtime injection. The
`univ-stratified-flag` experiment enables a block to elaborate `Univ : Univ`
and check definitions such as `PrintfType`; it does not residualize a dynamic
format or make its runtime result inspectable. The design composes the two
steps: the stratified checker establishes the type-level program, then
`inject` stages that checked program against dynamic inputs.

## `TypeRep` v1

Use a closed, family-specific algebraic data type generated from the checked
family, rather than a universal type interpreter:

```text
PrintfTypeRep = Nat | String | Arrow(PrintfTypeRep, PrintfTypeRep)
```

The consumer sees only the descriptor operations generated for its family
(or a private constructor set in generated code). Nim users do not pattern
match on Eponym terms or receive `RuntimeValue`. More general applications
can later generate per-family descriptor algebras from Eponym constructors;
v1 does not require abstract interpretation, open reflection, or a global
universe of host types.

For `Format = Number Format | Str Format | End`, the defining equations are:

```text
PrintfType(Number f) = Arrow(Nat, PrintfType(f))
PrintfType(Str f)    = Arrow(String, PrintfType(f))
PrintfType(End)      = String
```

If `Number(Str End)` is known at staging time, the stager returns the static
descriptor `Arrow(Nat, Arrow(String, String))`. If only the suffix is dynamic,
it emits a residual recursive case split for that suffix and wraps it in the
static prefix. The generated code contains only descriptor constructors,
branching, and recursion.

## Prototype and evidence

`src/experimental/staging/printf_inject.nim` is the vertical-slice prototype.
Its `injectPrintfType("NS", runtimeSuffix)` macro consumes the literal prefix
at expansion time and emits a residual function for the dynamic `Format`
suffix. The family equations are written explicitly in this spike; the
prototype does not yet extract them from an elaborated Eponym definition.

`tests/test_staged_printf_inject.nim` exercises two runtime suffixes and a
partially static prefix. It inspects the linked binary with `nm` and rejects
the Eponym interpreter entry points. The prototype module imports only Nim's
macro support; the runtime residual has no Eponym evaluator dependency.

This demonstrates the binding-time boundary and residual `TypeRep` shape,
not production integration. In particular, the spike does not yet compile a
surface `proc PrintfType(f: Format): Univ` from Eponym source.

## Production work remaining

- Expose the checked Eponym definitions and eliminator metadata to the stager
  without re-parsing source or trusting unchecked Nim AST.
- Thread host representation declarations from the wrapper backend into
  `stageFamily`, and wire marked block definitions to the generated residual
  proc. The current API residualizes beta/let terms, Nat eliminator splits,
  static Nat/String/Arrow descriptors, and recursive calls in that slice.
- Generate and validate family-specific `TypeRep` constructors, and connect
  the result to a real consumer such as `runtimeDerive` codec factories.
- Define cache keys for residuals and ensure source changes, bindings, and
  representation declarations invalidate them.
- Keep generated interfaces private, produce source-located diagnostics for
  unsupported staging, and assert in tests that residuals contain no
  interpreter dependency.
- Measure compile-time growth and runtime cost on codec-factory inputs before
  choosing eager residualization versus a staged cache.
- Keep the stratified-universe flag experiment separate for this release;
  issue #492 records why its elaboration-only behavior is not yet sufficient
  under strict wrappers. Revisit integration after staged runtime injection
  and a separate universe-policy soundness review.
