# Eponym — Project Plan and Architecture

> **Maintenance contract:** this file lives on `main` and describes the
> *expected* architecture — where the project is heading, not just where it
> is. When a merged branch changes the architecture (new layer, new pipeline
> stage, new core), update this file in the same merge. If reality drifts
> from the plan, either change the plan or file an issue; never let them
> silently diverge.

## The idea

Eponym is a dependently-typed language **embedded in Nim**. It is
deliberately not a standalone language: no compiler, stdlib, package
manager, or community to maintain and market. The dependent reasoning
lives in library code; users get the safety through a normal-looking API
without writing dependent types themselves.

The thesis: twenty years of dependently-typed languages (Epigram, Agda,
Idris) stalled on the adoption problem — each asked programmers to buy a
whole new ecosystem. A library in a language people already use is a much
easier sell. The target case is a session-type library: protocol
violations rejected at compile time through plain `send`/`recv` calls
(issue #28). The in-memory and TCP session examples already run checked
sender/receiver roles through bound Nim postulates. The Paxos demo now runs its
checked proposer and acceptor through bound TCP adapters. The borrow and
vector logistic examples retain separate runtime implementations; the
single-variable DCP example interprets its checked objective at runtime. The
embedding applicability plan below tracks those remaining gaps.
Deliberate-embedding prior art:
Turnstile/Turnstile+ (the architectural ancestor — dependent type systems as
macros), SynQ, Liquid Haskell.

## Architecture overview

Three views of the same system: the **embedding pipeline** (what happens
at compile time), the **layer stack** (dependency discipline), and the
**Track C vision** (where the elaborator is heading).

### 1. The embedding pipeline

User code is ordinary Nim. Eponym surface syntax appears inside a macro;
the macro elaborates it at compile time and splices ordinary Nim code
back. The target is for proof terms and static evidence to have no runtime
cost, with runtime values crossing an explicit typed boundary. Current
wrappers support first-order `Int`/`Nat` and explicitly mapped opaque
postulated types; unsupported signatures retain the legacy
`varargs[int] -> int` wrapper. The first runtime call re-elaborates the block
and caches its checked terms and globals for subsequent calls. External
postulates can be bound for unary Int, unary opaque, mixed Nat/opaque, and
typed opaque adapters of arbitrary curried arity when every argument and
result type has a runtime codec.

```
┌──────────────────────────────────────────────────────────────┐
│  Nim source: ordinary Nim + eponymBlock surface syntax       │
└──────────────────────────┬───────────────────────────────────┘
                           │ macro expansion (compile time)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Surface syntax                                              │
│  parse_surf.nim (string parser)  ·  mac_surf.nim (Nim AST)    │
└──────────────────────────┬───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  PreTerm — named preterm AST, the common interchange          │
│  preterm.nim                                                 │
└──────────────────────────┬───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Elaborator — bidirectional inferTm/checkTm                  │
│  elab.nim                                                    │
│    · metavariables + Miller-pattern unification (unify.nim)   │
│    · implicit insertion                                      │
│    · conversion checking (not just unification)              │
│    · data desugaring → postulate/elim/red                    │
│    · clause compilation → eliminators (issue #32)            │
│    · termination checking (issue #36)                        │
│    · equality as overridable effect: handler stack,          │
│      coreValid vs extending handlers (issue #41)             │
│    · positivity checking (issue #33, planned)                │
│    · constructor disjointness: noConfusion, noCycle (#80)    │
│    · multi-file programs: `import` decls, ModuleDriver,     │
│      elabCheckFile entry point (issue #49)                   │
└──────────────────────────┬───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  QTT core — small trusted kernel, quantities in judgments    │
│  eponym.nim (finally-tagless)  ·  eponym_init.nim (initial)   │
│  postulate / elim / red declarations; wRed values            │
└──────────────────────────┬───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Ordinary Nim — residual code, compiled as usual              │
│  eponym_mac.nim / eponym_embed.nim                           │
└──────────────────────────────────────────────────────────────┘
```

Design rule: the core never learns pattern matching, coverage, or
termination. The elaborator compiles all of that down to eliminator
applications and reduction rules. The trusted core stays small; the
elaborator does the work once.

### 2. The layer stack

Three layers, strict dependency discipline — each independently useful,
upper layers depend on lower ones, never the reverse. (See
`docs/layers.md` for the full contract.)

```
┌──────────────────────────────────────────────────────────────┐
│  Layer 3: Eponym — the dependently-typed language            │
│  elab.nim, eponym.nim, eponym_init.nim, unify.nim,                │
│  surface syntax, eponym_mac.nim, eponym_embed.nim,                │
│  egraph.nim, lsp.nim                                              │
│  May use Layers 1–2 for staging/relations, but the core       │
│  must work without them.                                     │
└──────────────────────────┬───────────────────────────────────┘
                           │ uses (never depends on)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Layer 2: Relational programming — miniKanren engine         │
│  minikanren.nim (fair FIFO search, =/=, setEqo, constraints)  │
│  rel_elab.nim (typeo), rel_interp.nim (evalo) — toy clients   │
│  May use Layer 1 for staging; must not import Layer 3.       │
└──────────────────────────┬───────────────────────────────────┘
                           │ uses (never depends on)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Layer 1: Staging — general infrastructure, DSL-agnostic      │
│  lms_staging.nim (LMS-style Rep), staged_codegen.nim,         │
│  staged_macro.nim                                            │
│  Depends on nothing.                                         │
└──────────────────────────────────────────────────────────────┘
```

Cross-layer research files (staged_synth, synth_staged,
specialized_engine, unified_driver, sudoku_*) explore the interplay;
they are experiments, not infrastructure.

### 3. The Track C vision — where the elaborator is heading

The long-term bet: write the language spec **once, relationally**, and
derive efficient tools (inference, checking, synthesis) for each
*direction* via staging. The relational elaborator must then be compared
head-to-head against the direct elaborator (issue #26). The relational
path stays experimental until that comparison happens.

```
┌──────────────────────────────────────────────────────────────┐
│  Relational spec — ONE definition, many directions           │
│  typeo(tm, ty, ctx): infer / check / synth modes              │
│  evalo(tm, val): forward eval / backward synthesis            │
│  (slow, general — the source of truth)                        │
└──────────────────────────┬───────────────────────────────────┘
                           │ stage by mode (what's known at
                           │ compile time?)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Staged tools — one efficient procedure per mode              │
│  inferType, checkType (term static)                          │
│  synthNat, synthArr (type static)                            │
│  stageEval (term static)                                      │
│  measured: 61x–17,000x over interpretive; correct            │
└──────────────────────────┬───────────────────────────────────┘
                           │ specialize the engine itself
                           │ (2nd Futamura projection)
                           ▼
┌──────────────────────────────────────────────────────────────┐
│  Specialized engine — dedicated reps, no generic dispatch     │
│  546x over staged; ~9Mx over naive                           │
└──────────────────────────────────────────────────────────────┘
```

Current status: demonstrated on toy STLC+Nat+Vec (`typeo`/`evalo`).
The real target is staging *elab.nim itself* — metavariables,
implicits, conversion and all.

## Roadmap

Completed experiments (see `plan.org`, `decisions.org`):

| # | Experiment | Result |
|---|-----------|--------|
| 1 | Surface syntax (string parser + Nim-AST macro) | Thin string-literal macro chosen |
| 2 | Compile-time elaboration via macros | Hybrid: string literal through macro |
| 3 | Metavariables, Miller unification, implicits | Bidirectional infer/check works |
| 4 | Extensible reduction (`postulate`/`elim`/`red`) | Bool/Nat eliminators compute |
| 5/5b | Indexed families + conversion in checkTm | `Vec`, `append` with `add` in indices |
| 6 | Tactics and reflection | `refl`/`assumption`; API in progress |
| 7 | LSP tooling | Diagnostics; holes/goals in progress |
| 8 | Staged ETT evaluator | Tagless-final staging works |
| 17 | ETT staging rules (Phase 2 validation) | Sym[SVal] with staging-time beta-reduction; twice/const/pairSwap staged == unstaged; 15.8x hoisting speedup, 0.67x on pure dispatch (negative) |
| 9 | Erasure (QTT-lite) | Superseded by #66: QTT is the core now, not a post-pass |
| 10 | Conversion cache | Exact memoization; e-graph future |
| 11 | Primitive Int | Machine int via wRed; literal overloading |
| 12 | Propositional equality | `Eq`/`refl`/`J`; `plusReducesZ` proven |
| 19/35 | Staged typeo benchmark + residual compiler | 1.90x vs compiled unstaged; 9/9 correct |
| 27 | Mode inference for relational staging | Inferred modes reproduce manual ones |
| 26 | Staged relational elaborator vs direct | REOPENED 2026-10-09: checker parity + negative staging result closed it early; finishing requires #59 (elabo with output terms) + #57 (direct-style codegen) |
| 60 | Compiled defunctionalized code pointers (compileD) | 1.9x→~1.4–1.7x gap vs baseline; closure-call indirection left to #72 |
| 64 | QTT prototype (ETT + linear binders) | Post-elaboration usage checker; feasibility step for #66 |
| 66 | QTT as the core type theory | Quantities in the judgments: in-judgment enforcement, quantity-aware conversion, quantity polymorphism, subject-side checking-mode tracking |
| 80 | Constructor disjointness | noConfusion/noCycle as named disequality facts; fail-fast unification, early impossible-clause rejection |

In flight (ordered):

1. **#26 — finish the staged relational elaborator** (reopened 2026-10-09):
   what shipped was a relational *checker* plus incomplete staging
   (specialized interpreter, 11–87x slower). Per Aaron these are not
   follow-ups but the remainder of #26 itself:
   - #59: `elabo(tm, ty, ctx, etm)` — relational elaboration producing
     elaborated terms, differential-tested against `checkTermElab` output
   - #57: residual direct-style codegen (no Goal/Stream layer),
     head-to-head wall-clock verdict vs the direct elaborator
   #26 stays open until both land and the comparison is end-to-end.

Completed: **#41 — equality as overridable effect** (Andromeda-style;
merged d4c4ceb: `convElab` effect site, `ConvHandler={decide,coreValid}`,
`cacheConvHandler` at 1.04–1.08x, `natArithHandler` as `by arith` tactic);
**#36 — termination checking** (structural recursion for
`red` rules and clause definitions; 10-accepted/8-rejected corpus);
**#32 — clause-style definitions** (MVP + indexed families; `vappend`
elaborates and computes);
**#60 — compiled defunctionalized code pointers** (`compileD`: dfLam compiles
DForm bodies to host closures once; gap 1.9x→~1.4–1.7x, remainder to #72);
**#64 — QTT prototype** (ETT + linear binders, post-elaboration usage checker;
feasibility step for #66);
**#66 — QTT as the core type theory** (quantities in the judgments:
quantity-aware conversion, application-site enforcement, quantity
polymorphism, subject-side checking-mode tracking);
**#80 — constructor disjointness** (`noConfusion`/`noCycle` as named
disequality facts in unification; impossible clauses rejected early).

Then: #33 positivity, #34 error snapshots, #37 records, #38 elaboration
adequacy tests, #28 session-type library demo (the motivating case),
DCP/convexity case (no issue yet — strong second demo).

## Embedding applicability plan

This plan addresses the user-visible gaps tracked in
[`docs/known-limitations.md`](docs/known-limitations.md), including the
runtime bridge, disconnected postulates, separate proof/runtime examples,
Nim interop, and setup friction. The goal is to make checked Eponym code
usable as a Nim library without claiming that Eponym verifies arbitrary host
implementations.

### Design boundary and target

- Eponym checks Eponym declarations, dependent indices, and QTT usage at
  compile time.
- Ordinary Nim types and procedures cross the boundary through generated,
  statically typed adapters/codecs. User-defined objects, references,
  collections, closures, and async results should be supportable when an
  adapter defines their runtime representation. Opaque values may pass
  through Eponym without exposing their structure.
- Nim's compiler checks the adapter's concrete Nim signature. Eponym checks
  callers against the postulated Eponym type. The adapter's behavior remains
  trusted: neither compiler proves that an arbitrary Nim implementation
  obeys a dependent protocol or that a host value satisfies an index.
- No unrecognized Nim code is evaluated as if Eponym checked it. A pure
  expression subset, if adopted, must lower explicitly to Eponym terms.
- QTT usage checking is a static guarantee over Eponym terms. It is not
  automatically a borrow checker for ordinary Nim references or a promise
  of mutation-based code generation.

### Ordered implementation stages

#### A. Specify and freeze the host boundary

- [x] Define an adapter/codec contract for values entering and leaving Eponym
   evaluation. Separate structural codecs (which translate data that
   Eponym inspects) from opaque handles (which Eponym only passes to a
   postulate and receives back). The current opaque mappings are restricted to
   named postulated Eponym types. Structural runtime codecs support
   non-dependent two-field Sigma tuples and named records represented as
   mapped Nim objects. Dependent structures remain future work.
- [x] Specify supported ownership, aliasing, exception, async, and lifetime
   behavior. QTT linearity is limited to checked Eponym terms; boxed Nim refs
   and closures may alias or be retained. Adapters pass values by value, have
   no `var`/`lent` or explicit ownership-transfer form, propagate synchronous
   exceptions, and pass mapped futures through opaquely.
- [x] Keep this contract independent of a particular TCP library. A user or
   library author writes a narrow adapter over `std/net`, `asyncnet`, or
   another backend.

**Exit criteria:**

- [x] The docs distinguish the Eponym guarantee, Nim signature check, codec
  behavior, and trusted host semantics; a reviewer can tell what an opaque
  handle does and does not prove.

#### B. Generalize the runtime call engine and generated ABI

- [x] Build on the `Value`-based evaluator entry points in
   `eponym_embed.nim`; preserve existing `Int` wrappers as compatibility
   shims.
- [x] Add property-based runtime coverage for `Int` and primitive `Nat`
   values crossing the low-level call API; retain a compatibility check for
   the old integer helper and reject negative Nim values for `Nat`.
- [x] Add an opaque boxed-value carrier for arbitrary Nim payload types and a
   typed `T -> T` adapter for a named Eponym postulated type. Property tests
   exercise a user-defined object through an imported checked definition,
   type mismatch rejection, per-call binding isolation, and rejection of
   Eponym conversion over opaque payloads. This is opaque pass-through, not a
   structural codec or generated Nim wrapper.
- [x] Generate fixed-arity Nim `proc` wrappers with concrete Nim `int`
   parameters and results for top-level, non-generic Eponym definitions over
   primitive `Int` and `Nat`. Tests cover runtime calls and reject missing,
   extra, and wrong-kind Nim arguments. `Nat` uses Nim `int` with a checked
   nonnegative conversion.
- [x] Generate typed wrappers for explicitly mapped opaque Eponym postulates
   and indexed type families using `runtimeType(EponymType, NimType)`.
   Mappings are accepted only for named postulated types/families, never
   transparent data definitions. Coverage includes a generated
   `proc(ChannelHandle, string): ChannelHandle` role with 200 property cases.
- [x] Add structural codecs for non-dependent `Sig(A, B)` values as nested
   runtime pairs and Nim two-element tuples. Recursively support primitive
   `Int`/`Nat` and explicitly mapped opaque leaves; 200-case properties cover
   primitive and opaque pair fields. Dependent pairs fail wrapper generation
   rather than losing indices.
- [x] Add structural codecs for non-dependent named `record` declarations as
   mapped Nim objects. Fields encode in declaration order using nested pairs;
   primitive, opaque, and nested non-dependent record fields recurse through
   their codecs. 200-case properties cover mixed `Nat` and opaque fields and
   recursively nested records, while dependent fields fail wrapper generation.
- [x] Add `bindPostulatePair` for typed Nim adapters with one to three
   arguments and a `(B, C)` result, bound to `A1 -> ... -> An -> Sig(B, C)`.
   The macro validates the postulate's argument type heads and non-dependent
   Sigma shape, generates recursive codecs, and lets Nim check the callback
   signature. 200-case properties cover each arity and outer Pi-indexed
   types; named Sigma binders are supported. Compile-fail fixtures reject
   dependent Sigma results and mismatched Nim tuple fields.
- [x] Add the separate `bindPostulatePairTrusted` escape hatch for a
   dependent Sigma result whose fields have runtime codecs. The checked
   Eponym signature is preserved, while matching a host field to its index
   remains explicitly trusted. A 200-case indexed-family property exercises
   this path; the ordinary pair adapter still rejects the same shape.
- [x] Generate typed wrappers for dependent Sigma results only when the
   definition opts in with `runtimePairTrusted(definition)`. The fields use
   their recursive runtime codecs, and the host relationship between values
   and dependent indices remains explicitly trusted. A 200-case indexed
   family property covers the generated wrapper; an unmarked dependent
   signature remains a compile-time error.
- [x] Generate typed host-argument overloads for `runtimeValue(name)` when a
   non-generic definition's parameter types have runtime codecs. Nim checks
   the concrete mapped argument types; the result remains a runtime `Value`,
   and correspondence between mapped host values and dependent indices is
   trusted. Logistic regression exercises indexed matrix/vector inputs.
- [x] Add a `Bool`/Nim `bool` codec backed by the checked `true` and `false`
   constructors from `bool.ep`. Generated wrappers compute checked Bool
   definitions and round-trip both constructor cases in a 200-case property;
   runtime missing-postulate diagnostics recognize data constructors as valid
   results.
- [x] Generate typed wrappers for type-level generic binders `[A: Univ]` when
   the binder is used only in the checked signature. Nim values of generic
   type `A` pass through opaque boxes; runtime computation uses the same
   checked body. A 200-case property covers primitive and user-defined Nim
   values through both the generated wrapper and typed `runtimeValue` helper.
   Add value-indexed Nat binders `[n: Nat]` as Nim `static[int]` generic
   parameters, passed at runtime using the checked Nat constructors. They can
   appear in signatures and runtime bodies; 200-case properties cover typed
   wrappers and typed/raw `runtimeValue` calls. Add Bool-indexed binders
   `[b: Bool]` as Nim `static[bool]`, encoded using checked Bool constructors;
   a 200-case property covers typed wrappers and typed/raw `runtimeValue`
   calls. Other value-indexed binder types and bodies that inspect generic
   type arguments remain unsupported. Add Int-indexed binders `[i: Int]` as
   Nim `static[int]`, encoded with Eponym integer values; a 200-case property
   covers negative and positive indices through typed wrappers and typed/raw
   `runtimeValue` calls. Add value binders over explicitly mapped runtime
   types as Nim static generic values, encoded through the mapped codec. A
   200-case property covers mapped opaque objects and nullary data enum values
   through typed wrappers and typed/raw `runtimeValue` calls. The value must
   be representable as a Nim compile-time constant; other unmapped value
   binders remain unsupported.
- [x] Add a structural codec for nullary, unindexed `data` declarations mapped
   to same-named Nim enum members. The codec translates through checked
   constructor reference identities; a 200-case property covers every variant,
   and a compile-fail fixture rejects constructors with payloads.
- [x] Add an explicit `runtimeVector(Vec)` codec for the canonical
   length-indexed `Vec` family. `Vec[A,n]` maps to `seq[A]`; input lengths and
   each runtime `cons` tail index are checked, and elements recurse through
   their runtime codecs, including nested `Vec` values. A 200-case property
   covers primitive and opaque elements, empty vectors, length mismatches, and
   nested vectors through typed and raw `runtimeValue` interfaces. Preserve
   grouping for nested bracketed type and term applications in the Nim AST
   translator; a nested-vector type exposed a precedence bug in that path.
- [x] Bridge multi-argument Nim closure types to curried Eponym function
   values in both directions. Each argument and result uses the existing
   recursive runtime codecs; 200-case properties cover primitive and explicitly
   mapped opaque arguments for callbacks passed into and returned from checked
   functions. Returned Nim closures require `{.closure.}`.
- [ ] Add explicit runtime type/codec descriptions for exported Eponym
   definitions and extend support to other dependent structures, non-Nat
   value-indexed generics, and other unsupported higher-order definitions.
   Definitions without a matching explicit Nim `proc` declaration still
   retain the legacy `varargs[int]` compatibility wrapper; explicit `proc`
   declarations with unsupported signatures fail clearly when called.
- [x] Validate each currently supported Eponym adapter shape during macro
   expansion and the concrete Nim adapter signature during compilation.
   Unsupported generated wrapper shapes produce a compile-time diagnostic;
   no unchecked cast is used for a signature mismatch. Generic and structural
   codecs remain part of the preceding open item.
- [x] For explicit `proc` declarations with no runtime codec, emit a
   compile-time error template naming the unsupported Eponym result or
   parameter type instead of silently generating a `varargs[int]` wrapper.
   A negative fixture covers a missing opaque mapping. Full structural and
   dependent codecs remain open.
- [x] Keep runtime source re-elaboration outside the per-call path. The Nim
   macro VM's checked `Term`/`Value` objects contain runtime closures and
   cannot be retained directly as executable runtime values; the first call
   therefore re-elaborates, then `eponym_embed` caches terms and globals by
   base directory and source. Subsequent calls use the cache. Property tests
   verify cached globals retain the checked postulate identities.
- [x] Document which runtime forms are genuinely represented (first-order data,
   closures, records, dependent pairs, opaque handles) instead of implying
   that one `Value` escape hatch makes all Nim types callable. The low-level
  bridge now represents primitive Int/Nat, evaluator closures, opaque boxed
  Nim values, non-dependent Sigma tuples, and non-dependent named records;
  `runtimeValue(name)` exposes a checked definition's Value for a host-side
  interpreter, including raw Value arguments with arity checking. It does not
  type-check those raw arguments or generate a Nim data type. Dependent pairs
  still lack general codecs and generated typed wrappers. The remaining
  implementation is tracked in the
   preceding ABI/codec items.

**Exit criteria:**

- [x] Existing integer examples keep working; primitive `Nat` crosses a
  generated statically typed Nim wrapper; wrong Nim argument shapes fail
  compilation; no Eponym proof is weakened. Verified for first-order
  `Int`/`Nat` signatures only; arbitrary codecs and signatures remain open.

#### C. Bind postulates to Nim procedures

- [x] Add explicit `bindPostulate(name, nimProc)` syntax for a declared
   postulate and Nim proc. Generated-wrapper bindings support unary
   `Int -> Int`, unary opaque `T -> T` / `T -> Nat`, mixed
   `Nat -> A -> B`, unary opaque `A -> B`, and curried opaque signatures up
   to five arguments through shape-specific adapters, and arbitrary curried
   signatures through the general codec-based adapter when each type has a
   runtime codec.
- [x] Use an explicit runtime binding environment keyed by
   checked postulate reference identity; do not use a process-global name or
   reference-ID registry. **Foundation complete:** `elabCheckDirState` and
   the runtime cache retain the checked `Globals` table alongside definitions;
   property coverage confirms definition occurrences and cached globals share
   the postulate's reference identity. The runtime evaluator accepts these
   bindings without mutating cached definitions.
- [x] Add a first typed adapter shape, Nim `proc(int): int` to Eponym
   `Int -> Int`; reject mismatched Eponym contracts before invocation. Keep
   the adapter implementation explicitly trusted.
- [x] Add host-callable values to binding-aware runtime evaluation. Property
   coverage checks imported-definition calls, independent per-call binding
   environments, duplicate and wrong-Eponym-type rejection, and 400 generated
   callback inputs.
- [x] Validate the `Int -> Int` Eponym contract during macro expansion and
   the Nim `proc(int): int` signature through generated calls. Compile-fail
   fixtures cover mismatches on each side.
- [x] Report an invoked but unbound runtime postulate by name at the call
   boundary instead of surfacing only a later `ValueError` during result
   conversion.
- [x] Diagnose a binding that no checked proc body references during macro
   expansion. Compile-time call-graph reachability remains open because Nim
   can call each generated wrapper independently; missing runtime bindings
   still fail by name if reached.
- [x] Specify synchronous exception behavior: exceptions raised by a Nim
   adapter propagate unchanged through the checked runtime wrapper; property
   tests verify the original exception type and message.
- [x] Allow an explicitly mapped opaque `Future[T]` as the result of a
   synchronous postulate callback and generated wrapper. The future passes
   through unchanged; Eponym does not await it.
- [x] Specify that mapped `Future[T]` values pass through postulate adapters
  opaquely as arguments or results; Eponym does not await, cancel, observe
  failure, or define async effects. A runtime identity check covers a future
  argument. Keep this distinct from asynchronous effect semantics, which are
  still unsupported.
- [x] Extend the low-level typed adapter from scalar primitives to an opaque
   user-defined Nim value. The handle can cross a checked role and return to
   Nim; representation and behavior are explicitly trusted. Property tests
   cover a user-defined object through an imported definition and 200
   generated object round trips.
- [x] Support a curried two-argument opaque postulate adapter with explicit
   mappings for both Eponym argument types and the result type. A checked
   role dispatches a channel handle and a message string to a Nim callback;
   property tests cover 200 input pairs.
- [x] Support a curried three-argument opaque adapter with explicit Nim type
  checks for all parameters and the result. A generated wrapper and a 200-case
  property test exercise a `Channel -> Message -> RequestId -> Channel`
  postulate.
- [x] Support a curried four-argument opaque adapter with compile-time
  Eponym signature validation and Nim signature checking. Generated wrappers
  and low-level runtime dispatch pass 200 property cases; a negative fixture
  rejects an incorrect fourth-argument mapping.
- [x] Support a curried five-argument opaque adapter with compile-time Eponym
   signature validation and Nim signature checking. A generated checked role
   passes 200 property cases, and a negative fixture rejects a Nim result type
   mismatch.
- [x] Generalize typed `bindPostulate` adapters beyond five arguments. The
   generated adapter decodes each argument and encodes the result through its
   declared runtime codec; a 200-case six-argument property and a negative
   Eponym type mismatch fixture cover the path.
- [x] Bind unary callbacks between distinct opaque mappings (`A -> B`) and
  return a mapped `Future[T]` through an ordinary typed wrapper. Property tests
  verify the future object and its result pass through unchanged; Eponym does
  not await it.
- [x] Accept a Nim closure as an explicitly mapped opaque callback argument to
  a checked role. The generated Nim wrapper checks the closure signature, and
  the bound adapter can invoke it; Eponym treats the closure body as trusted.
- [x] Generate codecs for unary Nim `{.closure.}` proc types at the checked
   wrapper boundary. Nim callbacks enter Eponym as runtime host functions, and
   checked Eponym closures return as callable Nim closures. A 200-case property
   covers each direction, including a captured Nim callback; mismatched Nim
   callback signatures fail compilation.
- [x] Expose unary opaque and binary opaque bindings through `eponymBlock`;
   explicit `runtimeType` mappings connect Eponym postulates to Nim types.
   Nim checks adapter and generated wrapper signatures, and compile-fail
   coverage rejects a mismatched callback type.
- [x] Add mixed primitive/opaque adapters for `opaque -> Nat` and
  `Nat -> A -> B` postulates, including different Nim types for the opaque
  argument and result. The in-memory session passes a Nat payload through a
  checked send/receive pair; the TCP session returns a mapped result value.
- [x] Add a message codec and use an opaque handle to bind protocol operations
   through Nim adapters. The indexed session demo encodes Nat payloads as
   canonical unsigned LEB128 bytes outside Eponym and runs checked sender and
   receiver roles over the channel handle. A separate `std/net` demo uses the
   same codec through a loopback TCP socket; transport libraries stay outside
   the Eponym core.
- [x] Add an explicitly trusted `bindPostulateValue` adapter for host
   operations that must invoke Eponym CPS continuations. The checked borrow
   client uses it to run its `withBorrow`/`readB`/`writeB`/`endB` sequence;
   300 property cases exercise different buffer contents. This low-level form
   checks postulate arity but leaves Value conversion and semantics to Nim.

**Exit criteria:**

- [x] A checked role calls its bound postulate at runtime; the Nim compiler
  rejects a mismatched adapter signature; a negative Eponym role still fails
  during elaboration; the trusted implementation caveat is documented.
  Verified for primitive unary Int and mapped opaque unary/binary adapters.

#### D. Make one end-to-end example use the checked role

- [x] Add a minimal indexed session example whose sender and receiver roles
  call bound Nim channel operations at runtime; property tests exercise 200
  messages.
- [x] Replace the hand-mirrored `runPaxosRound` sequence with calls to the
   checked `proposer` and `acceptor` roles through bound TCP operations.
   Forty property-generated rounds run the two roles in separate processes.
- [x] Provide a `std/net` loopback TCP adapter using the checked sender and
  receiver roles, with message encoding/decoding outside Eponym. The checked
  wrappers return explicitly mapped outcomes.
- [x] Represent transport and serialization failures in explicit Nim result
  values. The loopback integration test checks success, peer closure, and a
  malformed Nat frame through the checked receiver role.
- [x] Make the buffer/borrow example route through bound postulates, and label
   what the linear checker establishes versus what the Nim buffer adapter
   must uphold. The adapter scopes the runtime borrow in `try/finally`; Nim
   aliases held elsewhere remain outside the Eponym guarantee.
- [x] Exercise correct runtime session execution and compile-time failures for
  wrong message order, wrong indexed value, double use, and dropped linear
  handles. The error snapshots cover the negative cases; the TCP loopback test
  exercises the positive checked sender/receiver roles.

**Exit criteria:**

- [x] The running demos execute the same checked roles that compile-time
  negative examples constrain; there is no second manually maintained
  protocol sequence. The borrow property test invokes generated
  `borrowClient(Buffer)` and checks only the borrowed head cell changes.

#### E. Connect certified models to numeric execution

- [x] Choose runtime interpretation for both DCP examples.
   `runtimeValue(name)` exposes each checked definition's runtime Value; the
   Nim interpreters evaluate the relevant CExpr/VExpr constructors.
- [x] Pass the exact Eponym objectives to ternary search and logistic
   gradient descent. A 300-case scalar property and a 200-case vector
   differential property cover evaluated outputs; the certificates are
   checked during elaboration.
- [x] Document trusted assumptions: the interpreters, raw runtime argument
   construction, numeric precision, finite-difference error, optimizers, and
   convexity reasoning remain host/math assumptions.
- [x] Connect logistic regression's checked objective to the executed loss
   and gradient. Matrix and label data enter as the same explicit mapped
   values represented in the checked `lrProb` expression; its gradient is
   estimated from that objective, not separately restated.

**Exit criteria:**

- [x] A mutation to the checked objectives changes the runtime functions or
  causes generation/validation to fail; the solvers cannot silently optimize
  different expressions. The vector property checks a separately certified
  objective shifted by five.

#### F. Evaluate QTT-guided code generation

- [x] Keep usage checking as the correctness feature, independently of any
  optimization. No code-generation optimizer is wired into acceptance; the
  QTT usage property suite passes independently.
- [ ] Prototype destination-passing or slot reuse for a narrow first-order
   expression language where liveness and aliasing are explicit.
- [ ] Generate mutation only when the representation and ownership analysis
   prove it safe. Linear use alone does not make an arbitrary Nim object
   uniquely owned.
- [ ] Compare output behavior and allocations against an immutable baseline;
   report when the backend cannot optimize a term.

**Exit criteria:**

- [ ] The optimization has differential correctness coverage, does not
  change QTT acceptance, and has measured benefit on a documented workload.
  Do not market QTT as code-generation optimization until this lands.

#### G. Improve the Nim surface and onboarding

- [x] Keep the current supported AST boundary explicit in the syntax reference,
  tutorial, trust model, and known-limitations page.
- [x] Lower Nim `Int` expressions using `let`, unary minus, and `+`, `-`, `*`
  to the existing checked Eponym primitives. A 200-case property test compares
  generated wrappers with Nim arithmetic over values that avoid overflow.
- [x] Lower a single-condition `if/else` expression through the polymorphic
  `ifThenElse` definition in `lib/bool.ep`; both branches remain Eponym terms
  and Bool eliminator computation selects the result.
- [x] Lower chained `elif` expressions to nested checked `ifThenElse` calls;
  test a multi-branch embedded definition and a missing-`else` compile error.
  Effects, arbitrary procedure calls, macros, mutation, and IO remain outside
  unless introduced as explicit trusted bindings.
- [x] Use square brackets for explicit Eponym binders (`A`, indices such as
  `n`), parentheses for term arguments, and braces for implicit binders.
  Generic declarations, bracketed type applications, and bracketed term
  applications are covered; call-style forms remain supported for migration.
- [x] Resolve relative `.ep` imports source-relative first, then from the
  installed package's `lib/` directory. Absolute paths remain explicit
  overrides; a prelude-resolution test checks nested imports without vendoring.
- [x] Verify the resolution contract against a clean package-shaped install
  from a separate working directory; document the path order and absolute
  override behavior. The smoke script also compiles and runs the tutorial's
  first checked example and compiles its generic vector example from a clean
  Nim project directory.
- [ ] Revisit the first-use time estimate after installation and editor setup
   are streamlined.

**Exit criteria:**

- [ ] Examples use the documented Nim-friendly syntax; the tutorial runs
  from a clean Nim project using the published package; `.ep` resolution
  works from a different working directory without hidden global state.

### Cross-stage validation and project claims

- [x] Add positive property coverage for each supported codec/callback shape,
  plus compile-fail cases for type mismatch, missing and duplicate bindings,
  unsupported operators, dependent-index mismatch, and linear misuse.
- [x] Add runtime integration examples that execute the exact Eponym-checked
  definition, not a mirrored Nim implementation. The in-memory and TCP session
  examples run their checked sender/receiver roles, Paxos runs its checked
  proposer and acceptor, and the borrow example runs `borrowClient` through
  bound postulates. The raw borrow adapters remain trusted.
- [x] Classify the TCP/in-memory session, Paxos, borrow, and optimizer
  examples by what Eponym checks, what Nim checks, and what remains trusted
  or disconnected. The README links to the table; retain it as implementations
  change and qualify claims when the implementation does not meet them.
- [x] Update `docs/known-limitations.md`, the trust model, the tutorial, syntax
  reference, and this plan alongside the surface-syntax stage.
- [x] Preserve a supported-claims table in the docs: “checked by Eponym”,
  “checked by Nim”, “trusted adapter”, and “not currently connected”.

### Dependencies and sequencing

The runtime ABI (B) precedes callable postulates (C); postulates precede the
end-to-end protocol (D). The optimizer connection (E) can proceed after the
runtime evaluator is general enough to interpret or compile a reified
objective. QTT code generation (F) is independent of protocol bindings but
depends on a runtime representation with explicit ownership/liveness.
Surface syntax and package onboarding (G) can proceed alongside A–C, but must
not imply that unsupported host Nim is executable inside `eponymBlock`.

## Building

Requires Nim 2.x (built with 2.2.12 via choosenim):

```sh
export PATH=$HOME/.nimble/bin:$PATH
```

Full local CI matrix before merging to main (mirrors
`.github/workflows/ci.yml`): build and run `eponym`, `eponym_init`,
`preterm`, `parse_surf`, `mac_surf`, `elab`, `eponym_mac`, `egraph`,
`eponym_embed`, plus `tests/run_examples.nim`. `lsp.nim` is built but not
executed (it's a server loop, not a test). Keep the build warning-clean.

## References

- `plan.org` — experiment plan and research questions
- `decisions.org` — decision log (what worked, what didn't, and why)
- `research.org` — the motivating question
- `docs/layers.md` — layer dependency contract
- `docs/staging-*.md`, `docs/pipeline-architecture.org` — Track C design
- Shared zettelkasten: https://github.com/raven6941/notes
