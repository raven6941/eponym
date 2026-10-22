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
checked proposer and acceptor through bound TCP adapters. The single-variable
DCP example interprets its checked objective at runtime; the borrow and vector
logistic examples still have separate runtime implementations. The embedding
applicability plan tracks remaining gaps. Deliberate-embedding prior art:
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
wrappers support first-order `Int`/`Nat`, explicitly mapped opaque postulated
types, and local clause-style definitions whose checked signatures can be
reconstructed; unsupported signatures produce a compile-time diagnostic. The
first runtime call re-elaborates the block
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
| 240/241 | Profile and cache arithmetic evidence | The Nat lemma corpus has two evidence checks and no repeated goal shapes or proof pairs; normalization/build costs are negligible beside bare-core checking, so a cache has no measured hit opportunity |
| 242 | Price arithmetic evidence validation | Evidence path averages 3.81 s vs 63 ms for trusted-only `natConv` (~60x); the faster path incurs two trusted discharges and skips bare-core evidence validation |
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
**#240 — arithmetic evidence profiling** (`tools/profile_nat_arith.nim`):
three runs of `lib/nat_lemmas.ep` took 3.87 s each. The evidence-path spans
attribute 1.945 s (99.8% of those spans, about 50.2% of total elaboration) to
the bare-core evidence check, 3.2 ms to `normEvArith`, and 0.2 ms to evidence
construction. The next target is the cost of rechecking synthesized evidence;
proof-normalization caching is not supported by these measurements.

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
- [x] Record the v1 boundary for Float/String/Char operations: keep values
  opaque in the core and use typed postulates plus checked Nim adapters;
  document the representation and trust rationale in the syntax reference
  and known limitations.
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

### QTT branch-sensitive usage

- [x] Add a usage profile over zero, one, and many uses. Sequential
   composition saturates at many; alternative composition retains the set of
   possible path counts. Use the same profile predicate for the in-judgment
   check and post-elaboration backstop. `tests/pbt_usage.nim` property-tests
   sequential composition and quantity acceptance, compares generated nested
   choice/sequential trees with an independent concrete-path enumerator, and
   checks balanced versus inconsistent branch joins.
- [x] Make usage checking path-sensitive for Nim `if` expressions and
   finite and first-order recursive eliminators. The analysis unfolds checked
   definitions and derives alternatives from complete data-generated rules;
   each case template must apply its method to exactly the constructor fields
   and verified direct recursive hypotheses. For unindexed recursive data, a
   least fixed point over saturated usage profiles accounts for every finite
   recursive shape and all direct recursive fields when the result motive is
   ground (so recursive hypotheses cannot defer captured uses in closures).
   Indexed families, higher-order recursive fields, closure-valued motives,
   and unrecognized templates stay conservative. In-judgment checks, the
   post-elaboration backstop, and
   codegen erasure share the analyzer; `kernel_audit` independently checks
   registered rules. A 200-case Option property checks payload paths, a
   200-case List property checks strict nil-case evaluation at lengths 0–20, and
   compile-time regressions cover three-case and recursive data. Negative
   cases reject drops and duplicates. Usage profile properties, erasure, and
   the kernel audit pass.
- [ ] Extend path-sensitive usage to indexed recursive families,
   higher-order recursive fields, and user-written case templates that
   compute with branch values rather than following generated data rules.
   These forms currently keep conservative sequential counting. Add generated
   compile-time regressions for each newly supported eliminator shape. Do not
   infer q1 until every runtime path is accounted for.
- [ ] Decide quantity subsumption for q1 under Pi domains before enabling q1
   inference. The rule must respect contravariance and pass both elaborator and
   independent kernel checks; the existing inferred-q0-to-qOmega exception
   does not establish a general quantity subtyping rule.

### Ordered implementation stages

#### A. Specify and freeze the host boundary

- [x] Define an adapter/codec contract for values entering and leaving Eponym
   evaluation. Separate structural codecs (which translate data that
   Eponym inspects) from opaque handles (which Eponym only passes to a
   postulate and receives back). The current opaque mappings are restricted to
   named postulated Eponym types. Structural runtime codecs support primitive
   values, Bool and nullary enums, opaque mapped types, standard `List` and
   `Option` values, indexed `Vec` sequences, two-field Sigma tuples, and named records
   represented as mapped Nim objects. Dependent records and pairs have
   explicit trusted opt-ins; the remaining dependent runtime forms stay open
   under stage B.
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
   be representable as a Nim compile-time constant; unmapped values are
   available through dynamic `Value` wrappers when their Eponym type is named.
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
- [x] Add `runtimeRecordTrusted(Record)` for mapped records with dependent
   fields. Earlier field names are substituted into later codecs; supported
   codecs still check constraints they represent (for example, a Vec field
   against its preceding Nat length). A 200-case property covers typed and raw
   runtime wrappers and rejects mismatched sequence lengths.
- [x] Automatically validate generic dependent record binders when earlier
   fields are Nat and each dependent use is checked by a structural codec.
   Typed and raw-result wrappers reject mismatched Vec lengths. Other dependent
   record shapes still require `runtimeRecordTrusted(Record)`.
- [x] Add `runtimeList(List)` for the standard unindexed `List[A]` family.
   It maps recursively codec-supported elements to `seq[A]` and validates
   `nil`/`cons` constructor identities and application spines. A 200-case
   property covers primitive and opaque elements, empty lists, and typed/raw
   `runtimeValue` paths.
- [x] Add `runtimeOption(Option)` for a unary Option family with canonical
   `none` and `some` constructors. It maps `Option[A]` to `std/options.Option[A]`
   and recursively encodes the payload. A 200-case property covers `none`,
   `some`, primitive and opaque generic payloads, nested options, and typed/raw
   `runtimeValue` paths.
- [x] Preserve concrete element type witnesses in runtime `Vec`, `List`, and
   `Option` constructor values, including recursively nested collection types.
   The witness builder lowers nested Vec lengths to runtime Nat values and
   resolves generic element types through unique `runtimeType` mappings for an
   unindexed Eponym type and its concrete Nim type. Mapped opaque boxes retain
   that Eponym type witness so runtime inference can validate constructor
   arguments; generated generic wrappers also pass the mapped type as the
   checked body's type argument. 200-case properties validate mapped
   `Vec[A,n]` values, reject an incorrect element type, and cover mapped
   callback results through `vmap`, in addition to primitive Vecs including
   the empty case and nested collection round trips.
- [x] Add `runtimeCodec(EponymType, NimType, encoder, decoder)` for explicitly
   mapped named Eponym types and families. The typed encoder and decoder
   receive the module's `Globals`; generated wrappers and typed postulate
   bindings call them, so Nim checks the concrete procedure signatures. A
   200-case property maps a payload-bearing `Tree` family to `seq[int]`, tests
   typed and raw `runtimeValue` paths, and invokes a Nim implementation through
   a checked `Tree -> Tree` postulate. A compile-fail fixture rejects a Nim
   encoder with the wrong signature. Index relationships remain the codec
   author's responsibility.
- [x] Permit `runtimeValue(importedDefinition)` when a checked definition
   comes from an imported `.ep` module and has no local Nim `proc` declaration.
   It exposes a raw `openArray[Value] -> (Value, Globals)` wrapper and
   reconstructs typed wrappers for supported imported Pi signatures, including
   type-level `Univ` binders and non-dependent callback arrows. A 200-case
   property covers an imported polymorphic identity with `int` and a mapped
   Nim object through direct, typed `RuntimeValue`, and explicit raw calls; a
   second property maps `List[ChannelHandle]` through an imported `List.map`
   using a Nim closure and checks the mapped result. Imported callbacks can
   also use codec-supported argument and result types indexed by earlier outer
   parameters: a 200-case property passes an indexed `Vec` through a callback
   and checks that the length is enforced. This also covers erased Eponym
   indices that the host codec needs to encode the value. A second 200-case
   property supports callback-local dependencies: an imported callback takes
   and returns `Vec[Int, length]`, and rejects wrong-length callback inputs and
   outputs. Other dependent callback shapes still need supported Nim codecs.
   Other properties call an imported checked identity and dispatch an
   imported postulate to a bound Nim implementation; a negative runtime check
   rejects mismatched raw arity.
   Directory-aware runtime state retains imported bodies, and a checked-term
   reference scan lets bindings used only by imported bodies pass unused-
   binding validation.
- [x] Bridge multi-argument Nim closure types to curried Eponym function
   values in both directions. Each argument and result uses the existing
   recursive runtime codecs; 200-case properties cover primitive and explicitly
   mapped opaque arguments for callbacks passed into and returned from checked
   functions. Noncapturing Nim callbacks using the default `nimcall` convention
   are also accepted as inputs. Eponym callbacks returned to Nim still require
   `{.closure.}` because they may capture runtime state. Properties cover both
   callback input conventions; a compile-fail fixture checks the result rule.
- [x] Let Nim infer a mapped generic host type from a non-callback value
  argument when a callback also mentions that type, including through a
  mapped `Vec[A, 2]` represented as `seq[A]`. The generated wrapper defers the
  callback parameter's Nim type inference; its body still checks the
  callback's concrete argument and result types. A 200-case property covers
  generated and typed `RuntimeValue` wrappers for direct generic values and
  `vmap` over a Vec whose generic type is inferred from the later value
  argument. Negative fixtures reject incompatible callback signatures in both
  forms; the vector property also rejects wrong lengths through both wrappers.
- [x] Preserve Nim default parameter values on generated typed wrappers and
   typed `RuntimeValue` overloads. Compile-time and runtime regressions cover
   omitted defaults, positional overrides, and named overrides.
- [x] Lower named arguments in checked local and imported procedure calls to
   their declared binder order. Separate 200-case properties check reordered
   calls to each; unknown, duplicate, and missing required arguments receive
   compile-time errors.
- [x] Apply Nim defaults when checked local procedure calls omit positional
   trailing arguments or skip defaulted arguments with named calls. A 200-case
   property covers both forms; missing required arguments remain compile-time
   errors.
- [x] Reorder named arguments for Nim callback parameters from their declared
   `proc` type. A 200-case property covers both generated and typed
   `RuntimeValue` wrappers for a two-argument callback.
- [x] Preserve callable signature metadata through simple local `let` aliases
   of known procedures and Nim callback parameters. A 200-case property checks
   callback and local procedure aliases through generated wrappers; the callback
   property also covers typed `RuntimeValue` calls.
- [x] Generate typed dynamic wrappers for generic value binders whose domain
   is an indexed `Vec` with an existing runtime codec. The wrapper accepts the
   corresponding Nim `seq`, encodes it against the earlier generic indices,
   and rejects a sequence with the wrong length. A 200-case property exercises
   both the typed dynamic wrapper and `RuntimeValue` dynamic wrapper, including
   wrong-length rejection.
- [x] Generate typed dynamic wrappers for generic value binders whose domain
   is a non-dependent Sigma with codec-supported fields. Nested field codecs
   are composed, and indexed Vec fields are length-checked. A 200-case
   property exercises typed and `RuntimeValue` dynamic wrappers and rejects a
   Sigma containing a Vec of the wrong length.
- [x] Generate typed dynamic wrappers for generic value binders whose domain
   is `List[A]` or `Option[A]` when the matching runtime codec is registered.
   Recursive element codecs are reused; 200-case properties cover typed and
   `RuntimeValue` dynamic wrappers for `List[Int]` and `Option[Int]`.
- [x] Support raw `RuntimeValue` and typed Nim tuple dynamic wrappers for
   dependent Sigma generic binders. Raw values remain accepted and are
   checked against the generated witness. When field codecs can reconstruct
   that witness, an additional typed overload encodes and validates the tuple
   without `runtimePairTrusted`; the raw overload remains available. 200-case
   properties cover `Sig(length: Nat, Vec[Int, length])` and reject
   mismatched indices.
- [x] Accept unmapped named Eponym values as `Value` arguments in dynamic
  generic wrappers. Validate that each value inhabits its declared named type
  before checked evaluation. A 200-case property passes an unmapped data
  constructor through a generic projection; applied/indexed binder domains
  still need runtime type-expression validation. Generated signatures use the
  public `RuntimeValue` and `RuntimeValueResult` aliases from `eponym_embed`.
- [x] Add a low-level `RuntimeVariant` representation for data-family values.
  It preserves constructor identity and raw argument Values, checking family
  membership, constructor arity, and runtime spine shape. A 200-case property
  round-trips generated nested trees; negative checks reject wrong arity and
  constructors from another family.
- [x] Let `runtimeVariant(Family)` generate typed wrappers that use the
  structural representation for payload-bearing and indexed constructors.
  A 200-case property covers direct and generated wrapper round trips; typed
  recursive payload codecs remain future work.
- [x] Validate `RuntimeVariant` payloads against the selected constructor's
  checked Pi telescope when encoding. Earlier arguments are substituted into
  later dependent domains, so an indexed payload such as `Vec[Int, length]`
  must match its preceding Nat field. Reject primitive Int/Nat values used at
  unrelated Eponym types. A 200-case property covers dependent vector payloads
  and negative checks reject wrong field types and lengths. Raw variant
  extraction still exposes fields as `Value`s for caller-directed decoding.
- [x] Make raw runtime type validation check constructor arguments recursively
  against their checked Pi domains. This prevents untyped primitive Int/Nat
  terms from being accepted inside an otherwise well-formed constructor
  application. A 200-case property rejects malformed raw constructor values,
  including when they enter a dynamic generic wrapper.
- [x] Validate dynamic generic `Value` arguments against applied type
  expressions built from named types, earlier generic indices, applications,
  integer literals, and direct Bool-controlled conditional Nat indices. A
  200-case property checks raw and mapped `SizedTree[length]` values, plus both
  branches of `SizedTree[if b: n else: m]`, and rejects mismatched embedded
  indices. More complex type expressions remain unsupported.
- [x] Lower conditional Nat indices of the form `if b: n else: m` in dynamic
   generic Vec and non-dependent Sigma value codecs. The Bool condition is a
   generic runtime parameter; both branch lengths are checked. A 200-case
   property covers typed and `RuntimeValue` wrappers and wrong-length values.
- [x] Extend conditional Nat indices to Bool conditions composed with `and`,
   `or`, and `not`. Lower these through Nim's Boolean expression semantics for
   runtime codec checks and through the checked Bool definitions for Eponym
   elaboration. A 200-case property covers typed and `RuntimeValue` dynamic
   wrappers; invalid lengths are rejected for every Bool input combination.
- [x] Expose low-level runtime Pi and Sigma type builders for host-side checks,
   including dependent codomains. Reserve fresh IDs beyond checked globals and
   earlier binders; validate pair values recursively against dependent Sigma
   fields. A 200-case property checks non-dependent and dependent pairs, rejects
   mismatched fields and indices, and validates checked functions against both
   non-dependent and dependent Pi witnesses.
- [x] Expose `runtimeValueTypeOf(value, globals)` to infer an Eponym type
   witness for a runtime `Value`. Reserve fresh IDs past checked globals and
   property-test primitive values; validate a checked function against its
   inferred witness.
- [x] Property-test generated type-expression witnesses for named Pi binders
   in raw dynamic generic validation. A 200-case property accepts a checked
   `Token -> Token` identity and rejects a value with the wrong function type.
- [x] Add property coverage for generated runtime type-expression witnesses
   over nested and dependent Sigma domains, especially when their codomains
   refer to earlier generic values. Two 200-case properties validate nested
   pairs and `Sig(length: Nat, Vec[Int, length])`; malformed Nat fields and
   mismatched vector indices are rejected.
- [x] Let generic `Type 0` parameters use unique `runtimeCodec` mappings for
   unindexed Eponym types. Generated generic container and callback codecs use
   the mapped encoder/decoder and preserve the concrete type witness; a
   200-case property checks `vmap` over custom-coded `Tree` values and rejects
   a vector with the wrong length.
- [x] Validate custom-codec values passed to dynamic generic binders over
   applied data families against the full runtime type expression. A 200-case
   property checks `SizedTree[length]` values through typed and raw-result
   wrappers and rejects an encoded index that differs from the supplied Nat.
- [x] Generate codec-backed typed overloads for dynamic generic dependent
   Sigma binders without `runtimePairTrusted` when the generated Sigma witness
   can validate the encoded value. Preserve the raw `RuntimeValue` overload.
   A 200-case property covers typed and raw-result wrappers for
   `Sig(length: Nat, Vec[Int, length])` and rejects an encoded vector with a
   mismatched length.
- [x] Automatically allow dependent Sigma codecs when each dependent index
   occurrence lies in a structural codec that validates the corresponding
   host value. A 200-case nested-Vec property checks constraints at both levels;
   unsupported dependencies continue to require the explicit trust opt-in.
- [x] Support the explicit `runtimePairTrusted` opt-in for generic dependent
   Sigma binders when the available codecs cannot reconstruct the full witness.
   Typed and raw-result overloads still apply field codecs, and a 200-case
   property rejects a Vec field whose length disagrees with the Nat field.
- [x] Generate typed dynamic overloads for generic value binders whose domain
   is an Eponym Pi type with recursively supported Nim codecs. Reconstruct a
   Nim `{.closure.}` signature from the Pi binders, preserve the raw
   `RuntimeValue` overload, and validate the host callback against its Pi
   witness. 200-case unary and multi-argument properties cover typed and
   raw-result wrappers; compile-time checks reject mismatched callback
   signatures. A further 200-case dependent Pi property covers a callback
   taking `Nat` and `Vec[Int, length]` and returning `Vec[Int, length]`;
   typed and raw-result wrappers preserve the index, and malformed input or
   output lengths are rejected. A separate 200-case property passes a mapped
   Nim `ChannelHandle` object through a generic Pi callback using the explicit
   `runtimeType` mapping, through both typed and raw-result wrappers. Another
   property covers a callback whose Vec index is computed as
   `add(left, right)`, with negative checks for mismatched input and output
   lengths. A further 200-case property covers `SizedTree[length]` through a
   custom `runtimeCodec` in a generic Pi callback, including rejection of
   malformed input and output indices. A 200-case property passes a Nim
   closure as a callback argument to another generic Pi callback through typed
   and raw-result wrappers, and returns the remaining Pi as a Nim closure;
   compile-time coverage rejects mismatched nested closure signatures.
   The generic Pi wrapper also infers the Nim callback type, allowing both
   calling conventions while checking each use against the Pi signature;
   compile checks reject mismatches and a 200-case property covers both
   conventions.
- [ ] Add explicit runtime type/codec descriptions for exported Eponym
   definitions and extend support to remaining dependent structures,
   unmapped value-indexed generics, and unsupported higher-order definitions.
   Current support includes checked Nim wrappers for supported generic
   definitions, `runtimeValue` access to checked results, callback values with
   recursive codecs, standard `Vec`, `List`, and `Option` codecs, custom
   `runtimeCodec` mappings, and explicit trusted opt-ins for dependent records
   and ordinary pair wrappers. Remaining gaps include dependent structures
   without a supported runtime type witness; dependent Sigma binders whose
   fields lack codecs or whose encoded values cannot be checked against a
   generated witness; broader automatic codec coverage, additional dependent
   forms, and higher-order signatures whose Pi domains or codomains lack
   runtime codecs. Unsupported
   cases must continue to fail with a precise compile-time diagnostic.
   Imported signatures outside the current Pi reconstruction grammar still
   need a raw `Value` wrapper; callback-local dependent signatures outside
   the supported Nim codec grammar and explicit local `proc` declarations
   with unsupported signatures fail clearly when called.
- [x] Provide importable opaque `Float`, `String`, and `Char` types, each
   mapped through `runtimeType` to Nim `float64`, `string`, or `char`. A
   200-case property for each scalar passes through a checked wrapper and a
   bound Nim postulate. Eponym checks type flow and signatures; it does not
   supply scalar literals, arithmetic, string operations, or equality, whose
   behavior remains in trusted Nim adapters.
- [x] Document the typed API for runtime-valued Nat indices (`#335`):
   `runtimeValue(definition)` exposes `definitionDynamic(index, value)` when
   the signature has codecs, while the ordinary generic wrapper retains its
   `static[int]` index. The installed-package tutorial smoke test passes a
   runtime length and verifies that a mismatched Vec length is rejected; the
   runtime bridge property suite already covers 200 valid and negative cases.
- [x] Reconstruct typed wrappers for local clause-style definitions from
   their checked Pi signatures. Two 200-case properties cover direct calls
   and typed and raw `RuntimeValue` access for a `Nat -> Nat` identity and a
   recursive two-argument `Nat -> Nat -> Nat` addition definition. Restrict
   the generated wrapper to signatures with supported runtime codecs; an
   unsupported result type gets a compile-time diagnostic.
- [x] Validate each currently supported Eponym adapter shape during macro
   expansion and the concrete Nim adapter signature during compilation.
   Unsupported generated wrapper shapes produce a compile-time diagnostic;
   no unchecked cast is used for a signature mismatch. Generic and structural
   codecs remain part of the preceding open item.
- [x] For explicit `proc` declarations with no runtime codec, and definitions
   whose checked signatures cannot be reconstructed, emit a compile-time
   diagnostic instead of silently generating a `varargs[int]` wrapper.
   Negative fixtures cover a missing opaque mapping and an unsupported local
   clause result type. Full structural and dependent codecs remain open.
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
- [x] Settle the postulate-binding visibility policy: one block-level binding
   is reviewed beside its postulate and applies throughout that block,
   including imported definitions. Call sites and generated checked-wrapper
   signatures do not repeat or encode the host implementation because it is
   trusted input, not evidence checked by Eponym (#337).
- [x] Add an explicit `bindPostulateMutable` adapter for Nim procedures with
   `var` parameters. It decodes checked arguments to mutable locals and encodes
   the returned value, preserving copy-in/result-out semantics; caller-visible
   mutation and ownership transfer remain outside the checked Eponym model.
   A 200-case property exercises mutation, read-only value access, and the
   returned checked value. `docs/known-limitations.md` records the trust and
   ownership boundary.

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

- [ ] Keep usage checking as the correctness feature, independently of any
   optimization.
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
- [x] Audit the VS Code extension against bracketed Eponym syntax. It delegates
  parsing/checking to the Nim macro and Eponym LSP, contributes no Eponym
  grammar or snippets, and already pairs square brackets. The headless smoke
  test compiles a bracketed-generic `shedsBlock` and exercises its sidecar
  through the real LSP; no extension version bump is needed because its UI and
  protocol did not change.
- [x] Resolve the compiled LSP binary from the nearest repository root when
  the extension is opened from a nested workspace; retain the documented
  workspace-root fallback outside the checkout and cover both paths in smoke
  tests.
- [x] Give shed holes an in-process semantic model: retain the typed hole
  metavariable, zonked goal terms, structured binder contexts and Pi-spine
  binders with QTT metadata. Migrate LSP hover to consume that model. Keep the
  sidecar's rendered text as a presentation projection; a future cross-process
  semantic format needs a versioned structural term codec.
- [x] Let Nim shed case-splitting replay parameters and construct an
  index-generalized eliminator motive for indexed datatype families. Round-trip
  tests cover `List[Nat]`, generic `List[A]`, index-independent and
  index-dependent `Vec` goals, and a family whose index domain depends on a
  type parameter. Exact occurrences of compound index expressions are
  abstracted as a unit, with the generated eliminator validated by re-elaboration.
- [x] Lower single and chained `if/elif/else` expressions through the checked
  `ifThenElse` definition in `lib/bool.ep`. Branches are unit thunks, so only
  the chosen branch runs, matching Nim conditional evaluation even when a
  branch calls a bound postulate. A 200-case property checks effect counts and
  results; a compile-fail test covers a missing `else`. Arbitrary Nim control
  flow, macros, mutation, and IO remain outside unless explicitly bound.
- [x] Emit Nim's integer literal `1` as unambiguous Eponym `01`, preserving
  expected-type selection between `Int` and `Nat`. A 200-case `x + 1` property
  and surface-conformance fixture cover the behavior.
- [x] Use Nim integer literals for Nat indices and explicit Nat arguments in
  `eponymBlock` examples. The tutorial now uses `Vec[Nat, 2]` and
  `cons[Nat, 1](...)`; explicit bracket conversion consults the Eponym
  application telescope so `Int` binder literals retain their meaning.
  `tests/test_embedded_explicit_params.nim` covers imported constructors and
  procedures, a local generic, a local indexed family, and an `Int` binder.
  `tests/test_embedded_error_path.nim` requires a two-element vector declared
  with length one to fail. The installed-package tutorial smoke test passes.
- [x] Add an explicit `natToInt : Nat -> Int` in
   `lib/nat_to_int.ep`, importing the canonical `Nat` and primitive `Int`
   definitions. A 200-case generated-wrapper property passes the converted
   value through a bound Int postulate and checks that negative host values
   are rejected as `Nat`. The runtime conversion is limited by Nim `int`
   range and the interpreter's recursive evaluation depth.
   Keep conversion explicit: a postulate may hide host effects that its
   Eponym type does not prove absent. A compile-fail fixture pins the
   no-implicit-coercion policy.
- [x] Use square brackets for explicit Eponym binders (`A`, indices such as
   `n`), parentheses for term arguments, and braces for implicit binders.
   Generic declarations, bracketed type applications, and bracketed term
   applications are covered; recognized call-style explicit applications now
   fail with a migration diagnostic. Local Nat `let` aliases and conditional
   Nat index expressions are recognized too, with compile-fail regression
   fixtures. Direct callback parameters with explicit Pi type binders now use
   the same syntax check. Returned function aliases, callback aliases, and
   other function-valued paths still need a complete rejection audit before
   release.
- [x] Resolve relative `.ep` imports source-relative first, then from the
  installed package's `lib/` directory. Absolute paths remain explicit
  overrides; a prelude-resolution test checks nested imports without vendoring.
- [x] Verify the resolution contract against a clean package-shaped install
  from a separate working directory; document the path order and absolute
  override behavior.
- [x] Verify the resolution contract against a clean installed package from a
  separate working directory; document the path order and absolute override
  behavior. `tests/test_package_prelude_install.sh` mirrors the flat installed
  module layout from `installFiles`; an isolated Nimble install compiled the
  tutorial and ran the installed-prelude runtime example.
- [x] Map parse and elaboration diagnostics for local `eponymBlock`s back to
  the nearest Nim definition-body expression. A compile-fail fixture verifies
  the reported file and line. Imported `.ep` diagnostics retain their source
  path, line, and column (issue #347).
- [x] Add a type-preserving `debugEcho[A](value)` postulate in `lib/debug.ep`
  with an explicit `bindPostulateValue` runtime adapter. A 200-case property
  verifies the checked call returns each value and invokes the trace adapter
  exactly once. The adapter is trusted Nim IO and is not run during checking.
- [x] Preserve source positions through imported `.ep` modules so diagnostics
  can report the original imported-file location. `Loc` now carries its source
  path, the file loader attaches it during parsing, and `tests/test_imported_source_locations.nim`
  checks both elaboration and parse errors in an imported module.
- [x] Revisit the first-use time estimate after installation and editor setup
   are streamlined. The README and tutorial now make clear that the ~15-minute
   path assumes Nim and Nimble are already installed. Eponym's Nimble metadata
   no longer makes the test-only, unindexed Falsify package an install
   dependency; CI installs Falsify separately. `tests/test_package_prelude_install.sh`
   checks the published requirements and installs Eponym into an isolated
   Nimble directory before compiling tutorial snippets from a separate project.

**Exit criteria:**

- [x] Compile the marked hello and vector snippets extracted directly from
  `docs/tutorial.md` against a clean package-shaped install, and resolve `.ep`
  imports from a different working directory; `tests/test_package_prelude_install.sh`
  verifies these paths without hidden global state.
- [x] Verify `nimble install` in an isolated `NIMBLE_DIR` with an empty package
  index and no third-party install requirements, then compile tutorial
  snippets and installed-prelude examples from a separate clean Nim project.
- [x] Revisit the first-use estimate after installation and editor setup are
   streamlined; the install dependency and tutorial timing assumptions are now
   documented and checked as described above.

#### H. Generate runtime code from checked definitions

- [x] **Phase 0 (#328):** add a core pass that removes computation supplied
  to quantity-0 applications. The current Value evaluator retains the
  function binder/application slot, so erased arguments become inert unit
  witnesses; a 200-case `falsify` property compares results and confirms that
  effectful q0 arguments are skipped. Full local CI passed for this phase.
- [x] Reserve erasure's fresh neutral IDs above references reachable through
  checked terms and cached eliminator rules. A regression reproduces the
  constructor-ID collision as an out-of-bounds reduction without the fix.
  (#387)
- [x] **Phase 1 (#329):** compile supported erased definitions to Nim AST that
  constructs and operates on runtime `Value`s directly. Per-definition
  fallback to the interpreter for unsupported forms; the typed-wrapper
  calling convention is unchanged; generated procs carry user source
  positions. Pinned by a differential suite vs the interpreter
  (`tests/test_codegen_phase1.nim`, in the CI matrix): first-order Int
  defs, pairs, higher-order/partial application, Nat/Bool eliminators,
  stuck eliminators over neutral scrutinees, effect counting (no
  duplicated/dropped postulate effects), and source-mapped errors.
  Full local CI passed for this phase.
- [x] Omit q0 binders from generated typed-wrapper and Phase-1 compiled-proc
  computational argument vectors. A separate q0 witness vector carries
  checked values only to instantiate dependent runtime types; these witnesses
  do not enter computation. Property coverage checks dependent Vec arguments
  and results through both typed and raw runtime-value wrappers.
- [x] Omit q0 formals and local-call arguments in the scalar representation
  backend. A differential test covers inferred and explicit q0 binders,
  leading and interleaved q0 positions, and the typed wrapper checks 200
  generated values for both layouts.
- [x] Give generated q0 lambdas a nullary `Value` closure representation.
  Generated higher-order code keeps a placeholder only in its compile-time
  de Bruijn environment; it emits no host parameter or closure application
  slot. The interpreter remains unary. A differential test passes a generated
  q0 closure through a higher-order postulate and verifies a q0 argument's
  effects are skipped while the closure body runs exactly once.
- [x] Make erased execution the consistent public runtime contract for q0
  arguments. Both generated code and public interpreted entrypoints erase the
  argument, including effects hidden in bound postulates; raw
  `evalWithBindings` remains an explicitly lower-level evaluator of unerased
  terms. Property tests cover direct and imported definitions. Effects are
  still not tracked or checked for purity, so required operations must use a
  qω or q1 position.
- [x] Add an opt-in `requireCompiled()` block marker for the Phase 2
  representation backend (`int`, `seq[int]`, and `Option[int]`). It rejects
  definitions or wrappers outside that
  backend, emits only representation procs, and has a compiled-artifact audit
  proving the accepted static wrapper does not link `evalWhnf`. This is a
  deliberately small static subset. Imported definitions are compiled through
  their transitive closure when representable; other representations,
  ordinary-wrapper bootstrap, and `Value.syn` cleanup remain follow-up work
  (#358). Dynamic `runtimeValue` entrypoints remain interpreter-backed.
- [x] Specify and test the Nat runtime boundary across the interpreter,
  Phase 1, and Phase 2. Phase 2 successor checks `high(int)` explicitly;
  Value-to-Nim conversion rejects larger unary values. A 200-case property
  exercises the boundary and confirms no backend silently wraps, including
  builds with Nim overflow checks disabled.
- [x] Validate every baked global refId/name pair against the macro-time
  `Globals` table before code emission, including constructor IDs used by
  eliminator dispatch. A regression simulates a changed refId and checks that
  codegen rejects the mismatch instead of emitting a potentially miscompiled
  proc (issue #363).
- [x] Validate the emitted Phase-1 eliminator case dispatch against the
  constructor IDs in the kernel-validated reduction-rule table. Macro-time
  translation validation rejects missing, duplicate, or unregistered
  constructor labels and requires a default branch. It also validates each
  branch's constructor arity/spine-kind guard and malformed-spine fallback.
  Regressions delete a `natElim` branch and its shape guard; a dependent
  `Vec` clone differentially covers empty and singleton vectors, while a
  partially applied `natElim` is verified to remain on interpreter fallback
  (issue #378).
- [x] Add an opt-in compile-time codegen report (`-d:eponymCodegenReport`)
  that reports each block-local definition's highest emitted backend tier,
  the reason higher-tier compilation stopped, and runtime slow-path calls
  into definitions without a compiled local target (issue #370).
- [x] Review the host trust opt-ins as a family and add an opt-in per-block
  trust report (`-d:eponymTrustReport`). Keep dependent pair/result opt-ins,
  opaque mappings, custom codecs, and mutable adapters distinct, and explain
  that QTT single-use does not detect Nim reference aliases (issue #374).

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
- [x] Translate a direct Nim `nil` result or typed `List`/`Vec` local to the
  Eponym empty constructor using its declared family and element type. A
  property exercises direct and local empty runtime `List` values. Unsupported
  expression errors now name the Nim AST shape and give a practical workaround;
  a string-literal fixture pins it.
- [x] Preserve a supported-claims table in the docs: “checked by Eponym”,
  “checked by Nim”, “trusted adapter”, and “not currently connected”.
- [x] Extend PBT generators to exercise unifier occurs checks through nested
  terms and meta argument spines, randomly generated non-pattern meta spines,
  and distinct nested clause patterns that overlap. Coverage thresholds pin
  each shape; the properties check occurs-check rejection, deferred ambiguity,
  and overlap diagnostics (#232).

### Compile-time cost tracking (#376)

- [x] Benchmark `dependent_indices`, the checked Paxos example, and the
  lemma-heavy `lib/nat_lemmas.ep` corpus through Nim's compile-time boundary.
  Compare the pull request with its target commit on the same Nim runner.
- [x] Report median drift per corpus and fail CI only when growth exceeds both
  30% and 0.5 seconds. Save baseline and candidate measurements as workflow
  artifacts; test the regression detector with a synthetic 45% increase.
- [x] Keep the kernel re-check in the trusted path. Use existing phase
  profiles to guide optimization; do not treat a compile-time budget as
  permission to weaken checking.

### Dependencies and sequencing

The runtime ABI (B) precedes callable postulates (C); postulates precede the
end-to-end protocol (D). The optimizer connection (E) can proceed after the
runtime evaluator is general enough to interpret or compile a reified
objective. QTT-guided destination passing (F) is independent of protocol
bindings but depends on a runtime representation with explicit
ownership/liveness. Runtime code generation (H) proceeds from the erasure
boundary through a Value-level backend; it is separate from the optional
destination-passing optimization in (F).
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
