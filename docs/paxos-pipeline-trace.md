# Paxos end-to-end pipeline trace (issue #355)

**Status: complete.** Architectural checkpoint from the 2026-10-21 design
review: trace one realistic program — the checked Paxos proposer/acceptor
(#101, `examples/embedded/paxos_session.nim`) — from source through every
pipeline stage, recording every representation it becomes and every trust
boundary it crosses. Deliverables: this document, a recorded verdict on #67
(explicit IR DAG) in `decisions.org`, follow-up issues for load-bearing gaps,
and the TCB inventory below.

Sequencing: runs after the scalar (Int/Nat/Bool) fragment of #330 (landed on
main as `9373bd4`) and **gates the Vec/`seq` match-compilation work in #330**.
Not a blocker for scalar Phase 2 work, #331 design discussion, or the interop
stack.

## The program under trace

`examples/embedded/paxos_session.nim` (288 lines): dependent session types
describe the prepare/promise/accept/accepted protocol. Two checked roles:

- `proposer(ballot: Nat, ch {.linear.}: Chan(propProto())): Sig(accepted: Nat, Chan(endS()))`
- `acceptor(stored: Nat, ch {.linear.}: Chan(accProto())): Chan(endS())`

The dependent index that earns the checking: `promiseTicket(promise):
AcceptMsg(promiseValue(promise))` — the ticket type is indexed by the promised
value, so `sendAccept` can only be called with the ticket for the received
promise. Channels are linear (`{.linear.}`); `Promise`/`PaxosTicket` values
cross the runtime boundary as opaque Nim objects via explicitly trusted codecs
(`bindPostulatePairTrusted`).

## Stage 1 — Surface / embedded source (`eponymBlock`)

Modules: `src/eponym/eponym_mac.nim` (the `eponymBlock` macro),
`src/eponym/parse_surf.nim`, `src/eponym/preterm.nim`.

What `eponymBlock` receives is the **Nim AST of the block** — it converts the
block to Eponym source text and feeds it to the canonical string parser
(`parse_surf`); the standalone and embedded grammars are one grammar after
translation (#144). The macro is deliberately thin: no NimNode semantic
inspection, no hygiene tricks; elaboration failures become Nim compiler
errors (`docs/trust-model.md`).

Surface forms the Paxos block uses:

- `import "../../lib/nat.ep"` — the prelude via real `import` (#131), not
  redefined locally.
- `data(Session, Univ)` with `proc sendD(A: Univ, k: A -> Session): Session`
  etc. — desugars to postulate/elim/red (Experiment 5); elaboration checks
  strict positivity (#33).
- `postulate` (axioms: `Chan`, `Promise`, `AcceptMsg`, the protocol
  operations), `runtimeType` (codec mapping: `Chan`→`PaxosChannel`,
  `Promise`→`PaxosPromise`, `AcceptMsg`→`PaxosTicket`).
- `bindPostulate` / `bindPostulatePair` / `bindPostulatePairTrusted` —
  block-level axioms pairing each postulate with a Nim adapter proc.
- `proc` with `{.linear.}` binder annotations (QTT quantity 1 on the channel
  handle), `let`, `fst`/`snd` on Sigma values, `lam` for the session
  continuations.
- Nim-shaped conveniences translated to Eponym forms first (e.g. arithmetic
  and pure `if` become Eponym primitive/application terms); the translation
  does not import Nim semantics into Eponym.

Surface → `PreTerm`: parsing (`parse_surf`) produces `PreTerm`, the parser's
datatype; desugaring (`desugarTy`/`desugarTm`) expands telescopes and resolves
sugar. The Paxos block's session-type procs (`propAfterPrepare` etc.) are
ordinary `proc` definitions elaborated bidirectionally against their
ascriptions.

## Stage 2 — Elaboration (direct elaborator)

Modules: `src/eponym/elab.nim`, `src/eponym/unify.nim` (Miller),
`src/eponym/kernel_check.nim`, `src/eponym/elab_trace.nim`.

Metas are created wherever the bidirectional checker must defer: implicit
arguments (the `A: Univ` of `sendD`, the `Univ` indices of the session
family), the dependent index `AcceptMsg(promiseValue(promise))` (whose
well-formedness requires `promiseValue`'s type and the promise's), and the
Sigma projections `fst`/`snd` in the roles. Pattern unification (`unify.nim`)
solves them; `flushDeferredElab` retries suspended goals once at
declaration end, and leftovers become an ambiguity error (`elab.nim`).

Zonking (`elabCheck` zonks) substitutes every solved meta, leaving
**`ElabDef`s whose `ty`/`tm` fields are closed, zonked core `Term`s** —
the `tMeta` nodes gone. The `GEntry` table (`Globals`) records per-name the
`R` node, the zonked type (for implicit insertion at use sites), and
eliminator metadata (`isElim`, `elimNargs`).

What the kernel re-validates vs trusts (`kernel_check.nim`, #62/#156,
LCF-style): the kernel re-checks *every* elaborated core term with an
independent implementation — fresh capture-avoiding substitution, its own
weak-head evaluator, type-directed conversion with eta, re-implemented
bidirectional judgments. It shares only the `Term` syntax (the artifact
being audited); cached `Value` fields inside `tR` nodes are untrusted hints,
never consulted. `tMeta` raises (the zonk invariant must hold first); terms
outside the fragment raise "out of kernel fragment" rather than passing.
Eliminator iota rules — which the elaborator registers "trusted, like an
axiom" — are **motive-validated by the kernel** against the eliminator's own
Pi type (`validateElimRules`). Primops (`tPrim`) are kernel axioms: the
kernel trusts the host's binary `Int` operations.

For Paxos this means: the checked roles (`proposer`, `acceptor`) and the
session-type family definitions pass through two independent
implementations of the judgments; the protocol operations themselves are
postulates (axioms) whose *behavior* is trusted (Stage 5), but whose
*call sites* are checked against the postulate types — including the
value-indexed ticket types and the linear channel threading.

## Stage 3 — Interactive refinement (holes/sheds)

Modules: `src/eponym/sheds.nim`, `src/eponym/sheds_mac.nim`,
`src/eponym/shed_layout.nim`, `src/eponym/lsp.nim`.

This remains the least structured leg, but issue #377 adds an in-process
semantic snapshot for inspection. `HoleInfo` retains a typed metavariable,
goal term, and named binder context; `semanticShedState` zonks the goal and
context types and represents the goal's Pi spine as binders. LSP hover
consumes that state.
The sidecar itself is still a presentation record. `ShedInfo` (`sheds.nim`)
carries:

- `name`, and `draft` — the `repr` of the draft Nim node, user-owned scratch
  text that **never reaches the elaborator**;
- source positions (`nimLine`/`nimCol`, `holeLine`/`holeCol`) and `holeIdx`,
  an index into `MetaStore.holes` after hole-tolerant elaboration
  (`elabCheckHolesDir`, the #58 hole infrastructure);
- `goal` and `ctx` as **pretty-printed strings** (`"name : type"`), plus
  `goalPi` (the Pi spine as binder strings), projected from the semantic state;
- `genSrc` — the block's generated Eponym source, so the LSP can run real
  `#58` refine actions on `.nim` documents;
- `status` — the white/yellow/brown Epigram colour, serialized to the
  sidecar JSON (`<nimfile>.sheds.json`) that the LSP turns into diagnostics.

The editor's in-process hover path now sees structured terms. The sidecar
still carries rendered projections because it crosses the compiler/LSP
process boundary; those strings are not parsed back into terms. Refinement
actions continue to edit generated source and re-elaborate through the
existing hole-filling machinery. The draft remains user-owned Nim AST text
and is never checked by Eponym. See `docs/shed-semantic-model.md` for the
snapshot lifetime and future serialization boundary.

## Stage 4 — Erasure (#328)

Modules: `src/eponym/erasure.nim`, `src/eponym/usage_check.nim` (QTT).

`eraseQ0Arguments` consumes a **checked, closed core `Term`** and produces a
core `Term` of the same shape: it runs `checkUsage` first (the QTT quantity
discipline — q1 used exactly once, q0 unused, enforced in-judgment and by a
post-elaboration backstop), then replaces every *computation supplied to a
q0 application* with the inert unit value `tmC(cVoid)`. It fails loudly on
`tMeta` ("cannot erase a term with unresolved metavariable") and on
applications whose function type cannot be recovered as a Pi — erasure is
total over well-typed closed terms or it raises.

For Paxos: the value-indexed ticket proofs and any q0 proof arguments passed
to protocol combinators are replaced by unit; **what must survive past
erasure is exactly what #331 (linearity/DPS) depends on**:

- binder **quantities are preserved on the `Term`** (`mkBinder` carries
  `t.qty` through), including the `q1` linearity of `ch`;
- the **checked term keeps its binder/application shape** so the interpreter
  can evaluate the original term. Generated typed and compiled wrappers omit
  q0 values from computational arguments, retaining a separate witness vector
  only where dependent runtime types need it. Generated higher-order Value
  code also uses nullary q0 closures; the interpreter remains unary.

Erasure is a runtime transformation, not a proof rule. For pure q0 arguments,
the checked binder cannot inspect the argument in computational position, so
the unit witness preserves the result. Postulate effects are not tracked,
however: generated code skips effects in q0 arguments while direct evaluation
of unerased source may run them. This caveat is **optimization-only** (see the
TCB inventory); any effect that must run belongs in a qω or q1 position.

## Stage 5 — The interop boundary

Modules: `src/eponym/eponym_mac.nim` (postulate/binding elaboration),
`src/eponym/eponym_init.nim`, `src/eponym/eponym_embed.nim`
(`HostRuntimeType`, `callValueFuncDir`); `docs/trust-model.md`; #336 var
adapters; #337 trust documentation; #242 arithmetic evidence.

The `runtimeType` declarations are the **representation spec** — reused by
#330's repr tier (`compileBlockProcs` takes the block's `runtimeTypes:
seq[HostRuntimeType]` and `isPlainIntMapping` recognizes the plain
`-> int` case). For Paxos:

| Eponym type | Nim type | Mapping kind |
|---|---|---|
| `Chan` | `PaxosChannel` (ref object wrapping a `Socket`) | opaque |
| `Promise` | `PaxosPromise` | opaque |
| `AcceptMsg` | `PaxosTicket` | opaque |
| `Nat` | `int` | plain (identity boundary) |

What each binding form trusts:

- `bindPostulate(f, hostF, ...)` — first-order: the checker checks each call
  against the postulate signature; Nim checks the adapter's mapped
  signature; **the adapter's behavior is trusted**.
- `bindPostulatePair(f, hostF, ..., A, B)` — one non-dependent Sigma result:
  the generated adapter checks the Nim tuple type and recursively encodes
  both fields per their Eponym types. Dependent Sigmas are rejected — the
  bridge does not erase a dependent index.
- `bindPostulatePairTrusted(f, hostF, ...)` — permits a *dependent* result
  when its fields have codecs (used for `recvPromise`, `recvPrepare`,
  `sendPromise`): **Nim does not prove a host field matches its Eponym
  index, so the adapter author owns that guarantee.** The Paxos
  ticket/index mapping — `hostPromiseTicket` returning `promise.ticket`
  against the type `Pi(promise: Promise, AcceptMsg(promiseValue(promise)))`
  — is the explicitly trusted codec in this program.

What crosses the boundary as opaque (`PaxosChannel`, `PaxosPromise`,
`PaxosTicket`) vs what stays checked (the indexed session types, the linear
threading of the channel handle through `proposer`/`acceptor`, the
requirement that `sendAccept`'s ticket has type
`AcceptMsg(promiseValue(promise))` for *the* received promise). The host
transport (TCP sockets in the example, `session_runtime_bindings` codec) is
trusted and outside the checked fragment — the example's own header says
so. #336's mutable postulate adapters (`var` parameters) extend the
trusted surface to Nim-side mutation; aliasing and host lifetime rules are
the author's responsibility (`docs/trust-model.md`).

## Stage 6 — Phase 1 Value backend (#329)

Modules: `src/eponym/codegen.nim` (naive tier), `src/eponym/eponym_init.nim`
(`Value` constructors).

`compileBlockProcs(defs, globals, ...)` consumes the block's **`ElabDef`s
(closed, zonked, erased core `Term`s) plus `Globals`** — the refId/name
tables and eliminator metadata — and emits Nim AST manipulating `Value`s
directly. Per definition it emits `eponymCompiled_<name>`; the typed
wrapper's calling convention is unchanged, only the wrapper body's
evaluation call is rerouted from the interpreter to the compiled proc.

Semantics: the same as the `evalWhnf` interpreter, but with no dispatch loop
over `Term` nodes and no per-call re-walk of the definition's term (today
every wrapper call re-runs `evalWithBindings` on the def term). Eliminators
(`wRed`) become a generated `eponymElim_<name>` proc holding the static
case dispatch over the registered reduction rules — fully applied, or
partially-applied/bare and eta-expanded at macro time into nested
`vHostFunc` closures over the missing arguments whose innermost body is
the saturated dispatch call (issue #407); an over-applied eliminator
falls back to the interpreter. `tR` to block-local definitions becomes a direct recursive
call; to other definitions, a cross-block direct call when the callee was
exported by an earlier block in the same compilation via the compile-time
export registry (issue #408 — value tier unconditional, repr tier on
signature agreement and only when the callee's closure touches no postulate
bound in the exporting block), else the `callValueFuncDir` slow path;
`tPrim` becomes `vPrim` accumulation.

The module header documents the **deliberate deviations from the
interpreter** (all unreachable in checked code): `syn` fields are
approximate (never nil, but not substituted); an eliminator scrutinee whose
spine length mismatches `nParams + ctorArity` yields a stuck neutral where
the interpreter would raise `IndexDefect`; refIds are baked in as integer
literals (stable across elaborations of the same source — sequential
`freshId`, deterministic elaborator — pinned by the differential tests);
reduction-rule contractum templates are compiled as written (unerased),
matching the interpreter's `fireRed` on the unerased template.

For Paxos, Phase 1 compiles the pure session-type plumbing and role
composition; the postulate calls still go through the interop adapters, and
the `Nat` values in the protocol (ballots, accepted values) are boxed
`Value`s at this tier.

## Stage 7 — Phase 2 representation backend (#330)

Modules: `src/eponym/codegen.nim` (repr tier: `reprProcs`, `compileElimProc`,
`compileDefProc`, `cgRepr*`).

The scalar fragment (landed as `9373bd4`) adds, for definitions whose
signatures map to plain host representations, an
`eponymCompiledRepr_<name>(p1: int, ...): int` proc whose body is direct
host code: primitive `Int` ops become Nim arithmetic, `Nat`/`Bool`
constructors become int literals and arithmetic, `natElim` becomes an
iterative fold, `boolElim` a conditional, calls become direct calls. The
typed wrapper **prefers the repr proc when the boundary is the identity**
(all-`int` formals and result, checked by `reprSig` against the
`runtimeType` mapping via `isPlainIntMapping`), skipping the `Value`
conversions. `reprSig` raises `CgUnsupported` — falling back to the Phase 1
tier — for anything outside the fragment (non-atomic binder domains,
non-`tR` result, erased binders in the signature, missing mappings). Since
#407 slice 3, function types are inside the fragment: a (non-dependent)
function type is a `{.closure.}` Nim proc type flattened across curried
binders, so closure values (partially-applied eliminators) and compiled
definitions of matching host arity cross definition boundaries as ordinary
proc values; quantity-0 function domains and arity mismatches (e.g. after
quantity inference erases a parameter) are honest named fallbacks.

The representation spec is the same `runtimeTypes` block mapping from Stage
5: where `Nat`→`int` is declared, host `int`s replace `Value`s. The
preservation relationship to core evaluation is: the repr tier is a
**verified-by-testing specialization** of the Phase 1 tier, which is a
**documented-deviation transliteration** of the interpreter, which evaluates
the **erased core term**, which the kernel independently checked. The chain
is only as strong as its links: kernel soundness → erasure's observational
equivalence → Phase 1's documented deviations → the differential suites
(`tests/test_codegen_phase1.nim`, `tests/test_codegen_phase2.nim`).

**Vec/`seq` (gated — not started).** Indexed-family match compilation is the
known hard corner: the motive depends on the scrutinee's indices, so the
compiled case dispatch must respect index unification, not just constructor
tags. `compileElimProc` today handles only the fully-applied,
non-indexed shape; the gated work must decide how the `wRed` iota-rule
tables (which the kernel motive-validates) become a compiled case tree that
preserves the motive discipline. **This checkpoint's verdict on that work is
in the questions below.**

## Questions the trace must answer

### 1. #67 verdict: is an explicit multi-level IR DAG needed?

**No — not for the pipeline this trace exhibits.** The property that makes
it unnecessary: **every backend consumer agrees on one representation.**
The kernel auditor, the erasure pass, the Phase 1 emitter, and the Phase 2
repr tier all consume the same artifact — the zonked core `Term` — plus one
auxiliary table, `Globals` (name↔refId, eliminator metadata, iota-rule
registry) and the block's `runtimeType` codec mapping. No stage needs a
different term form than the one the previous stage produced: erasure is
`Term → Term` (same datatype, same shape); codegen is `Term → Nim AST`.

The tangle #67 wants to untangle — implicit insertion interleaved with
bidirectional checking inside `elab.nim` — is real, but it is an
*elaborator-implementation* concern, invisible to every consumer. Naming the
layers (Surface → Desugared → Explicit → Checked → Zonked) would not change
any consumer's input or enable any new check; the stage-boundary structure
the backend actually needs already exists as separate *data* (the `Globals`
tables), not as a term IR. Refactoring `elab.nim` into layers would buy
debuggability of elaboration internals — a genuine but different benefit —
at the cost the issue already names (untangling is real work), and the trace
gives no evidence any pipeline stage is blocked on it.

**Reversal condition** (recorded so the verdict is falsifiable): if a
future stage needs a term form the core `Term` cannot carry, introduce that
as a *local* internal IR at that stage boundary — DAG-style, exactly as #67
suggests — without re-layering elaboration. Two concrete triggers: (a) the
gated Vec/`seq` work, if indexed match compilation turns out to need an
explicit case tree with motive witnesses rather than direct `wRed`-table
emission; (b) #331, if DPS/linearity needs a CPS or ANF normal form the
`Term` datatype cannot express. Until a trigger fires, `Term` + `Globals` +
codec map is the IR, and it is one level, not a DAG.

### 2. Backend input: what exactly should the codegen backend consume, long-term?

Exactly what `compileBlockProcs` takes today, with the fragment contract
tightened: **closed, zonked, erased core `Term`s (`ElabDef`s) + `Globals`
(refId/name/eliminator tables) + the block's `runtimeType` codec mapping**,
with QTT quantities carried on the binders (erasure preserves `t.qty`; #331
needs them). The tightening is #358's program, not a new IR: fragment total
over closed zonked terms (fail loudly at macro time instead of silent
interpreter fallback), per-block compilation of the transitive closure from
exported entry points (killing the `defnValue` slow path), and removing live
`syn` dependencies from the compiled path. The trace shows the current
per-definition tiering is *sound-by-fallback* (anything unsupported keeps
the interpreter wrapper) but *fragile-by-assumption* (baked refIds,
approximate `syn`) — #358 converts the assumptions into checked contracts.

### 3. Semantic preservation (Phase 2)

Today's mechanism is three-part: the documented deviations in
`codegen.nim`'s header (the complete list of ways the emitter knowingly
differs from the interpreter), the differential suites
(`test_codegen_phase1.nim`, `test_codegen_phase2.nim`), and the per-definition
fallback that keeps uncompilable definitions on the interpreter. Differential
testing is necessary but not sufficient — the invariant that would make
"compiled ≡ interpreted" checkable **by construction** is a single source of
truth for the operational rules: derive the `cg`/`cgRepr` case analysis from
the same rule set as `evalWhnf`/`fireRed`, or add translation validation
that the emitted case dispatch covers exactly the registered red-rule table
(`detectBadElims` is the seed of this — it already rejects bad eliminator
shapes at macro time; extend it to certify dispatch coverage).

Corner cases the Vec/`seq` tests must target (from the trace):

- **motive-dependent iota**: the kernel motive-validates every iota rule;
  the compiled case tree must not drop the motive discipline when indices
  are erased to host values;
- **partial eliminator application**: today it falls back to the
  interpreter — a soundness cliff if the repr tier ever accepts a partially
  applied eliminator without the same fallback;
- **scrutinee spine shape**: the Phase 1 deviation (stuck neutral vs
  `IndexDefect`) is unreachable in checked code only if elaboration can never
  produce the mismatch — the differential tests must include the
  negative-eliminator corpus, not just the happy path.

### 4. TCB inventory

From the trace, by module/function:

**(a) Trusted for soundness** — if this is wrong, checked programs lie:

- `src/eponym/kernel_check.nim` itself: the LCF auditor is the last line;
  small and independent, but still trusted code.
- The `Term` datatype (`eponym_init.nim`): the shared artifact every stage
  reads; a miscompilation of pattern matches over it corrupts everything
  downstream.
- Host `Int` primops (`tPrim` as kernel axioms): if the Nim host's binary
  `Int` operations are not what they claim, every proof touching `Int` lies.
- Postulate adapters and their behavior (`hostSendPrepare`,
  `hostRecvPromise`, …, `hostPromiseValue`, `hostPromiseTicket`): checked
  only in *type*, never in behavior.
- `runtimeType` codec mappings and the `bindPostulatePairTrusted` adapters:
  the Paxos ticket/index mapping is explicitly trusted — Nim never proves
  the host field matches its Eponym index.
- Host transport and `session_runtime_bindings`: TCP framing, Nat codec —
  outside the checked fragment by design.
- #336 mutable adapters: Nim-side aliasing and lifetime rules.
- RefId determinism: codegen bakes refIds as integer literals assuming the
  sequential-`freshId` deterministic elaborator; pinned by differential
  tests, but an assumption, not a proof (follow-up issue filed: resolve by
  name at macro time).

**(b) Evidence-generating but core-validated** — wrong output fails loudly
at the kernel:

- `src/eponym/elab.nim` (bidirectional elaboration, implicit insertion,
  conversion) and `src/eponym/unify.nim` (Miller): producers; the kernel
  re-checks every judgment.
- `src/eponym/usage_check.nim` (QTT discipline): the kernel independently
  enforces quantity judgments.
- Eliminator iota-rule tables: registered by the elaborator "trusted, like
  an axiom"; every rule motive-validated by the kernel (`validateElimRules`).
- `convElab` handler evidence (#41): revalidated with handlers uninstalled,
  LCF-style.

**(c) Optimization-only** — must preserve observable behavior of checked
code, trusted for nothing else:

- `src/eponym/erasure.nim`: q0 arguments are uninspectable in checked code,
  so the unit substitution is observationally equivalent; it is a runtime
  transformation. Generated wrapper ABIs omit q0 computation arguments;
  dependent witnesses remain separate from those arguments.
- `src/eponym/codegen.nim` (Phase 1 + Phase 2): "compiled ≡ interpreted" is
  a tested claim with documented deviations and interpreter fallback, not
  a trusted axiom.
- Conversion/e-graph caches and the `RedRule` registry: performance
  machinery; the kernel consults none of it.
- Everything under `src/experimental/` (relational/staged): not in the
  production pipeline (see question 5).
- The sheds/LSP layer (`sheds.nim`, `lsp.nim`): tooling; sheds manipulate
  sidecar records and hole indices, never terms — they cannot alter what
  the checker checked.

### 5. Production pipeline membership

The trace exhibits exactly one production pipeline:

```
parse_surf → elab (+unify) → kernel_check → usage_check → erasure → codegen
```

with `eponym_mac`/`eponym_embed` as the Nim-embedding shell (macro
expansion, runtime re-elaboration cache, typed wrappers) and the sheds/LSP
stack as hole-tolerant tooling on the side (it consumes elaborator hole
state, never core terms). **Nothing in the Paxos trace touches
`src/experimental/`.** The relational/staged machinery therefore stays
experimental under the burden-of-proof rule recorded in `decisions.org`
(2026-10-21): it graduates only on demonstrated backward
execution/synthesis, materially less machinery, or competitive forward
code. This trace adds a fourth data point to that entry's evidence: the
entire realistic program — dependent session types, linearity, erasure,
interop, two codegen tiers — composes without it.

## Follow-ups filed from this trace

- **#358** (already open): the interpreter-free guarantee — fragment total,
  per-block compilation, live `syn` removal. This trace confirms it is the
  right hardening of the backend input (question 2), not a new IR.
- **#363** (filed from this trace): codegen bakes refIds as integer literals
  on the assumption of deterministic elaboration order; resolve or validate
  them by name at macro time so an elaborator change cannot silently
  miscompile.
