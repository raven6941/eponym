# Eponym trust model: what the system checks, and what is your problem

The Eponym design stance (2026-10-09): arbitrary host programs in types are
acceptable even if they may not terminate — a looping type-level program is
the author's problem, like a bad build script; a successful compile still
carries high certainty. This document states that position publicly: what
the system guarantees, what it checks for you, and the known soundness gaps
we have chosen to *document rather than fix* for now. Strict positivity of
`data` declarations (#33), mutual-recursion termination (#42), and the
universe hierarchy (#52) were in that set; all three are now checked at
elaboration time (see below).

## What the kernel checks and guarantees

Eponym's core type theory is QTT (quantitative type theory, Idris-style
0/1/ω) rather than ETT. Two layers share the trust boundary:

- **The elaborator** (`src/eponym/elab.nim`): bidirectional `inferTm`/`checkTm`,
  Miller-pattern unification for metavariables (`unify.nim`), implicit
  insertion, and full conversion checking at check-mode sites.
- **The independent kernel** (`src/eponym/kernel_check.nim`, issues #62, #156):
  an LCF-style auditor that re-checks every elaborated core term. It is
  deliberately independent — capture-avoiding substitution, a fresh weak-head
  evaluator (no NbE, no `RedRule` registry), type-directed conversion with
  eta, and the bidirectional judgments are all re-implemented from scratch.
  The only shared artifact is the `Term` syntax itself (the thing being
  audited); cached `Value` fields inside `tR` nodes are treated as untrusted
  hints and never consulted.

The kernel never silently accepts anything outside its fragment: metavariables
raise (`tMeta` — the zonk invariant must hold before kernel checking), and any
term outside the fragment raises "out of kernel fragment" rather than passing.

Fragment status (v2): the pure ETT fragment plus eliminator iota
(independently re-implemented *and* motive-validated — see below), `tNatLit`
(the kernel's own `suc^n(zero)` expansion, #93), and `tInt`/`tPrim`
(kernel axioms: primops are binary `Int` operations, Exp 11).

**Eliminators.** `data` declarations (Experiment 5) desugar to
postulate/elim/red. The elaborator registers eliminator `red` rules as
trusted "like an axiom" — but the kernel does not trust them: every iota
rule is validated against the motive derived from the eliminator's own Pi
type (`validateElimRules`). The elaborator also rejects non-structurally-
recursive calls in `red` rules at declaration time (see Termination below).

**Quantity discipline** (issues #64, #66; `usage_check.nim`). QTT quantities
are enforced, not advisory:

- `q1` (linear) binders must be used exactly once;
- `q0` (erased) binders must not be used;
- `qω` (unrestricted) binders are unchecked.

Enforcement happens in two places: in-judgment checks at each lambda while
the body is being checked (with correct depth tracking, so a type-level
mention of a linear variable does not consume it — types are checked in the
all-0 context), plus a post-elaboration whole-term pass as a backstop.
Known wart: the post-pass attributes domain (type-annotation) occurrences to
the innermost binder — an off-by-one the in-judgment check does not have.
Conversion respects binder quantities (#66), and erased parameters are
enforced at application sites. The initial core erasure pass (#328) replaces
the computation passed to a checked q0 application with an inert unit value;
it preserves the interpreter's current binder/application shape. This is a
runtime transformation, not an additional proof rule. It preserves results
Public generated and interpreted runtime entrypoints both erase q0 arguments,
so effects hidden in those arguments do not run. Raw `evalWithBindings`
remains a lower-level evaluator of the unerased core and can run them. The
type system does not track host effects or enforce purity; put any operation
that must execute in a qω or q1 position. Generated typed and compiled
wrappers omit q0 values from computational argument vectors; a separate
witness vector may still carry them to validate dependent runtime types.
Generated higher-order `Value` code uses nullary closures for q0 lambdas,
while the interpreter retains unary closures and inert unit witnesses.

**Inference** (issue #84). Unannotated binders do not default to
unrestricted: each becomes a quantity variable solved from observed usage —
zero relevant uses becomes erased (`0`), any use becomes unrestricted
(`ω`); quantity `1` is never inferred. Explicit annotations override.
Only term positions count as uses (domains, annotations, and motives do
not), and a body that still mentions unsolved metavariables keeps the
conservative `ω` (sound: only precision is lost, never correctness).

**Singleton types** (issue #74). Nat literals carry singleton types in
type position (`(d : 2)` demands exactly `2`); the one-directional
subsumption `tNatSing(k) <: Nat` lives in the elaborator's conversion and
is mirrored in both kernels (`eponym_init.check` and
`kernel_check.kCheck`), with 0 disagreements on the audit harness.

**Elaboration-time effects** (#41, #177). Conversion-handler effects
(`convElab` as the single effect-raising site) and ambient abilities
(Frank-style Σ threaded through `check`/`infer`) fire at macro
expansion/compile time, never in the object program. The #41 handler
discipline revalidates evidence with handlers uninstalled, LCF-style, so an
unsound handler fails loudly instead of silently corrupting. Object-level
effects are blocked on delimited continuations and are not part of the
guarantee set.

## Termination

**Checked (#36, merged 2026-10-09).** The criterion is syntactic structural
recursion, implemented twice: `checkStructuralRec` over `PreTerm` for `red`
rules (before the rule is registered) and `checkClauseTermination` for clause
definitions (after IH-rewriting; any surviving self-reference is
non-structural). A recursive call is accepted iff its scrutinee-position
argument is a bare pattern-bound variable — a direct subterm (with the #113
higher-order extension: the variable may be applied to lambda-bound
variables). Corpus: 10 terminating definitions accepted, 8 non-terminating
rejected, all under test timeout — no hangs. Rejections are located,
name-aware elaboration errors.

**Checked (#42).** Mutual blocks of clause-style `def`s are checked by
size-change termination (Lee/Jones/Ben-Amram) over per-call-site graphs:
each call site records strict (`<`, strict subterm) and non-strict (`<=`)
arcs from caller formals to callee formals; a block is accepted iff every
composed self-loop carries a strict self-arc (per-edge "a decrease
somewhere in the cycle" is unsound — see decisions.org #42). Corpus: 4
mutual blocks accepted (including even/odd elaborated and evaluated:
`even 4 = true`, `odd 4 = false`), 3 rejected; rejections name the cycle
(e.g. `ping -> pong -> ping`). The full mutual corpus elaborates in
0.029s. Limitation (MVP): mutual blocks must be clause-style defs.

**Unchecked, and the author's problem:**

- Anything beyond syntactic structural recursion (course-of-values / BelowD
  was considered and deferred, decisions.org #36).
- Type-level computation in general. Eponym elaborates at Nim compile time
  inside the `eponym`/`eponymBlock` macros. A type-level program that loops
  (e.g. through a `postulate`d primop, or a hostile `red` rule set the
  structural check was never designed to see) hangs the Nim compile the same
  way a bad build script would. The design stance is explicit: this is the
  author's problem, not the system's. A successful compile carries the
  guarantees in this document; getting to a successful compile is yours.

## Positivity (#33, implemented 2026-10-15)

`data` declarations are checked for **strict positivity** at elaboration
time (`elabDataDecl`, via `checkFamIndices`/`splitCtorArg` in
`src/eponym/elab.nim`). A constructor argument like
`bad (k : (Bad -> O) -> Bad) : Bad` puts the type being defined in a
negative position and is rejected with a located error naming the
constructor and the offending argument. The check covers:

- the domains of leading Pi telescopes in constructor argument types
  (the type being defined may not occur there — the #113 eliminator
  requirement, now enforced for every `data` declaration);
- the head of a family occurrence, which must be a direct application of
  the family to indices (nested occurrences through other type formers,
  e.g. `Box Nest`, are rejected — conservative, see decisions.org #33);
- the family occurring inside its own *index terms*, whether in the
  constructor's return-type indices or in the indices of a family-headed
  argument type (also rejected conservatively).

Combined with propositional equality, negative occurrences could encode
paradoxes and non-termination; the check closes that hole for the
`data` declarations the system itself accepts. (Universe discipline #52
and mutual-recursion termination #42 remain the author's problem, as
documented above.)

## Universes (#52, implemented 2026-10-15)

The core has an explicit hierarchy, `Type l : Type (l+1)`. `Pi`/`Sig`
formation takes the maximum of the domain and codomain levels, and
cumulativity is directional: `Type i` checks against `Type j` for `i <= j`
at ascription points, while conversion itself stays level-strict (so
equality-handler extensions never see subtyping as an equality goal).

Surface universe syntax is explicit: `Type l` has type `Type (l+1)`. The old
surface `?` universe notation has been retired; `?` now introduces an
elaboration hole, and `_` is used for discarded binders and wildcard
patterns. In `eponymBlock`, `Univ` maps to `Type 0` because Nim cannot spell
the universe token directly.

## Host code, postulates, and the phase distinction

Eponym is *embedded*: there is one phase boundary, and it is Nim's compile
time.

- **Surface entry.** `eponymBlock` converts a Nim AST block to Eponym source
  text, feeds it to the canonical string parser (`parse_surf`), elaborates,
  and generates wrapper procs (eponym_mac.nim). The macro is deliberately
  thin: no NimNode semantic inspection, no hygiene tricks — elaboration
  failures become Nim compiler errors. The Nim-shaped syntax is translated
  into Eponym forms first: for example, supported arithmetic and pure
  `if`/`elif`/`else` expressions become Eponym primitive/application terms.
  This translation does not run arbitrary Nim expressions or import Nim
  semantics into Eponym. Per #144, the standalone and embedded grammars are
  one grammar after translation.
- **`postulate` is an axiom.** `postulate Int : Type 0` asserts a type with no
  evidence; machine `Int` and its primops (`tPrim`) are kernel axioms — the
  kernel trusts that the Nim host's binary `Int` operations are what they
  claim to be. If the host lies, every proof that touches `Int` lies too.
- **Runtime re-elaboration.** Ordinary wrappers may re-run the elaborator on
  first runtime use (cached by source and base directory;
  `eponym_embed.nim`) to obtain terms with runtime closures. Subsequent calls
  use the cache. `requireCompiled()` wrappers use direct representation code
  and do not take this path. Compile-time elaboration is the checking. A
  definition whose ordinary runtime re-elaboration fails was still checked at
  compile time; the runtime path cannot introduce an unchecked term.
- **Runtime value codecs.** First-order generated wrappers convert primitive
  `Int`/`Nat`, opaque mapped values, non-dependent `Sig(A, B)` values
  represented as two-element Nim tuples, and non-dependent named records
  represented as mapped Nim objects. Structural codecs recursively convert
  fields according to their Eponym types; opaque field mappings and host
  adapter behavior remain trusted. Dependent Sigma values and records with
  dependent fields are rejected; the bridge does not erase a dependent index.
  `bindPostulatePair` supports one to three codec-supported named arguments
  and a non-dependent Sigma result. Its generated adapter checks the Nim tuple
  type and recursively encodes both fields. `bindPostulatePairTrusted` permits
  a dependent result when its fields have codecs; Nim does not prove that a
  host field matches its Eponym index, so the adapter author owns that guarantee.
- **Runtime Nat range.** The interpreter and Phase 1 keep Nat as `zero`/`suc`
  `Value`s, so they can construct a value above `high(int)` while memory
  permits. Converting such a value to Nim with `valueToNat` raises
  `ValueError: runtime Nat does not fit Nim int`. Phase 2 represents Nat as a
  Nim `int`; its generated `suc` checks the bound explicitly and raises the
  same error at `high(int)`, even when Nim overflow checks are disabled. Thus
  no backend silently wraps, but a raw `Value` can hold a larger unary Nat
  than a Nim `int` can carry. `high(int)` depends on the host architecture.
  Phase 2 `natElim` is iterative but still takes time proportional to its
  input; an in-range value near `high(int)` is representable, not practical to
  fold.
- **Postulate bindings are block-level axioms.** Declare `bindPostulate` in
  the same `eponymBlock` as the postulate and checked definitions that use it.
  The binding is not part of the Eponym type: the checker checks each call
  against the postulate signature, and Nim checks the adapter's mapped
  signature, but neither proves the adapter's behavior. A generated checked
  wrapper does not expose the internal adapter as an argument or encode its
  identity in the wrapper signature. We keep the binding visible once beside
  the postulate rather than repeating it at each use site; repetition would
  not add a proof obligation or make the host implementation verified. When
  reviewing a checked role, inspect the block's bindings as part of the trust
  boundary. Imported `.ep` definitions use the binding supplied by the block
  that instantiates them.
- **Host evaluation inside types.** There is no general splice of arbitrary
  Nim code into types; the trust boundary is that *you* are the compiler
  plugin. Any Nim computation you run to produce or check an Eponym program
  (scripts generating surface text, compile-time helpers) is your own code
  with your own bugs — the guarantees in this document cover what the
  elaborator and kernel check, not what your metaprogramming computes.

## The Nim boundary and trusted opt-ins

Every postulate adapter is trusted for behavior even when its Nim signature
matches the checked Eponym type. `bindPostulatePairTrusted` adds trust in the
dependent relationship between a pair's fields and its index. The separate
`runtimePairTrusted` and `runtimeRecordTrusted` opt-ins permit typed wrappers
when the available field codecs cannot reconstruct and validate that
relationship; codecs still check the field shapes and any indices they do
represent. Keep these opt-ins separate because they authorize different
operations at different boundaries.

An explicit opaque `runtimeType` mapping trusts the correspondence between
the Eponym type and the chosen Nim representation, including aliasing and
lifetime behavior. A custom `runtimeCodec` additionally trusts its encoder and
decoder. Neither opt-in proves properties of the host value itself.

**Family-wide opaque mappings assert index-independence (#401).** A
`runtimeType` mapping on an applied family (`Chan s`, `AcceptMsg n`) declares
*one* host type for every index tuple: the representation tier drops the
indices from the host signature (`Chan s` is `PaxosChannel` for all `s`, as
`Vec A n` is `seq[int]` for all `n`). The checker cannot verify that the host
layout is genuinely index-independent — for example, that no `s` needs a
differently-shaped channel — so declaring the mapping is a trust assertion by
the block author, in the same family as `bindPostulatePairTrusted`. The
dependent `Sig` compiled to a host tuple is sound exactly when its component
mappings are index-independent in this sense; a `Vec` length index mentioning
the bound Sigma value is honestly rejected instead of silently erased.

`bindPostulateMutable` is retained with decoded-local/result-out semantics:
the adapter receives decoded local variables, and its encoded result returns
to Eponym. It does not receive the caller's Nim variable as a `var` alias, and
the runtime does not deep-copy reference-like mapped values. Mutating through
a reference stored inside a decoded value can still affect shared host state,
so alias and effect behavior remains trusted. The opt-in name refers to the
mutable Nim adapter parameters.

For a build-time inventory of these boundaries in each `eponymBlock`, compile
with `-d:eponymTrustReport`. The report is diagnostic text and is not a stable
machine-readable interface. QTT linearity still checks uses of Eponym values
inside the block; it cannot detect two Nim references that alias the same
host resource.

## Summary of the trust boundary

| Checked for you | Your responsibility |
|---|---|
| Bidirectional elaboration + conversion (kernel re-checks, LCF-style) | Termination beyond structural recursion + size-change (#36, #42) |
| Eliminator iota rules (motive-validated by the kernel) | Girard's paradox from an inconsistent universe rule (the hierarchy is explicit, #52) |
| QTT quantity discipline (linear used once, erased unused; inference for unannotated binders, #84) | Termination of type-level computation (author's problem) |
| A checked caller's postulate type and the mapped Nim adapter signature | Adapter behavior, opaque type mappings, reference aliasing, and host lifetime rules |
| Structural recursion for `red` rules and clause defs (#36); mutual recursion via size-change termination (#42) | Soundness of `postulate`d primops (host `Int` ops) |
| Strict positivity of `data` declarations (#33) | Anything your own metaprogramming computes |
| Universe hierarchy `Type l` + directional cumulativity (#52) | |
| Nat singleton types, one-directional subsumption `tNatSing(k) <: Nat` (#74) | |
| Phase 2 Nat successor checks the `high(int)` boundary; all backends reject Nim conversion of larger values | Mathematical Nat values beyond Nim `int` are not available through the Nim `int` boundary |
| Handler evidence revalidated LCF-style (#41) | |

Eponym's guarantee: a term that elaborates *and* passes the kernel was
checked by a small independent checker against QTT's judgments, with
quantities enforced, eliminators motive-validated, recursion structurally
guarded, and universes stratified — modulo the documented deferrals above
(legacy-`?` Type-in-Type, type-level termination, postulate soundness).
