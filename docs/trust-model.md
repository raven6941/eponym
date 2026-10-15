# Eponym trust model: what the system checks, and what is your problem

The Eponym design stance (2026-10-09): arbitrary host programs in types are
acceptable even if they may not terminate — a looping type-level program is
the author's problem, like a bad build script; a successful compile still
carries high certainty. This document states that position publicly: what
the system guarantees, what it checks for you, and the known soundness gaps
(#42, #52) we have chosen to *document rather than fix* for now. Positivity of
`data` declarations (#33) was in that set until 2026-10-15; it is now
checked at elaboration time (see below).

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
enforced at application sites.

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

**Unchecked, and the author's problem:**

- Mutual recursion (#42, open). Only single-function self-recursion is
  checked. A mutual block (`even`/`odd` style) can encode non-termination.
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

## Universes (#52, open — documented, not fixed)

The core is `? : ?` — Type-in-Type, known-inconsistent. `Nat : ?`, `? : ?`;
the kernel itself checks against `cStar` (kernel_check.nim:462,748). The
honest policy: **don't write Girard's paradox**. Epigram itself treated
stratification as out of scope ("Epigram Reloaded" calls it orthogonal to the
paper), but we do not claim the original's scope as cover — #52 is the
explicit, tracked deferral (explicit levels vs level inference vs constraint-
based remains undecided, decisions.org #52 reserved). If you need universe
discipline from Eponym, it does not exist yet.

## Host code, postulates, and the phase distinction

Eponym is *embedded*: there is one phase boundary, and it is Nim's compile
time.

- **Surface entry.** `eponymBlock` converts a Nim AST block to Eponym source
  text, feeds it to the canonical string parser (`parse_surf`), elaborates,
  and generates wrapper procs (eponym_mac.nim). The macro is deliberately
  thin: no NimNode semantic inspection, no hygiene tricks — elaboration
  failures become Nim compiler errors. Per #144, the standalone and embedded
  grammars are one grammar.
- **`postulate` is an axiom.** `postulate Int : ?` asserts a type with no
  evidence; machine `Int` and its primops (`tPrim`) are kernel axioms — the
  kernel trusts that the Nim host's binary `Int` operations are what they
  claim to be. If the host lies, every proof that touches `Int` lies too.
- **Runtime re-elaboration.** The wrappers re-run the elaborator at runtime
  (cached; eponym_embed.nim) only to obtain evaluable terms — compile-time
  elaboration is the checking. A definition whose runtime re-elaboration
  fails was still checked at compile time; the runtime path cannot introduce
  an unchecked term.
- **Host evaluation inside types.** There is no general splice of arbitrary
  Nim code into types; the trust boundary is that *you* are the compiler
  plugin. Any Nim computation you run to produce or check an Eponym program
  (scripts generating surface text, compile-time helpers) is your own code
  with your own bugs — the guarantees in this document cover what the
  elaborator and kernel check, not what your metaprogramming computes.

## Summary of the trust boundary

| Checked for you | Your responsibility |
|---|---|
| Bidirectional elaboration + conversion (kernel re-checks, LCF-style) | Termination beyond single-function structural recursion (#42) |
| Eliminator iota rules (motive-validated by the kernel) | Universe discipline — `? : ?`, don't write paradoxes (#52) |
| QTT quantity discipline (linear used once, erased unused) | Termination of type-level computation (author's problem) |
| Structural recursion for `red` rules and clause defs (#36) | Soundness of `postulate`d primops (host `Int` ops) |
| Strict positivity of `data` declarations (#33) | Anything your own metaprogramming computes |
| Handler evidence revalidated LCF-style (#41) | |

Eponym's guarantee: a term that elaborates *and* passes the kernel was
checked by a small independent checker against QTT's judgments, with
quantities enforced, eliminators motive-validated, and recursion
structurally guarded — modulo the three documented deferrals above.
