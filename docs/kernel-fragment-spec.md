# Kernel fragment spec — the "kernel accepts" language (issue #62, v2: #156)

**Version:** v2 (2026-10-13)
**Implementation:** `src/eponym/kernel_check.nim`
**Harness:** `tests/kernel_audit.nim`

The independent audit kernel re-checks every elaborated core term
LCF-style: the elaborator (`elab.nim`) is the untrusted producer, the
kernel the auditor. This document versions the exact core language the
kernel accepts, so "audited" has a precise meaning that can evolve.

## Shared with the elaborator

- The `Term` syntax (`eponym_init.Term`) — it is the artifact being audited.
- Nothing else. Substitution, weak-head evaluation, conversion, and the
  bidirectional judgments are re-implemented from scratch. The cached
  `Value` fields (`refTyp`, `refVal`) in `tR` nodes are treated as
  untrusted hints and never consulted; the kernel takes its own
  `KernelGlobals` table (name → type + definition body).
- Elaborator-produced *data* (not logic): definition bodies, iota rule
  tables (contractum templates via `redRuleInfo`), and the refIds of
  `zero`/`suc`/`Int`. The kernel re-implements every judgment over this
  data and validates each iota rule against its motive (below).

## Accepted term forms (v2)

Pi, Sigma, Lam, Pair, App, Fst, Snd, Let, Absurd, `?`, `1`, `O`, `<>`,
variables (de Bruijn), global references, `tInt`/`tPrim` (Experiment 11
primops), `tNatLit` (issue #93), and fully-applied eliminator-headed
neutrals (iota reduction, see below).

## Typing rules (v2)

- Bidirectional: `kInfer` synthesizes, `kCheck` checks.
- Lambdas synthesize from their domain annotation (`Pi(dom, bodyTy)`);
  the domain is itself checked against `?`.
- `<>` (cVoid) synthesizes `1` (cOne); `?`, `1`, `O` synthesize `?`.
- Conversion is type-directed with eta for functions; definitions
  delta-unfold during weak-head evaluation.
- **Iota** (`kwhnfElim`): an eliminator applied to `elimNargs` arguments
  whose scrutinee (last argument) weak-head-evaluates to a
  constructor-headed neutral with a validated rule fires: the contractum
  template is instantiated with the elim args and constructor args
  (the elaborator's `fireRed` spine convention, re-implemented) and
  reduction continues. Under-applied eliminators and stuck scrutinees
  stay neutral. Every rule is validated first (see below).
- **Nat literals** (`kExpandNatLit`): `tNatLit(n)` is definitionally
  `suc^n(zero)`, expanded with the kernel's own `zero`/`suc` globals
  (issue #93's semantics, re-implemented; the elaborator's O(1) fast
  path plus `numeralChainEq` fallback are replaced by uniform expansion).
- **Primops** (`kwhnfPrim`, `kInfer`): the kernel's axiom is that primops
  are binary `Int -> Int -> Int` operations. The elaborator's claimed
  `primTy` is *verified* against the kernel's own axiom type, not
  trusted. A fully-applied primop fires on two `tInt` args via host
  arithmetic; otherwise it stays neutral.
- Quantities, implicit/erased flags: accepted but not compared by
  conversion (the kernel audits the pure typing judgments; QTT usage is
  the elaborator's `checkUsage` pass, out of scope).

## Iota rule validation: the motive check (v2)

`elabRedDecl` elaborates each `red` contractum in inference mode only --
"the rule is trusted, like an axiom". The kernel does not trust it
(`validateElimRules`, run by the harness before auditing):

- From the eliminator's Pi type in the kernel's globals: the argument
  types `A_1..A_n` and result type `B` (`n = elimNargs`).
- From the constructor's Pi type: the telescope types (leading `nParams`
  instantiated with the eliminator's param variables) -- this rebuilds
  the template's context `[w_m..w_1, a_{n-1}..a_1]` independently.
- Index discovery: the scrutinee type is the family applied to
  `(params.., index vars..)`; the constructor's return type is the family
  applied to `(params.., index exprs..)`. Leading params must match
  syntactically; each index variable maps to its index expression.
  (Motive-headed hand-written eliminators take the naive path: no indices.)
- The template is then *checked* against `B` with the scrutinee replaced
  by the constructor spine and each index variable replaced by its index
  expression.

A rule failing this check is an audit disagreement (triaged, never
silent). A rule whose shape cannot be discovered raises a fragment
error instead, so dependent definitions SKIP honestly.

## Fragment exclusions (v2) — raise, never pass

A term outside the fragment raises `KernelError("out of kernel
fragment: ...")`. Absence of a rule is a failure, never a silent
acceptance. The harness (`tests/kernel_audit.nim`) counts these as
SKIP, distinct from PASS and from DISAGREE.

- `tMeta`: the zonk invariant must hold before kernel checking.
- `tNatLit` with no `zero`/`suc` registered; `tInt`/`tPrim` with no `Int`
  registered: the kernel cannot know which globals the literals belong to.
- Iota rules whose shape the kernel cannot discover (non-`data`
  indexed eliminators, param mismatches): marked invalid, their use
  raises a fragment error.

## Audit protocol

`tests/kernel_audit.nim` elaborates every `.ep` file under `lib/`,
`examples/`, `examples/ep/` (fresh `ModuleDriver` per file; `*-neg.ep`
must be rejected by the elaborator), builds the kernel's globals from
`drv.globals` + `drv.allDefs` (imported definitions' bodies included),
validates every iota rule against its motive, and re-checks each
definition with `kernelCheckDef`. Any DISAGREE (elaborator accepted,
kernel rejected -- or an iota rule failed the motive check) fails the
suite.

## Current status (v2)

41 files, 87 definitions PASS, 0 SKIP (out of kernel fragment),
0 DISAGREE, 15 negative tests rejected as expected. The v1 skips
(24 eliminator-iota, 8 primop/nat-literal) are all genuinely audited
now. No iota rule in the corpus failed the motive check.

## Known limitations / next versions

- The kernel is more permissive than the elaborator in one direction
  (ignores quantities in conversion); it cannot catch elaborator bugs
  that only manifest as quantity misuse. Usage checking stays with
  the elaborator.
- `tNatLit` uses uniform expansion rather than the elaborator's O(1)
  literal fast path: very large literals would build large suc-chains.
  (A `numeralChainEq`-style comparison is the natural follow-up if
  large literals ever appear in the corpus.)
- The kernel does not check structural recursion of `red` rules
  (issue #36 does that at declaration time); a diverging rule would hit
  the kernel's reduction fuel limit and SKIP honestly.
