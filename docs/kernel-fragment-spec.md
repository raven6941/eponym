# Kernel fragment spec — the "kernel accepts" language (issue #62)

**Version:** v1 (2026-10-13)
**Implementation:** `src/eponym/kernel_check.nim` (≤ 500 lines)
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

## Accepted term forms (v1)

Pi, Sigma, Lam, Pair, App, Fst, Snd, Let, Absurd, `?`, `1`, `O`, `<>`,
variables (de Bruijn), and global references. Data type formers,
constructors, postulates, and eliminators are accepted as *neutrals*
(the kernel knows their types but not their definitions; eliminators
are flagged via `isElim`/`elimNargs`).

## Typing rules (v1)

- Bidirectional: `kInfer` synthesizes, `kCheck` checks.
- Lambdas synthesize from their domain annotation (`Pi(dom, bodyTy)`);
  the domain is itself checked against `?`.
- `<>` (cVoid) synthesizes `1` (cOne); `?`, `1`, `O` synthesize `?`.
- Conversion is type-directed with eta for functions; definitions
  delta-unfold during weak-head evaluation.
- Quantities, implicit/erased flags: accepted but not compared by
  conversion (the kernel audits the pure typing judgments; QTT usage is
  the elaborator's `checkUsage` pass, out of scope for v1).

## Fragment exclusions (v1) — raise, never pass

A term outside the fragment raises `KernelError("out of kernel
fragment: ...")`. Absence of a rule is a failure, never a silent
acceptance. The harness (`tests/kernel_audit.nim`) counts these as
SKIP, distinct from PASS and from DISAGREE.

- `tMeta`: the zonk invariant must hold before kernel checking.
- `tInt`, `tPrim` (Experiment 11 primops), `tNatLit` (issue #93).
- Fully-applied eliminator-headed neutrals encountered during
  conversion: v1 has no iota reduction. Detected via the `isElim` flag
  (not by failing the comparison), so iota-dependent programs are
  reported as not-yet-auditable rather than rejected.

## Audit protocol

`tests/kernel_audit.nim` elaborates every `.ep` file under `lib/`,
`examples/`, `examples/ep/` (fresh `ModuleDriver` per file; `*-neg.ep`
must be rejected by the elaborator), builds the kernel's globals from
`drv.globals` + `drv.allDefs` (imported definitions' bodies included),
and re-checks each definition with `kernelCheckDef`. Any DISAGREE
(elaborator accepted, kernel rejected) fails the suite.

## Current status (v1)

41 files, 55 definitions PASS, 32 SKIP (out of kernel fragment),
0 DISAGREE, 15 negative tests rejected as expected. The disagreements
found during development were all kernel bugs, fixed before v1
(see decisions.org #62): sigma-binder index adjustment (`kinst` not
`ksubstKeep` for pair/snd), fragment-error prefix unification, `<>`
typing, lambda synthesis.

## Known limitations / next versions

- v2: eliminator iota (the largest skip class: 24 of 32 skips).
- v2: `tNatLit` expansion (issue #93), `tInt`/`tPrim` primop semantics.
- The kernel is more permissive than the elaborator in one direction
  (ignores quantities in conversion); it cannot catch elaborator bugs
  that only manifest as quantity misuse. Usage checking stays with
  the elaborator.
