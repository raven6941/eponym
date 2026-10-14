# Adequacy contract for elaboration (issue #38)

Version: 2026-10-13. Elaborator: bidirectional `checkTm`/`inferTm`
(Experiment 3 onward, with QTT quantities from #66 and literal
overloading from #93).

Twelf's adequacy methodology — an encoding must be a compositional
bijection between object-language entities and canonical forms — stated
as a *tested* contract on the surface→core boundary. A failing property
points at exactly the phase boundary that broke. Tested by
`tests/adequacy_props.nim` (fixed seed `20261013`, run in CI).

## The contract

**P1 — Totality in checking mode.** Every well-scoped surface term
elaborates when checked against its type. (Inference is intentionally
partial — see P6.)

**P2 — Compositionality.** Elaboration is a homomorphism on term formers:
- `elab(lam(x,A,t))` is `tLam` whose domain is `elab(A)` and whose body is
  α-equal to `elab(t)` under the context extended with `x`;
- `elab(app(f,x))` is α-equal to `app(elab(f), elab(x))`;
- `elab(fst(p))` is α-equal to `fst(elab(p))`.

**P3 — Substitution commutation.** For open `t` (over `x`) and closed `u`:
`elab(substPre(t,x,u))` is α-equal to `subst(elab(t), 0, elab(u))`.

**P4 — Surface round-trip.** Rendering a surface term to text (`$`),
re-parsing, and re-elaborating yields an α-equal core.

**P5 — Injectivity on numerals.** Distinct numerals elaborate to
non-α-equal cores (so a degenerate elaborator cannot pass P1–P4).

**P6 — Intentional partiality of inference.** Integer literals are
checking-only constructs (like `by` tactics): a literal in inference
position is *rejected*, not defaulted. The suite pins the rejection.

α-equality here = structural equality on core `Term`s, ignoring binder
*names* (de Bruijn indices carry binding) but including
impl/erased/quantity flags and global refIds.

## Known boundary limitations

- **The literal `1` has no surface form** (issue #158): `1` lexes as the
  unit *type* (QTT), so `pkInt(1)` cannot be written in text and the
  renderer (`$`) is unfaithful exactly there. P4 skips `pkInt(1)` terms
  (counted in the output) until #158 is decided.
- **Literals need expected types.** The generator is mode-aware:
  function-position terms (application infers its function) are
  literal-free transitively; checked positions may use literals. This
  mirrors the elaborator's checking/inference discipline rather than an
  idealized "every well-scoped term elaborates" claim.

## Sanity

A deliberately injected bug (surface `substPre` skipping the application
argument) fails exactly the P3 properties (57/300) and nothing else;
reverting restores green. The suite bites at the right boundary.
