# Issue #103 corpus: elaboration failure sites requiring human repair

Each entry is a place where the corpus as first written did not elaborate
(or parse) and a human had to change the source. Parse errors count: the
surface grammar is part of the annotation-burden story (a keyword collision
forces a rename just as surely as a missing ascription).

## Baseline (2026-10-15)

- [x] `lam` is a reserved surface keyword (the lambda introducer), so the
  object-language constructor `lam` in `stlc_syntax.ep` / `typing.ep` did not
  parse (`expected '.', got ')'`). Renamed to `abs` (and `tLam` to `tAbs`).
  Divergence from Agda/Lean idiom: there `lam` is a legal constructor name.
- [x] `import "../../lib/nat.ep"` from `examples/ep/corpus103/` resolved to
  `examples/lib/nat.ep`: imports resolve relative to the importing file, so
  the deeper directory needs `../../../lib/...`. Authoring repair, not a
  language divergence.

Elaboration failures after parsing: none — all four files elaborated on the
first attempt, including both weakening lemmas (no extra ascriptions needed;
`append`-on-`cons` reduces definitionally by iota, so no rewriting).
