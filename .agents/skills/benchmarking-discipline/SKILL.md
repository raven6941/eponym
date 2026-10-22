---
name: benchmarking-discipline
description: Use when measuring performance, drawing a conclusion from a benchmark, or closing an issue on performance evidence. Covers fair-baseline verification, why a first measurement is a draft, and profiling surprising results before recording a verdict.
---

# Benchmarking discipline

Performance conclusions in this repo have twice been wrong because the
comparison was quietly unfair. These rules are the repair.

## Verify the comparison is fair before trusting the number

Two historical failures, same shape:

- #26: "staged" code still built goal closures run by the miniKanren
  engine — specialization without codegen. Not evidence against
  staging; incomplete staging.
- #53: a defunctionalized `apply` re-interpreted syntax on every call,
  against a baseline of pre-compiled host closures. Not evidence
  against defunctionalization; a representation change mistaken for an
  optimization.

Before recording any conclusion, name the actual work each side does
and check that neither side is re-doing work the other amortized:
re-walking syntax, rebuilding closures, re-rendering keys,
re-elaborating, materializing through a boxed `Value` layer the other
side avoids. If one side crosses a codec or interpreter boundary the
other doesn't, the benchmark measures the boundary, not the technique.

## A first measurement is a draft

- Do not close an issue on the first benchmark. Before closing, answer:
  *do I understand why the number is what it is?* #53 was closed on
  wall-clock alone; the profiling that found the real mechanism only
  happened after the verdict was challenged.
- Surprising results get inspected, not just recorded. When a result
  surprises (87× slower staged, 1.9× slower defunctionalized): profile
  with isolated micro-benchmarks, dump the generated code or IR,
  examine what the specializer actually produced. Mechanism inferred
  from code reading has been right about the culprit and wrong about
  the proportions; measurement corrects it.
- Separate compile time from run time when reporting numbers, and say
  which machine/cache state produced them (cold vs warm nimcache has
  changed suite timings by minutes, not percents).
- Prefer differential correctness first, speed second: a faster path
  that disagrees with the naive reference on any generated case is a
  bug report, not a speedup.
