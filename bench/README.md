# bench/ — benchmarks and measurement instruments

Most files here are one-off experiment benchmarks. The runtime benchmark
suite (issue #432) is the `bench_runtime_*` family:

- `bench_runtime_harness.nim` — shared harness: warmup, pilot-calibrated
  iteration counts (~1.5 s per path), ms/iter tables, speedup ratios.
- `bench_runtime_dps_vec.nim` — Vec DPS folds (`vmapDps`, `vappendDps`,
  `vlenDps`): interpreter vs Value backend vs repr backend.
- `bench_runtime_dps_list.nim` — List DPS folds (`lmapDps`, `lappendDps`,
  `lfilterNonZero`): same three paths.
- `bench_runtime_defheavy.nim` (+ `fixtures/defheavy_lib.ep`,
  `fixtures/defheavy_score.ep`) — definition-heavy program: `pipelineRep`
  (nested cross-definition Vec calls) compares interpreter vs repr
  same-block vs repr cross-block (the #408 registry pair, 1.00x on the
  reference run); `scoreOfRep` exercises the #402 derived `Score` mapping
  on the interpreter and Value paths (no repr row — the derived
  single-field-variant representation is outside the Phase-2 fragment).

## Running

Single command:

```
sh tools/bench-runtime.sh
```

or one driver directly (build flags are in each file's header):

```
nim c -r --path:src --path:src/eponym --path:tests --path:bench \
  bench/bench_runtime_dps_vec.nim
```

## When to use it

This suite is an **investigation tool, not a gate**. Run it when:

- you changed codegen and want to know whether the generated code got
  faster or slower end-to-end;
- you are evaluating an optimization (e.g. #413 q1-gated in-place reuse)
  and need the end-to-end number, not just the fragment benchmark;
- a compiled program feels slow and you want the per-path breakdown.

It is **deliberately absent** from `tools/ci-local.sh` and every GitHub
Actions workflow (issue #432 constraint). Verify: `grep -rn
"bench_runtime\|bench-runtime" tools/ci-local.sh .github/workflows/`
must print nothing.

## Reading the numbers

Each program prints one table: ms/iter per available path, then speedup
ratios in #19's framing (each compiled tier against the one below it,
plus compiled-vs-interpreter end to end). Paths a program does not
support are reported as unsupported with the tier-report reason —
absence of a row is data, not an omission.

Fairness discipline (AGENTS.md benchmarking), enforced by the harness:

- Args are built once, outside the timed loop, for every path.
- Elaboration is cached (`defCache`) and warmed before timing; the timed
  interpreter section is findDef + the ETT interpreter + result decode.
- Each driver header names what its paths actually do.
- The suite reports measurements, never verdicts. A surprising result
  gets profiled before it gets recorded anywhere as a conclusion.

## Known interpreter limits

The ETT interpreter recurses per list element, so List workloads need
`-d:nimCallDepthLimit=30000` in a debug build (the Vec driver does not).
The knob raises the debug-build safety rail only; it changes no
semantics. Stack depth scaling with input size is a property of the
interpreter worth knowing when reading the interpreter column.
