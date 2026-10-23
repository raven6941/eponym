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

## Programs the suite does not time, and why (issue #432 slice 3)

Issue #432 named four representatives: the DPS fold workloads (timed
above), the definition-heavy program (timed above), the Paxos pipeline,
and the DCP logistic-regression demo. The last two have no executable
eponym program to time, so they appear here as explicit non-coverage
rather than as rows. Absence of a driver is data, not an omission.

- **Paxos** (`examples/embedded/paxos_session.nim`): the pipeline's
  per-round work is loopback-TCP socket I/O (`runPaxosRound` blocks on
  `recv` in every phase). Wall-clock on it would measure socket latency,
  not generated-code quality — the interpreter and the repr backend would
  differ by the noise floor of loopback, which says nothing about the
  codegen story this suite exists to check. Correctness across paths is
  covered by `tests/test_require_compiled_paxos.nim` (real TCP rounds
  through the compiled wrappers). If Paxos ever grows an in-memory
  variant, that variant belongs in this suite.
- **DCP logistic regression** (`examples/embedded/convex_opt_vec.nim`):
  the eponym block is proof layer only — datatypes, postulates, and proof
  terms; it defines no executable functions (`grep 'def \|fn '` over the
  block finds nothing). The executing logistic regression
  (`lrProbRuntimeValue`) is plain Nim, outside the eponym execution
  paths entirely, so there is no interpreter/Value/repr comparison to
  make. The proof layer's measurement instrument is the compile-time
  regression tracker (#376), not this suite. If the objective function is
  ever written as an executable eponym program, that program belongs here.
