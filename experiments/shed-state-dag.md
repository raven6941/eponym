# Shed state DAG feasibility probe (#450)

## Result

The prototype passed the narrow two-goal refine scenario from #450. The
fixture has two single-line open sheds in one `eponymBlock`. `refineShedPlan`
checks `double ( ? )` against the real Eponym checker and returns a state with
one residual goal. The sibling remains yellow and retains the same stable goal
ID. The residual goal ID is derived from the parent root, action, target goal
ID, and child ordinal.

The planner is in-memory. The probe compares the fixture and sidecar contents
before and after the query; neither changed. A cache with the sibling goal node
evicted reports that node ID as missing. Supplying that node from the client
cache makes the successor closure available again. A node whose content was
modified while retaining its old digest is rejected. Local undo/branch
selection is represented by switching the selected root between the retained
parent and successor, without calling the server.

SHA-256 matches the standard empty-string and `abc` vectors. For the fixture,
the canonical encodings for nodes absent from the parent cache total 1,570
bytes; the full parent snapshot totals 1,928 bytes. This is only a transfer
feasibility comparison for this fixture, not a performance benchmark.

## Reproduce

From the repository root, first compile the fixture to generate its sidecar,
then run the probe:

```sh
nim c --hints:off --nimcache:/tmp/eponym-probe-fixture-cache \
  -o:/tmp/eponym-probe-fixture --path:src --path:src/eponym \
  examples/embedded/shed_state_dag_probe_fixture.nim
nim c -r --hints:off --nimcache:/tmp/eponym-probe-harness-cache \
  --path:src --path:src/eponym --path:src/experimental \
  -o:/tmp/eponym-shed-state-probe \
  src/experimental/shed_state_dag_probe.nim \
  examples/embedded/shed_state_dag_probe_fixture.nim
```

The fixture compilation writes the ignored `.sheds.json` sidecar next to the
fixture. The probe itself only reads it and does not write the fixture or
sidecar.

## Production action integration probe (#451)

The feature-surface probe in `shed_state_actions_probe.nim` uses a separate
embedded fixture with goals for all seven action IDs. It queries and executes
Refine, Give, Intro, Construct, Apply, Case-split, and Rewrite through the
state-addressed LSP methods. Every action returned a distinct checked
successor root, and the fixture and sidecar were byte-identical before and
after the requests. The probe continued from a Refine successor containing
residual `shedHole(name)` markers while retaining its parent root. It also
exercises node recovery through the actual LSP request path. The walkthrough
fixture compiles with two independent open goals in one `eponymBlock`.

Reproduce the action probe after compiling its fixture:

```sh
nim c --hints:off --nimcache:/tmp/eponym-actions-fixture-cache \
  -o:/tmp/eponym-actions-fixture --path:src --path:src/eponym \
  examples/embedded/shed_state_actions_fixture.nim
nim c -r --hints:off --nimcache:/tmp/eponym-actions-probe-cache \
  --path:src --path:src/eponym -o:/tmp/eponym-actions-probe \
  src/experimental/shed_state_actions_probe.nim \
  examples/embedded/shed_state_actions_fixture.nim
```

## Limits

The VS Code TypeScript build, inline-shed headless tests, VS Code smoke test,
LSP compilation, embedded walkthrough compile/run, both LSP probes, and the
manual Extension Development Host walkthrough have passed. The live check
also confirmed keyboard History/Redo selection between sibling successors.
The current environment fingerprint includes Nim version, `NIMFLAGS`, checker
source hashes, quoted import content, and document URI; project-level Nim
config and import search resolution are not yet included. The server cache
uses LRU by node count (4096), not bytes, and does not pin roots during
requests; cache misses remain recoverable, but large states may require extra
transfer rounds.
