# Shed state DAG test plan

This plan is the acceptance checklist for VS Code state-addressed shed editing
(#451). Keep #451 open until the automated checks and the manual scenarios below
pass on the implementation branch. The UI smoke scenario is deliberately
multi-step: a single successful `refine` does not cover state selection,
cross-shed targeting, branching, or local undo.

## State machine invariants

| Area | Action | Expected result |
| --- | --- | --- |
| Identity | Build equal states twice; vary source, goal, environment, schema, and action inputs | Equal canonical inputs have equal IDs; any changed input in the identity domain changes the relevant ID. |
| Integrity | Supply malformed node data and content under the wrong digest | The server rejects it before checking or caching it. |
| Declaration | Declare a state with all nodes, then with shallow references | Both declarations resolve to the same root and goal IDs. |
| Cache miss | Evict a referenced node, request a transition, transfer the requested closure, retry | The first response identifies missing nodes; retry succeeds without resending known nodes. |
| Bounded cache | Insert more nodes than the configured limit | Cache size remains bounded; eviction affects transfer cost only. |
| Restart | Restart the LSP with a client-held root | Re-declaration/rehydration restores the state and allows a checked successor. |
| Hypothetical transition | Run an action from `(stateId, goalId)` | Response names a distinct checked successor and its edits/nodes; no server-selected active root or pending commit is created. |
| Multiple roots | Continue once from a parent and once from its successor | Both requests succeed independently; the server does not assume which root the client selected. |
| Multiple goals | Refine one goal in a two-goal state | All untouched sibling goal IDs and records survive; residual child goals have new stable IDs. |
| Goal lifecycle | Complete a goal, then query it through the successor and through its parent | It is no longer actionable in the completed successor; the same goal ID remains actionable through the historical parent and can produce an alternate successor. |
| No server disk effects | Create/query/transition states and exercise cache recovery | Hypothetical server operations do not write Nim source or `.sheds.json`. |

Automated evidence lives in `src/experimental/shed_state_dag_probe.nim` and
`src/experimental/shed_state_actions_probe.nim`. Re-run both after any change to
state encoding, cache, request handling, checker validation, or restored layout.

## VS Code client and editor checks

Run against the Extension Development Host launched from
`editors/vscode/.vscode/launch.json`, with its host workspace set to the
worktree root and `examples/embedded/sheds_walkthrough.nim` open. Confirm the
branch in the host status bar before editing. Build the extension and LSP from
the same worktree. Do not save temporary inline preview text as part of these
checks.

| Scenario | Steps | Expected result |
| --- | --- | --- |
| Initial state/layout | Expand `quadBody` at its marker | The layout displays the restored open `Int` hole with a hole ID; it does not say “no open holes”. |
| Refine continuation | Refine `quadBody` with `double ( ? )`, then refine its residual goal with `double n` | Both transitions succeed; the second request uses the first successor and its residual goal ID. The final selected state closes `quadBody`. |
| Cross-shed continuation | From the selected state, move to `addThreeBody`; refine with `add (add n 3) 3` | The action targets `addThreeBody` in the selected root, leaves other goals addressable, and reports no stale document, unknown state, pending commit, or method-not-found error. |
| Case split | Select `isZeroBody`, case-split on `n` | A successor contains the zero and successor clause goals, retains unrelated open sheds, and renders both clause holes. |
| Local undo + alternate refinement | Immediately Undo the case split, then refine the restored `isZeroBody` with `false` | Undo selects the prior local root without an LSP request; the alternate refine succeeds from that root. The case-split successor remains available as a redo/history branch. |
| Act on a goal from history | Complete `quadBody`, keep the successor selected, choose `quadBody` from the shed panel's goal picker, and refine it from that historical layout | The client sends the earlier `(stateId, goalId)` without changing the selected root or editor buffer. The checked successor is stored as a local branch; select that successor in History to adopt its document text. Ambiguous historical roots require an explicit History choice. |
| Redo branch | Redo/select the saved case-split successor | The client selects the known successor locally and the two clause goals return. |
| Two goals in one shed block | Select `branchLeft`, refine with `add ( ? ) ( ? )`, then switch to `branchRight` and give `n` | The successor contains both residual left goals and `branchRight`; targeting the sibling preserves the residual goals. No sibling-state overwrite occurs. |
| Alternate branch | Return locally to the branch demo parent, refine `branchLeft` with `n`, then inspect History/Redo | The new successor is a sibling branch; the earlier `add` successor is still selectable and redo can choose between them. |
| Same-file shed switching | Switch repeatedly among `quadBody`, `addThreeBody`, `isZeroBody`, and the branch demo, issuing actions after each switch | Every action uses the currently selected root plus the chosen goal ID. There is no document-wide pending transition, and selecting one shed does not silently reset another branch. |
| Source conflict | Make an unrelated editor change after recording a successor, then select/apply a stored state | The client reports the source revision conflict, keeps the selected proof state/history, and does not overwrite the unrelated edit. |
| Save boundary | With Auto Save disabled, transition to a selected source projection, switch sheds/open the layout, then inspect disk; explicitly save afterward | Selecting a successor may update the editor buffer. Opening/switching views and compiling a sidecar must not save that dirty buffer as a side effect. Explicit save persists the selected projection and regenerates metadata as needed. If Auto Save is enabled, VS Code may persist the selected buffer according to its setting. |

## Keyboard-only interaction checks

Run the same multi-shed walkthrough without clicking editor, CodeLens, webview,
or picker controls. Use the keyboard to focus each surface and confirm focus
and resulting state in the UI. On macOS, VS Code displays `⌘` where Windows and
Linux use `Ctrl`.

| Scenario | Keyboard path | Expected result |
| --- | --- | --- |
| Open/collapse | Put the cursor on a marker; `Ctrl+Shift+S` opens it; `Escape` collapses it | The inline view opens for the cursor's shed and collapse removes only the preview. |
| Refine continuation | With inline view focused, press `r`, type `double ( ? )`, press `Enter`; navigate to the residual marker, reopen, press `r`, type `double n`, `Enter` | Both checked transitions succeed from their selected successor, and the final goal closes. |
| Cross-shed | Move the editor cursor to `addThreeBody` with keyboard navigation; expand; `r`, type `add (add n 3) 3`, `Enter` | The action targets the selected goal in the current root; no stale-state or pending-commit error. |
| Case split | Navigate to `isZeroBody`; expand; press `c`, type `n`, `Enter` | Both constructor goals are created and visible. |
| Undo + alternate refinement | Focus the shed webview with VS Code focus navigation; Tab to Undo and press `Enter`; select `isZeroBody` through its picker with type-to-select and `Enter`; Tab to Refine, enter `false`, activate Refine | Undo selects the prior root locally; the alternate branch is checked and the case-split branch remains in History. |
| Redo/history branch selection | Tab to Redo and press `Enter`; where a QuickPick appears, filter by action/goal text and press `Enter`; use History similarly to choose the other branch | The chosen root becomes selected and its open goals return; no server commit round-trip is needed. |
| Historical goal action | With a later state selected, focus the shed picker, type `quadBody` to select its historical layout, then Refine with a different valid term | The historical `(stateId, goalId)` is queried while the editor and selected root stay put; History lists the new successor for local adoption. |
| Multiple goals | Navigate to `branchLeft`; expand; press `r`, enter `add ( ? ) ( ? )`; then navigate to `branchRight`, expand, press `g`, enter `n` | Residual left goals remain selectable after refining the right sibling. |
| Keyboard scope safety | With no inline view active, press `i`, `r`, `c`, and `g`; then repeat with the view active and editor focused | Unbound actions do not type into source when inactive; active actions open the expected input/action flow. |
| Native editor undo/redo | After adopting a successor, press VS Code's normal Undo (`⌘Z` on macOS, `Ctrl+Z` elsewhere), then Redo | When the buffer matches a known local snapshot, the client follows that parent/child proof root immediately; the next shed query and refinement must use that root without a server adoption round-trip. |

The current manifest binds `Ctrl+Shift+S`, `Escape`, `i`, `r`, `c`, and `g`.
Undo, Redo, and History currently have keyboard access through the webview's
Tab order and QuickPick controls, but no dedicated global shortcut. Do not
count the earlier pointer-driven scenarios as keyboard evidence.

For every transition, note the selected state ID and target goal ID from client
history/debug output when available. A success toast by itself is not sufficient
for branch cases: verify the expected sibling/residual goals in the refreshed
layout and verify the source/sidecar boundary on disk.

## Current evidence

- [x] VS Code build, headless inline tests, and extension smoke test pass. The
  smoke test needed a temporary Nim cache under `/private/tmp` because the
  existing default cache failed to open a generated C file.
- [x] Nim LSP compiles with `nim c` (stdio server; do not use `nim c -r`).
- [x] Action probe covers `refine`, `give`, `caseSplit`, `intro`, `construct`,
  `apply`, and `rewrite`, including continuation from a refine successor.
- [x] State DAG probe covers digest verification, sibling preservation,
  missing-node recovery, bounded cache, restart recovery, local root selection,
  and unchanged fixture/sidecar bytes.
- [x] Live host: `quadBody` refinement with `double ( ? )` returned a yellow
  checked successor instead of the prior “Method not found” error; refining
  the residual goal with `double n` closed it.
- [x] Live host: switched to `addThreeBody` in the same file and refined it;
  no stale-document, pending-commit, or method-not-found error occurred.
- [x] Live host: case-split `isZeroBody` on `n`; locally undid; chose the
  alternate `false` refinement; then selected the case-split branch again and
  verified both clause goals returned.
- [x] Live host: refined `branchLeft` into two goals, switched to `branchRight`
  and gave `n`; the two left goals remained available. A separate `branchLeft`
  refinement remained as a sibling history branch.
- [x] Native editor Undo restores a known source snapshot and the client follows
  its matching parent root. After undoing a completed `quadBody`, a different
  refinement from the restored goal succeeded in the rebuilt live host.
- [x] Server action and DAG probes confirm hypothetical operations do not
  change source/sidecar bytes.
- [x] Keyboard smoke: webview Undo, History QuickPick filtering/selection, and
  shed-picker type-to-select worked without pointer input. Case-split on a
  child goal was correctly rejected as inapplicable. The rebuilt host showed
  that a queued selection event from the Eponym Output editor was clearing the
  inline view while the walkthrough editor remained active. The handler now
  ignores inactive-editor events. Re-tested `Ctrl+Shift+S`: the preview stayed
  expanded through repeated Output events. Then keyboard `r` + `double ( ? )`
  and `r` + `double n` succeeded; the latter returned white with 7 open goals.
- [x] Keyboard smoke: expanded `isZeroBody`, case-split on `n`, undid back to
  the original marker, then switched to `addThreeBody` and refined it. The
  `addThreeBody` action succeeded from the restored state with six open goals.
- [x] Keyboard History/Redo branch choice: from the walkthrough's initial
  state, keyboard refinement of `branchLeft` with `add ( ? ) ( ? )` created
  one successor. Keyboard History selected the parent; keyboard give of `n`
  to `branchRight` created a second successor. History showed both actions.
  Keyboard History adopted the `give branchRight` successor, Undo returned to
  the parent, and keyboard Redo QuickPick selected `give branchRight`; after
  another Undo, Redo selected `refine branchLeft`. The selected shed and goal
  changed with each adoption. The current VS Code 1.143.1 host loaded the
  panel normally; the prior Service Worker failure was isolated to the older
  host and also affected built-in Markdown Preview. Temporary unsaved
  walkthrough edits were discarded after the live check.
- [x] Keyboard case-split follow-up: after rebuilding, `c` + `n` adopted the
  checked successor and showed both branch goals. Native Undo restored the
  pre-split root, and a different keyboard refinement from `caseGoal` produced
  an alternate successor.
- [x] Save-boundary regression investigation found that `ensureSidecar`
  implicitly saved dirty documents. The client now refuses that implicit save
  and uses the selected local DAG for existing histories.
- [x] Live save-boundary check on disposable `shed_save_boundary_valid.nim`:
  opening the layout and creating a `giveGoal` successor left the source and
  sidecar disk hashes unchanged. Selecting that successor changed the editor
  buffer from `![giveGoal]` to `zero` while disk stayed unchanged. Explicit
  Save then changed both hashes and regenerated the sidecar without
  `giveGoal`. The disposable fixture and sidecar were removed after the check.
- [x] Goal lifecycle probe: a completed goal is rejected in its successor,
  while the immutable parent remains queryable and can produce a distinct
  alternate successor.
- [x] Client history tests verify historical goal resolution, the layout path
  sends the exact historical `(stateId, goalId)`, an all-known-goals picker
  model, ambiguous-root rejection, and successor adoption only when its exact
  parent remains selected and displayed.
- [x] Targeted Nim suites passed: LSP holes/actions, sheds/layout/loop, refine
  method, semantic action history/discovery, and refine round-trip. The
  walkthrough also compiled and ran directly, reporting all eight yellow sheds.
- [x] `tests/run_examples.nim` passed in full using a temporary Nim cache under
  `/private/tmp`.
- [ ] `tests/run_embedded_examples.nim`: all examples passed except
  `paxos_session.nim`, which cannot bind `127.0.0.1` in this sandbox
  (`Operation not permitted`). Re-run where loopback sockets are permitted.
  The affected-test wrapper also did not get past its `nimble path falsify`
  prerequisite because Nimble hung.
- [x] Shed webview startup: a clean document opens a rendered Shed panel with
  its goal picker, layout, and action controls in VS Code 1.143.1. The extension
  now installs a usable HTML shell before awaiting the first asynchronous
  layout request, so a failed request can display its error instead of leaving
  an empty panel. The earlier “state environment changed; initialize a fresh
  shed state” message came from the dirty test buffer and disappeared after
  discarding it and reopening the on-disk walkthrough.
- [x] Live historical completed-goal workflow: in the rebuilt host, created a
  `give historicalGoal` state (`zero`), selected it, then used the shed picker
  to display `historicalGoal` from the initial state and refined it with
  `suc zero`. The client reported the result stored in History while the
  `give` projection remained selected during that historical action. Selecting
  the returned refinement in History adopted its source projection; after
  closing the Shed panel, the editor showed `historicalTarget(): Nat = suc zero`.
  The temporary fixture remained unsaved and was removed with its sidecar and
  binary.
- [x] Extension `npm run build` and `npm run test:headless` pass after the
  dirty-buffer save-boundary change.
- [x] Extension `npm run smoke` passes against `sheds_demo.nim` and the current
  eight-shed walkthrough; it checks generated sidecar names, layouts, inline
  rendering, and legacy action behavior.
- [ ] CI merge gate: run `sh tools/ci-local.sh` before opening a PR. It was
  attempted with an isolated cache, but stalled at its initial `nimble path
  falsify` dependency check; a 10-second direct retry also timed out, so the
  full CI matrix did not start.
- [x] Resolved the resumed live-host issues on clean fixtures: the rebuilt host
  collapses the inline preview, adopts keyboard transitions, switches to a
  sibling shed, and follows native Undo. The earlier malformed `quadBody`
  buffer was left unsaved; repeat the actual walkthrough case from a clean
  buffer before counting that scenario complete.
- [x] Inline preview collapse: in the rebuilt host, `Ctrl+Shift+S` on a clean
  fixture inserted the preview; Escape restored the exact original source
  text. No fixture changes were saved. The separate disk save-boundary check
  is recorded above.
- [x] The `goal ... is not open in any locally known proof state` client error
  is not a server-wide active-goal latch. State-addressed queries use an exact
  `(stateId, goalId)` pair, and the client searches its local history for a
  state containing that open hole. A solved goal needs a reference to an older
  state where it is still a hole; replacing a proof in a state where it is
  closed would need a distinct replace/reopen operation.
- [x] Reproduced `quadBody` against the freshly generated walkthrough sidecar
  using the state-addressed `transitionShedState` request with
  `double ( ? )`. The returned source line is
  `proc quad(n: Int): Int = double ( double ( shedHole(quadBody) ) )`; the
  server splice is well-formed and left the walkthrough and sidecar unchanged.
  Extension build and headless inline/history suites pass after updating the
  client error text to describe a missing state reference instead of a global
  “open” requirement. Subsequent rebuilt-host checks passed on clean fixtures;
  the complete walkthrough `quadBody` interaction is recorded below.
- [x] After the memory recovery, used the clean `shed_state_actions_fixture.nim`
  in the rebuilt Extension Development Host. `Ctrl+Shift+S` expanded
  `giveGoal`; Escape removed the preview and restored the exact editor source.
  Then native Undo restored the parent marker for `giveGoal`, and keyboard
  `r` + `zero` produced a successful completed successor. This confirms
  collapse, local undo, and a different refinement after undo in the rebuilt
  client without saving the fixture buffer.
- [x] In the same rebuilt host, keyboard-opened `caseGoal`, used `c` + `n`, and
  observed the checked successor adopted into the editor as
  `natElim(lam(u: Nat) => Nat, ![caseGoal_zero], ![caseGoal_suc], n)`. Both new
  branch goals appeared in the shed picker and the notification reported two
  open goals.
- [x] Native Undo immediately restored the pre-split `caseGoal` marker; opening
  that historical goal and using keyboard `r` + `zero` then produced a distinct
  completed successor. The editor showed the original `caseGoal` source after
  Undo and the client accepted the alternate action.
- [x] Keyboard-only multi-goal sequence on a clean same-line sibling fixture:
  refined `branchLeft` with `suc(?)`, opened `branchRight`, then gave it `zero`. The
  editor adopted `add ( suc(shedHole(branchLeft)) ) ( zero )` and reported
  one remaining open goal. `zero()` is invalid Eponym term syntax for a
  nullary constructor (the parser rejects the closing parenthesis), so the
  keyboard input prompts now show Eponym examples `zero` / `suc zero`; Give
  parse failures are labeled as Give failures.
- [x] On a clean walkthrough buffer in the rebuilt host, keyboard `r` +
  `double ( ? )` accepted the first `quadBody` refinement and `r` + `double n`
  completed its residual hole. The server reported `white (7 open goals)` and
  the buffer showed `double ( double ( double n ) )`. The test buffer was
  closed with “Don't Save”; the worktree's walkthrough source remains at its
  original `shedHole(quadBody)` state and the sidecar was not changed.
  Historical completed-goal picker and successor adoption are recorded above.
