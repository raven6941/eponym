# Content-addressed shed proof states

The implementation acceptance matrix and manual VS Code walkthrough are in
[`shed-state-dag-test-plan.md`](shed-state-dag-test-plan.md).

Status: implemented for the VS Code state-addressed shed editing path (#451),
following the design in #449 and feasibility probe in #450.

## Ownership and invariant

The client owns the selected proof-state root and its local history. The LSP
answers hypothetical requests of the form `evaluate(stateId, goalId, action)`
and returns a checked successor root. A response does not select that root for
the client. The client can select any root it already knows, including a
parent, immediately and without a server round trip. The LSP does not maintain
an active root or a document-wide pending action/commit.

An ID is a content address, not evidence that content was checked. A node
supplied by a client is untrusted until its canonical encoding and digest have
been verified; a transition is not trusted until the checker has validated its
result under the named environment.

## Canonical state DAG

All digests are SHA-256 of a versioned, domain-separated canonical encoding.
Strings are UTF-8 byte strings with explicit lengths. Integers use a specified
fixed-width big-endian encoding. Sequences include an element count. Maps are
encoded in sorted-key order. The wire format carries the schema version and
node kind. A digest is `SHA256(domain || version || encoding)`; changing the
schema requires a new version/domain.

The prototype node kinds are:

| Node | Canonical payload |
| --- | --- |
| `SourceLeaf` | Exact source bytes for a bounded chunk, including line endings |
| `SourceBranch` | Left and right child digests and byte lengths |
| `GoalRecord` | Stable goal ID, display name, goal term, ordered context, status, and source span/anchor |
| `GoalSet` | Goal-record digests sorted by stable goal ID |
| `Environment` | Nim/Eponym checker version, prelude and imported-source fingerprints, relevant options and working-directory identity |
| `ProofState` | Source root, goal-set root, environment root, and schema version |
| `Transition` | Parent root, action kind, target goal ID, canonical arguments, successor root, and checker version |

The source tree is lossless: reconstruction reproduces exact bytes. Branches
are balanced deterministically from ordered leaves so the same source and
chunking produce the same root. Goal IDs persist when an action retains a goal;
new goals receive deterministic IDs derived from the parent root, canonical
action, target goal ID, and stable action-local ordinal. (This avoids a cycle:
the transition ID also includes the successor root.) Goal display names remain
labels, not identities.

The prototype uses exact 64-byte source leaves and a deterministic midpoint
balanced tree, replacing changed paths while reusing unchanged subtree IDs.
This chunking rule is part of schema version 1; changing it requires a new
version/domain. Environment fingerprints include every input that can change
checking, so a state checked under another compiler/prelude is a different
state.

## Request and response

1. The client declares a root with a shallow DAG: changed nodes contain their
   payload; unchanged subtrees are references by digest. It includes the
   expected state root and action request.
2. The server verifies the supplied node encodings and hashes, resolves
   references, reconstructs the named state, and checks that the supplied
   environment matches the active checker environment.
3. If references are absent from the bounded cache, the server returns
   `missingNodes: [digest, ...]` without evaluating the action. The client
   sends the missing node closure and retries the same hypothetical request.
4. The server applies the action to an immutable copy of the state, checks the
   result, builds changed nodes and a transition record, and returns the
   successor root, transition ID, changed nodes, goal summaries, and source
   patch/projection data needed by the client.
5. The client may select the successor, keep both states, or discard the
   response. No adoption/accept message is sent.

Repeated requests should be idempotent for equal `(parent, action, goal,
arguments, environment)` inputs. The transition ID is deterministic from
those inputs and the successor root. Failures return diagnostics and do not
change any Nim source or sidecar.

## Verification and cache

On every cache miss or client-supplied node, the LSP recomputes the digest and
rejects malformed or mismatched content. Cache entries distinguish
hash-verified nodes from states whose transitions have been checker-validated;
only the latter can satisfy a request that requires a checked state. The
checker evaluates transitions from reconstructed source/goals and does not
trust a client's claim that a node is checked.

The current server cache is bounded by an LRU limit of 4096 nodes. It is
bounded by node count rather than bytes, and nodes are not pinned during a
request; large states may trigger additional transfers. Eviction removes
acceleration only. A client holding a root can rehydrate its needed nodes and
continue after eviction or server restart. The server does not promise
persistent cache identity across sessions.

## Undo, branches, and editor source

The extension stores parent/successor roots and transition metadata in local
history. Undo and Redo change the selected root synchronously. When multiple
goals exist, every request names both the selected root and the goal ID, so
any open goal in any locally held branch can be targeted. A successor keeps
all untouched sibling goals.

The selected proof state can be shown in a temporary inline projection. Writing
its Nim source back to the shared document is a separate editor operation. The
projection is not written to the source file or sidecar until the user saves. The
client captures the editor revision/source hash at the state’s base and
compares it with the current document before applying a patch. On conflict it
keeps the selected in-memory branch and asks the user to refresh/rebase or
choose another state; it never silently overwrites intervening edits. This is
the one document-scoped boundary. It does not gate local undo or further
hypothetical queries.

## Migration boundary

The VS Code action surface uses state-addressed requests and a client-owned
root/history for action discovery and submission, inline expansion, keyboard
and webview entry points, history display, source projection, and source
adoption. The seven action IDs are covered by an executable integration probe.
Older LSP methods such as `availableShedActions`, `submitShedAction`,
`commitShedAction`, and the server-owned history/undo/redo methods remain
available for legacy clients but are not used by VS Code actions. #449 records
the design; #450 demonstrates the smallest two-goal refine and cache-miss path;
#451 owns the feature, walkthrough, docs, and manual VS Code demonstration.
