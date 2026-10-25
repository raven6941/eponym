# Release notes

## Unreleased

First release. The version number is still to be decided; these notes
describe what is in the tree.

### Added

- Native code generation: checked definitions compile to Nim procs.
  The Value backend covers everything in the compiled fragment,
  including dependent and indexed definitions such as the Paxos
  session roles; the representation backend emits direct host code
  where a representation mapping applies (`Int`/`Nat`/`Bool` as
  `int`, `Vec`/`List` as `seq[int]`, `Option` as `Option[int]`),
  with destination-passing folds for sequence eliminators.
  `requireCompiled()` is the opt-in guarantee that no definition
  falls back to the interpreter or the Value layer, and
  `-d:eponymCodegenReport` names each definition's backend.
- Interactive sheds in VS Code: seven actions (Intro, Construct,
  Apply, Rewrite, Refine, Give, Case-split) over client-selected,
  branchable proof states.
- LSP first-use setup: with no explicit server path, the extension
  discovers Eponym sources from a checkout or a nimble-installed
  package and builds the server into global storage; sidecar
  generation works from installed packages too, so no checkout is
  needed to use sheds as a library user.

### Breaking changes

- `Bool` is now recognized specially by generated runtime wrappers
  and maps to Nim `bool`. Rename a custom Eponym type that used the
  name `Bool` to avoid the new interpretation.

### Known limitations

See [known-limitations.md](known-limitations.md) for the current
boundary: which definitions get wrappers, which shapes
`requireCompiled()` admits, and which parts of the Nim boundary stay
trusted.
