# Shed semantic model

Issue #377 records a gap in the interactive editing model: the elaborator
knows a hole as a typed metavariable, but the editor-facing `ShedInfo` had
only a hole index and rendered strings. The first step is to make the
in-process semantic state explicit and define where its presentation and
serialization boundaries sit.

## In-process state

`HoleInfo` now retains the typed hole term (`holeTerm`), its goal term, and an
innermost-first context of named binders. Each context binder keeps its type
and quantity, including an unresolved quantity variable while the elaborator
is still checking an open definition. `semanticShedState` retains the hole's
metavariable ID and context spine, zonks the goal and context types against
the live `MetaStore`, and exposes the goal's Pi spine as structured binders
with their domains, quantity, implicitness, and erasure flags.

This state is a read-only snapshot tied to the lifetime and identity space of
that `MetaStore`. It is not a standalone serialized term: unresolved
metavariables refer to that store, and core terms may also contain values
whose runtime closures are not serializable.

## Consumer and projection boundaries

LSP hover now reads the semantic state and renders its goal and context from
the structured terms. `shedGoalAndCtx` also projects that same state into the
existing text fields used by the sidecar and 2D layout. This avoids treating
pretty-printed text as editable semantic data.

The `.sheds.json` sidecar remains a cross-process presentation record. Its
goal, context, and Pi-spine strings are display projections; the LSP does not
parse them back into terms. Positions, status, generated source, and user
draft text remain sidecar/editor metadata. The draft is still opaque scratch
text and does not enter Eponym elaboration.

If a later feature needs semantic terms across the compiler/LSP process
boundary, it needs a versioned structural codec for the term algebra, binder
contexts, metavariable IDs/spines, and global references. Such a codec must
preserve de Bruijn meaning and validate that references belong to the
serialized snapshot. Parsing the pretty-printer output would not be a safe
substitute.

## Editing remains source-driven

The semantic snapshot is currently used for inspection. Refinement and
case-splitting still edit generated Eponym source and invoke the elaborator
again, so the checker remains authoritative after every edit. This change
does not make draft text typechecked, mutate core terms in place, or define a
persisted semantic editing session.
