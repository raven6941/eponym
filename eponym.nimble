# Package

version       = "0.1.0"
author        = "raven6941"
description   = "Eponym: a dependently-typed language elaborator in Nim"
license       = "MIT"
# Production modules live in src/eponym/ and import each other bare
# (e.g. `import eponym_mac`); pointing srcDir there makes the installed
# package support exactly the import style the embedded examples use.
# Experimental probes remain outside srcDir and are never installed
# (issue #189: release packaging excludes experiment code). The stable SHA-256
# and shed-state DAG runtime modules live in src/eponym because the LSP and
# shed state implementation depend on them.
srcDir        = "src/eponym"

# Dependencies

requires "nim >= 2.0.0"
# Falsify is used only by the property-test suite. It is not an install
# dependency; tools/ci-local.sh installs it directly from GitHub because it
# is not in Nimble's package index yet.

# The Eponym prelude (lib/*.ep) ships with the package. Relative imports
# resolve beside the calling Nim file first and then fall back to this
# installed `lib/` directory. installDirs is package-root-relative: nimble first probes
# srcDir-relative (spurious "Missing directory src/eponym/lib" prompt,
# auto-answered by --accept / interactive "Continue?"), then falls back to
# the package root and copies correctly. "../../lib" installs nothing
# (verified 2026-10-14), so do not "fix" this to be srcDir-relative.
installDirs   = @["lib"]

# Production modules: list explicitly -- nimble does not install srcDir's
# .nim files by default. installFiles resolves relative to srcDir, so these
# are the bare module names. The set must be the full import closure of the
# public entry points (eponym_mac, eponym_embed, lsp): missing
# one breaks `import eponym_mac` for users (2026-10-14: abilities,
# elab_prof, usage_check were missing).
# (Experimental probes in src/experimental/ are deliberately excluded:
# issue #189, release packaging excludes experiment code. src/repl.nim
# is a dev tool, not part of the installed library.)
installFiles  = @["abilities.nim",
                  "codegen.nim",  # issue #329: Phase 1 backend (imported by eponym_mac)
                  "derive_repr.nim",  # issue #402: representation derivation
                  "eponym_init.nim",
                  "erasure.nim",
                  "preterm.nim",
                  "parse_surf.nim",
                  "sha256.nim",
                  "shed_state_dag.nim",
                  "elab.nim",
                  "elab_prof.nim",
                  "elab_trace.nim",
                  "unify.nim",
                  "usage_check.nim",
                  "eponym_mac.nim",
                  "lsp.nim",
                  "egraph.nim",
                  "eponym_embed.nim",
                  "kernel_check.nim",
                  "sheds.nim",
                  "shed_layout.nim",
                  "shed_state.nim",
                  "mutual_termination.nim",
                  "staged_inject.nim"]  # issue #499: staged runtime type residuals

# Tasks
#
# `test` IS the CI matrix: tools/ci-local.sh is the single source of truth
# (the GitHub workflow calls it too), so delegation -- not duplication --
# keeps `nimble test` matching CI by construction (issue #183).
task test, "Run the full CI matrix (same matrix GitHub CI runs)":
  exec "sh tools/ci-local.sh"

# `buildall` mirrors the "Build: production modules" section of
# tools/ci-local.sh. Keep the module list in sync with that script.
# (Named buildall because nimble's built-in `build` cannot be shadowed
# by a custom task -- `nimble build` runs the built-in and reports
# "Nothing to build" for a library with no `bin`.)
task buildall, "Build all production modules":
  for f in ["abilities", "codegen", "derive_repr", "eponym_init", "erasure", "preterm", "parse_surf", "sha256", "shed_state_dag", "elab", "elab_prof", "unify", "usage_check", "eponym_mac", "lsp", "egraph", "eponym_embed", "kernel_check", "sheds", "shed_layout", "shed_state", "mutual_termination", "staged_inject"]:
    echo "=== build " & f & " ==="
    exec "nim c --hints:off --path:src --path:src/eponym src/eponym/" & f & ".nim"
  echo "=== build repl (issue #50) ==="
  exec "nim c --hints:off --path:src --path:src/eponym src/repl.nim"
