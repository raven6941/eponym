# Package

version       = "0.1.0"
author        = "raven6941"
description   = "Eponym: a dependently-typed language elaborator in Nim"
license       = "MIT"
# Production modules live in src/eponym/ and import each other bare
# (e.g. `import eponym_mac`); pointing srcDir there makes the installed
# package support exactly the import style the embedded examples use.
# Experimental code (src/experimental/) is outside srcDir and is never
# installed (issue #189: release packaging excludes experiment code).
srcDir        = "src/eponym"

# Dependencies

requires "nim >= 2.0.0"
requires "falsify >= 0.1.0"  # property-based testing for tests/pbt_*.nim
# NOTE: falsify is not in nimble's package index yet, so CI installs it
# explicitly (tools/ci-local.sh, .github/workflows/ci.yml) via
# `nimble install -y https://github.com/raven6941/falsify`.

# The Eponym prelude (lib/*.ep) ships with the package. `import "x.ep"`
# inside eponymBlock resolves relative to the calling Nim file, so users
# vendor the prelude files they need next to their project; see README
# "Installation". installDirs is package-root-relative: nimble first probes
# srcDir-relative (spurious "Missing directory src/eponym/lib" prompt,
# auto-answered by --accept / interactive "Continue?"), then falls back to
# the package root and copies correctly. "../../lib" installs nothing
# (verified 2026-10-14), so do not "fix" this to be srcDir-relative.
installDirs   = @["lib"]

# Production modules: list explicitly -- nimble does not install srcDir's
# .nim files by default. installFiles resolves relative to srcDir, so these
# are the bare module names. The set must be the full import closure of the
# public entry points (eponym_mac, eponym_embed, sheds_mac, lsp): missing
# one breaks `import eponym_mac` for users (2026-10-14: abilities,
# elab_prof, usage_check were missing).
# (Experimental code in src/experimental/ is deliberately excluded:
# issue #189, release packaging excludes experiment code. src/repl.nim
# is a dev tool, not part of the installed library.)
installFiles  = @["abilities.nim",
                  "eponym_init.nim",
                  "preterm.nim",
                  "parse_surf.nim",
                  "elab.nim",
                  "elab_prof.nim",
                  "unify.nim",
                  "usage_check.nim",
                  "eponym_mac.nim",
                  "lsp.nim",
                  "egraph.nim",
                  "eponym_embed.nim",
                  "kernel_check.nim",
                  "sheds.nim",
                  "sheds_mac.nim",
                  "shed_layout.nim",
                  "mutual_termination.nim"]

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
  for f in ["abilities", "eponym_init", "preterm", "parse_surf", "elab", "elab_prof", "unify", "usage_check", "eponym_mac", "lsp", "egraph", "eponym_embed", "kernel_check", "sheds", "sheds_mac", "shed_layout", "mutual_termination"]:
    echo "=== build " & f & " ==="
    exec "nim c --hints:off --path:src --path:src/eponym src/eponym/" & f & ".nim"
  echo "=== build repl (issue #50) ==="
  exec "nim c --hints:off --path:src --path:src/eponym src/repl.nim"
