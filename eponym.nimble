# Package

version       = "0.1.0"
author        = "Wally"
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

# The Eponym prelude (lib/*.ep) ships with the package. `import "x.ep"`
# inside eponymBlock resolves relative to the calling Nim file, so users
# vendor the prelude files they need next to their project; see README
# "Installation". Installed at <pkgdir>/lib/.
installDirs   = @["lib"]

# Tasks
#
# `test` IS the CI matrix: tools/ci-local.sh is the single source of truth
# (the GitHub workflow calls it too), so delegation -- not duplication --
# keeps `nimble test` matching CI by construction (issue #183).
task test, "Run the full CI matrix (same matrix GitHub CI runs)":
  exec "sh tools/ci-local.sh"

# `build` mirrors the "Build: production modules" section of
# tools/ci-local.sh. Keep the module list in sync with that script.
task build, "Build all production modules":
  for f in ["eponym_init", "preterm", "parse_surf", "elab", "unify", "eponym_mac", "lsp", "egraph", "eponym_embed", "kernel_check", "sheds", "sheds_mac", "shed_layout"]:
    echo "=== build " & f & " ==="
    exec "nim c --hints:off --path:src --path:src/eponym src/eponym/" & f & ".nim"
  echo "=== build repl (issue #50) ==="
  exec "nim c --hints:off --path:src --path:src/eponym src/repl.nim"
