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
# "Installation". installDirs resolves relative to srcDir, hence ../lib.
# Installed at <pkgdir>/lib/.
installDirs   = @["../lib"]

# Production modules: srcDir's .nim files must be listed explicitly --
# nimble does not install them by default. Patterns are relative to the
# package root. (Experimental code in src/experimental/ is deliberately
# excluded: issue #189, release packaging excludes experiment code.)
installFiles  = @["src/eponym/eponym_init.nim",
                  "src/eponym/preterm.nim",
                  "src/eponym/parse_surf.nim",
                  "src/eponym/elab.nim",
                  "src/eponym/unify.nim",
                  "src/eponym/eponym_mac.nim",
                  "src/eponym/lsp.nim",
                  "src/eponym/egraph.nim",
                  "src/eponym/eponym_embed.nim",
                  "src/eponym/kernel_check.nim",
                  "src/eponym/sheds.nim",
                  "src/eponym/sheds_mac.nim",
                  "src/eponym/shed_layout.nim",
                  "src/repl.nim"]

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
