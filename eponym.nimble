# Package

version       = "0.1.0"
author        = "Wally"
description   = "Eponym: a dependently-typed language elaborator in Nim"
license       = "MIT"
srcDir        = "src"

# Dependencies

requires "nim >= 2.0.0"

# Tasks

task test, "Run all test suites and examples":
  for f in ["ett", "ett_init", "preterm", "parse_surf", "mac_surf", "elab", "ett_mac"]:
    echo "=== " & f & " ==="
    exec "nim c -r --hints:off --path:src src/" & f & ".nim"
  echo "=== examples ==="
  exec "nim c -r --hints:off --path:src tests/run_examples.nim"

task build, "Build all modules":
  for f in ["ett", "ett_init", "preterm", "parse_surf", "mac_surf", "elab", "ett_mac", "lsp", "egraph", "ett_embed"]:
    exec "nim c --hints:off --path:src src/" & f & ".nim"
