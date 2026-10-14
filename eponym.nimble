# Package

version       = "0.1.0"
author        = "Wally"
description   = "Eponym: a dependently-typed language elaborator in Nim"
license       = "MIT"
srcDir        = "src"

# Dependencies

requires "nim >= 2.0.0"

# Tasks (production paths; issue #189: experimental code lives in src/experimental/)

task test, "Run all test suites and examples":
  for f in ["eponym_init", "preterm", "parse_surf", "elab", "unify", "eponym_mac", "egraph", "eponym_embed", "kernel_check"]:
    echo "=== " & f & " ==="
    exec "nim c -r --hints:off --path:src --path:src/eponym src/eponym/" & f & ".nim"
  echo "=== examples ==="
  exec "nim c -r --hints:off --path:src --path:src/eponym tests/run_examples.nim"

task build, "Build all production modules":
  for f in ["eponym_init", "preterm", "parse_surf", "elab", "unify", "eponym_mac", "egraph", "eponym_embed", "kernel_check", "sheds", "sheds_mac", "shed_layout"]:
    exec "nim c --hints:off --path:src --path:src/eponym src/eponym/" & f & ".nim"
  exec "nim c --hints:off --path:src --path:src/eponym src/repl.nim"
  echo "=== lsp (compile only; it blocks on stdin) ==="
  exec "nim c --hints:off --path:src --path:src/eponym src/eponym/lsp.nim"
