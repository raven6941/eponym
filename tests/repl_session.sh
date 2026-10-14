#!/bin/sh
# Issue #50: scripted REPL session test.
# Builds src/repl.nim, pipes a fixed session into it, and asserts the
# outputs: defs persist across lines, :type/:eval work, errors are located
# and don't kill the session, :load makes a file's defs usable.
set -e
cd "$(dirname "$0")/.."
P="--path:src --path:src/eponym --path:src/relational --path:src/staging"
nim c --hints:off $P -o:/tmp/eponym-repl-test src/repl.nim
/tmp/eponym-repl-test > /tmp/repl-session.out <<'EOF'
:load lib/nat.ep
proc two : Nat = suc (suc zero)
proc constFn (A : ?) (B : ?) (x : A) (y : B) : A =
  x
:eval two
:eval (add (suc zero) two)
:eval (constFn Nat Nat two (suc zero))
:type (add two two)
proc bad : Nat = true

:type bad
:type constFn
:quit
EOF
fail=0
check() { # $1 = grep pattern, $2 = description
  if grep -qF "$1" /tmp/repl-session.out; then
    echo "ok: $2"
  else
    echo "FAIL: $2 (missing '$1')"; fail=1
  fi
}
check "two : Nat" "single-line def elaborates and persists"
check "constFn : Pi(?, A. Pi(?, B. Pi(A, x. Pi(B, y. A))))" \
  "multi-line def elaborates and persists"
check "(suc (suc zero))" ":eval prints weak-head normal form"
check "(suc (suc (suc zero)))" ":eval reduces add through the eliminator"
check "error: line 1, col 18" "failing decl prints a located error"
check "Nat" ":type prints the inferred type"
check "error: line 1, col 1: unbound variable 'bad'" \
  "session continues after the error (:type bad fails)"
if [ "$fail" -ne 0 ]; then
  echo "--- full session output ---"; cat /tmp/repl-session.out
  exit 1
fi
echo "--- repl session test passed ---"
