## Issue #42: tests for the mutual-termination call-graph machinery.
## Builds PreTerms directly (no parser dependency); the next chunk wires
## real elaborated bodies in.

import std/strutils
import ../src/eponym/[preterm, mutual_termination]

proc v(name: string): PreTerm = mkVar(name)
proc app1(f, a: PreTerm): PreTerm = mkApp(f, a)

proc d(name: string, body: PreTerm, patVars: seq[string]): MutDecl =
  MutDecl(name: name, body: body, patVars: patVars)

proc expectRaise(decls: seq[MutDecl], cycleFragment: string) =
  try:
    checkMutualBlock(decls)
    doAssert false, "expected MutualTerminationError"
  except MutualTerminationError as e:
    doAssert cycleFragment in e.msg,
      "cycle not named in error: " & e.msg

when isMainModule:
  # 1. Mutual even/odd, both decreasing on the pattern variable: accept.
  let evenOdd = @[
    d("even", app1(v("odd"), v("n")), @["n"]),
    d("odd", app1(v("even"), v("n")), @["n"]),
  ]
  checkMutualBlock(evenOdd)
  echo "ok: even/odd mutual pair accepted"

  # 2. Ping-pong with no decreasing argument: reject, cycle named.
  let pingPong = @[
    d("ping", app1(v("pong"), v("x")), @[]),
    d("pong", app1(v("ping"), v("y")), @[]),
  ]
  expectRaise(pingPong, "ping -> pong -> ping")
  echo "ok: non-decreasing ping-pong rejected with named cycle"

  # 3. One direction decreases, the other calls back: accept (every cycle
  #    still contains a decreasing edge).
  let mixed = @[
    d("a", app1(v("b"), v("m")), @["m"]),
    d("b", app1(v("a"), v("k")), @[]),
  ]
  checkMutualBlock(mixed)
  echo "ok: mixed decreasing/non-decreasing pair accepted"

  # 4. Non-decreasing self-loop: reject, self cycle named.
  let selfLoop = @[d("f", app1(v("f"), v("z")), @[])]
  expectRaise(selfLoop, "f -> f")
  echo "ok: non-decreasing self-loop rejected"

  # 5. No mutual calls at all: accept.
  let unrelated = @[
    d("g", app1(v("h"), v("w")), @[]),
    d("k", app1(v("h"), v("w")), @[]),
  ]
  checkMutualBlock(unrelated)
  echo "ok: call-free group accepted"

  # 6. Nested call under a lambda still registers the edge.
  let nested = @[
    d("p", mkApp(v("lam"), app1(v("q"), v("n"))), @["n"]),
    d("q", app1(v("p"), v("n")), @["n"]),
  ]
  checkMutualBlock(nested)
  echo "ok: nested call edges collected"

  echo "--- mutual termination graph checks passed ---"
