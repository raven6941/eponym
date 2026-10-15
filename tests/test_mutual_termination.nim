## Issue #42: tests for size-change termination of mutual groups.
## Builds SctCalls directly (no parser dependency); the elaborator layer
## constructs these from clause patterns (see elabMutualDecl).

import std/strutils
import ../src/eponym/[preterm, mutual_termination]

proc call(caller, callee: string, arcs: seq[SctArc],
          nSrc = 1, nTgt = 1): SctCall =
  SctCall(caller: caller, callee: callee, nSrc: nSrc, nTgt: nTgt,
          arcs: arcs, loc: noLoc)

proc expectRaise(calls: seq[SctCall], cycleFragment: string) =
  try:
    checkSct(calls)
    doAssert false, "expected SctError"
  except SctError as e:
    doAssert cycleFragment in e.msg,
      "cycle not named in error: " & e.msg

when isMainModule:
  # 1. Mutual even/odd, both decreasing on the scrutinee: accept.
  checkSct(@[
    call("even", "odd", @[(src: 0, strict: true, tgt: 0)]),
    call("odd", "even", @[(src: 0, strict: true, tgt: 0)]),
  ])
  echo "ok: even/odd mutual pair accepted"

  # 2. Ping-pong with no size information at all: reject, cycle named.
  expectRaise(@[
    call("ping", "pong", @[]),
    call("pong", "ping", @[]),
  ], "ping -> pong -> ping")
  echo "ok: sizeless ping-pong rejected with named cycle"

  # 3. One direction decreases strictly, the other passes the formal
  #    through (<=): accept — the composed self-loop has a strict arc.
  checkSct(@[
    call("a", "b", @[(src: 0, strict: true, tgt: 0)]),
    call("b", "a", @[(src: 0, strict: false, tgt: 0)]),
  ])
  echo "ok: mixed strict/nonstrict pair accepted"

  # 4. THE SOUNDNESS CASE (see module doc): f decreases into g, but g
  #    calls f on a constant. The naive "every cycle has a decreasing
  #    edge" check accepts this; SCT must reject it.
  #    f (suc (suc zero)) = g (suc zero); g (suc m) = f (suc (suc zero))
  #    loops: f (suc (suc zero)) -> g (suc zero) -> f (suc (suc zero)).
  expectRaise(@[
    call("f", "g", @[(src: 0, strict: true, tgt: 0)]),
    call("g", "f", @[]),  # constant argument: no arcs
  ], "f -> g -> f")
  echo "ok: decrease-then-constant loop rejected (SCT composition)"

  # 5. Non-decreasing self-loop: reject, self cycle named.
  expectRaise(@[
    call("f", "f", @[]),
  ], "f -> f")
  echo "ok: non-decreasing self-loop rejected"

  # 6. Structural self-loop: accept (subsumes the #36 single-def case).
  checkSct(@[
    call("f", "f", @[(src: 0, strict: true, tgt: 0)]),
  ])
  echo "ok: structural self-loop accepted"

  # 7. No mutual calls at all: accept (empty call list).
  checkSct(@[])
  echo "ok: call-free group accepted"

  # 8. Three-function cycle, decrease threaded through all three: accept.
  checkSct(@[
    call("a", "b", @[(src: 0, strict: true, tgt: 0)]),
    call("b", "c", @[(src: 0, strict: false, tgt: 0)]),
    call("c", "a", @[(src: 0, strict: false, tgt: 0)]),
  ])
  echo "ok: three-function threaded cycle accepted"

  # 9. Three-function cycle where the decrease is dropped mid-cycle:
  #    a -> b strict, b -> c strict, c -> a constant. The a->b->c path
  #    composes to strict, but c -> a drops it; the composed c->c loop
  #    (via a,b) has no strict self-arc. Reject.
  expectRaise(@[
    call("a", "b", @[(src: 0, strict: true, tgt: 0)]),
    call("b", "c", @[(src: 0, strict: true, tgt: 0)]),
    call("c", "a", @[]),
  ], "a -> b -> c -> a")
  echo "ok: decrease-dropped-mid-cycle rejected"

  # 10. Decrease on a non-scrutinee formal threads through: accept.
  #     f's formal 1 decreases into g's formal 0; g passes it through.
  checkSct(@[
    call("f", "g", @[(src: 1, strict: true, tgt: 0)]),
    call("g", "f", @[(src: 0, strict: false, tgt: 1)]),
  ])
  echo "ok: non-scrutinee formal decrease accepted"

  echo "--- size-change termination checks passed ---"
