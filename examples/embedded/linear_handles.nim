# Single-use handles / affine-linear types over ORC, embedded (Issue #482).
#
# A one-shot acked job: fresh --send--> sent --ack--> acked --close-->
# closed, each step exactly once, in order. The reusable library lives in
# lib/linear.ep; this file is the example-specific use: checked clients
# over that library plus a real Nim backend, so the happy path actually
# runs and its backend trace can be asserted.
#
# What is checked, and what is not (read before reusing this pattern):
# - Checked: inside eponym terms, an ANNOTATED q1 binder is used
#   exactly once and the phase order holds. Double use and drops of
#   annotated binders are compile-time errors (examples/ep/29a, 29b);
#   a phase violation is a compile-time error (29c). The bracket
#   client shows the sound boundary: the handle never becomes a value
#   Nim code can name.
# - KNOWN GAP (watchlist, found by probe while building): a LET-bound
#   intermediate derived from a q1 value is NOT checked — dropping it
#   or using it twice elaborates cleanly, because the unannotated let
#   binder is omega-inferred instead of inheriting the value's
#   quantity. The single-use guarantee therefore covers directly
#   threaded annotated binders, not let-bound intermediates. Whether
#   let binders should inherit quantity (or require annotation) is
#   filed as #484; until it is resolved, do not read
#   "single-use" as covering let-bound handles.
# - Not checked: Nim-side aliasing. Two Nim references to the same
#   JobHandle are invisible to the checker (see
#   docs/known-limitations.md, "Static checks do not manage Nim
#   resources"). ORC's deterministic drop is trusted runtime glue, not
#   something the checker verifies. This example demonstrates checking
#   at the eponym API boundary; it does not claim end-to-end resource
#   management.
# - The bracket callback must be written in eponym. A plain Nim proc
#   callback would receive the handle as an ordinary Nim value and
#   could stash, double-use, or drop it unchecked; a Nim func callback
#   cannot perform the side-effect operations at all, and confinement
#   is not linearity (it does not enforce exactly-once use). That
#   adoption cost is real: the Nim programmer writes the use in eponym
#   and calls withJob from Nim.
# - Copy-to-omega: deliberately absent for live handles; see
#   lib/linear.ep for the per-variant reasons. Only the completed
#   receipt (an immutable Nat) crosses to Nim.
#
# Representation verdict (measured, not assumed): NEGATIVE for this
# handle shape. The q1 happy path and the omega happy path below
# produce identical backend traces (1 send, 1 ack, 1 close, same
# receipt), because at runtime they are the same value moved the same
# way: every Job phase maps to the same Nim ref type (the phase index
# erases), and quantities never reach codegen (they are checking-only;
# the erasure pass drops q0 arguments and the codegen consumes the
# zonked term). Linearity here buys the compile-time guarantee, not a
# cheaper representation. What would pay: codegen mapping a q1 argument
# to a sink move or a q1 handle to a non-refcounted owned pointer, so
# a transfer skips the refcount bump a copy pays. That mapping does
# not exist today; it is #413's move-semantics territory. Note the
# shape of the saving that is NOT available here: this handle is
# already a ref, passed by pointer, so there is no per-transfer copy
# for linearity to remove in the first place; the saving would have to
# come from the refcount itself, i.e. from ownership in codegen.
#
# The omega contrast: omegaDoubleSend below COMPILES and RUNS, sending
# twice through the same handle (backend count 2). The q1 double-send
# is a compile-time error (29a). That is the whole point of the q1
# checking: it rules out at compile time what the omega API permits at
# runtime. The omega backend procedures deliberately do NOT assert
# phases, so the double send succeeds; the q1 backend procedures DO
# assert phases, as defence in depth behind the checker, not as the
# guarantee.
#
# Watchlist (part of the deliverable; observations from building this):
# - Let-linearity gap (above): let-bound intermediates escape q1
#   checking entirely, for both drop and double use. Filed as a
#   follow-up issue (#484). This qualifies every "single-use" claim in this
#   example and in #481-style threaded clients.
# - Generic-result bracket NOT shipped (see lib/linear.ep): with A
#   caller-instantiated, A := Job freshP lets the handle escape through
#   the result, so the Nat-fixed bracket is the sound shape here. A
#   higher-rank bracket is a language-design follow-up, not a library
#   method today.
# - No new language friction otherwise: the lib-import + runtimeType
#   on a data family + mixed bindPostulate / bindPostulatePair /
#   bindPostulateValue bindings all worked first try, and the
#   phase-indexed + q1 pattern fell directly out of #481's machinery.
# - Unused let-bound closed handles do not error (the `c` bindings in
#   jobSession/finishJob): consistent with the let-inference reading,
#   and semantically fine for an inert closed handle, but it is the
#   same mechanism as the gap above, so it is noted, not assumed safe.
# - Structural split, same as #481: misuse cases cannot live in the
#   embedded file itself (they would fail compilation), so the example
#   necessarily splits into embedded positives + .ep negatives.
#
# Misuse cases are negative tests under examples/ep/, run by
# tests/run_examples.nim:
#   - double use:  29a-linear-double-use-neg.ep
#   - dropped:     29b-linear-drop-neg.ep
#   - phase error: 29c-linear-phase-neg.ep (send after close)
# Positive .ep case: 29-linear-ok.ep (threaded client + bracket client).

import eponym_mac
import eponym_embed
import eponym_init
import elab

type
  JobPhaseB = enum freshB, sentB, ackedB, closedB

  JobHandle = ref object
    phase: JobPhaseB
    payload: int
    ack: int
    sends: int
    acks: int
    closes: int

proc newJobHandle(): JobHandle =
  JobHandle(phase: freshB)

# --- q1 backend: phase asserts are defence in depth, not the guarantee.
proc hostSendJ(payload: int, handle: JobHandle): JobHandle =
  doAssert handle.phase == freshB, "sendJ on a non-fresh job"
  handle.phase = sentB
  handle.payload = payload
  inc handle.sends
  handle

proc hostAckJ(handle: JobHandle): tuple[ack: int, handle: JobHandle] =
  doAssert handle.phase == sentB, "ackJ on a non-sent job"
  handle.phase = ackedB
  handle.ack = handle.payload + 1
  inc handle.acks
  (handle.ack, handle)

proc hostCloseJ(handle: JobHandle): JobHandle =
  doAssert handle.phase == ackedB, "closeJ on a non-acked job"
  handle.phase = closedB
  inc handle.closes
  handle

# --- omega backend: no phase asserts, so double use succeeds at runtime.
proc hostSendW(payload: int, handle: JobHandle): JobHandle =
  handle.payload = payload
  inc handle.sends
  handle

proc hostAckW(handle: JobHandle): tuple[ack: int, handle: JobHandle] =
  handle.ack = handle.payload + 1
  inc handle.acks
  (handle.ack, handle)

proc hostCloseW(handle: JobHandle): JobHandle =
  inc handle.closes
  handle

# --- bracket backend (raw Value route: the callback is a checked term).
proc hostWithJob(args: seq[Value], globals: Globals): Value =
  if args.len != 1:
    raise newException(ValueError, "withJob expects 1 runtime argument")
  let handle = newJobHandle()
  let outcome = callRuntimeValue(args[0], [toHostValue(handle)])
  if handle.phase != closedB:
    raise newException(IOError,
      "withJob callback returned without closing the job")
  result = outcome

eponymBlock:
  import "../../lib/linear.ep"

  # Every Job phase erases to the same Nim ref type at runtime.
  runtimeType(Job, JobHandle)

  bindPostulate(sendJ, hostSendJ, Nat, Job, Job)
  bindPostulatePair(ackJ, hostAckJ, Job, Nat, Job)
  bindPostulate(closeJ, hostCloseJ, Job, Job)
  bindPostulateValue(withJob, hostWithJob)

  # Omega variants of the same operations: same backend state shape,
  # no linearity, no phase asserts. Declared here, not in the library:
  # the library's discipline IS q1, and the omega API exists only to
  # make the contrast runnable.
  postulate(sendW, Pi(x: Nat, Pi(j: Job freshP, Job sentP)))
  postulate(ackW, Pi(j: Job sentP, Sig(a: Nat, Job ackedP)))
  postulate(closeW, Pi(j: Job ackedP, Job closedP))
  bindPostulate(sendW, hostSendW, Nat, Job, Job)
  bindPostulatePair(ackW, hostAckW, Job, Nat, Job)
  bindPostulate(closeW, hostCloseW, Job, Job)

  # Happy path, direct style: send, ack, close, return the receipt.
  proc jobSession(j {.linear.}: Job[freshP()]): Nat =
    let s = sendJ(zero(), j)
    let p = ackJ(s)
    let c = closeJ(snd(p))
    fst(p)

  # Helper for the bracket callback: close the acked handle and return
  # the receipt. The closed handle is bound and dropped: it is inert
  # (no operation accepts Job closedP), and the receipt is the only
  # value returned. The callback itself stays a single nested
  # expression, so no let-in inside a lambda body is needed.
  proc finishJob(p: Sig(a: Nat, Job[ackedP()])): Nat =
    let c = closeJ(snd(p))
    fst(p)

  # Happy path, bracket style: the handle never escapes this term.
  proc jobViaBracket(): Nat =
    withJob(lam(j: Job[freshP()]) => finishJob(ackJ(sendJ(suc(zero()), j))))

  # Omega happy path: same steps, same trace as jobSession.
  proc omegaSession(j: Job[freshP()]): Nat =
    let s = sendW(zero(), j)
    let p = ackW(s)
    let c = closeW(snd(p))
    fst(p)

  # Omega double send: compiles and runs. The q1 equivalent is 29a,
  # which is a compile-time error. This is the contrast the example
  # exists to show.
  proc omegaDoubleSend(j: Job[freshP()]): Job[sentP()] =
    let s1 = sendW(zero(), j)
    sendW(suc(zero()), j)

# --- Normal Nim program ------------------------------------------------
# Plain Nim from here: the clients above were checked at compile time.

proc main() =
  echo "linear_handles: single-use acked jobs, embedded (Issue #482)."
  # Bracket path: fresh handle created inside withJob; callback sends
  # suc(zero()) = 1, ack receipt is payload + 1 = 2.
  let bracketReceipt = jobViaBracket()
  echo "  bracket receipt: ", bracketReceipt
  doAssert bracketReceipt == 2, "bracket receipt must be payload + 1"

  # Direct q1 path over a fresh handle.
  let directHandle = newJobHandle()
  let directReceipt = jobSession(directHandle)
  echo "  direct receipt: ", directReceipt,
    " trace sends/acks/closes: ", directHandle.sends, "/",
    directHandle.acks, "/", directHandle.closes
  doAssert directReceipt == 1, "direct receipt must be payload + 1"
  doAssert directHandle.phase == closedB, "direct job must end closed"
  doAssert (directHandle.sends, directHandle.acks,
    directHandle.closes) == (1, 1, 1), "q1 trace must be exactly 1/1/1"

  # Omega happy path: identical trace to the q1 path (the verdict's
  # measurement: same value, same moves, same cost).
  let omegaHandle = newJobHandle()
  let omegaReceipt = omegaSession(omegaHandle)
  echo "  omega receipt: ", omegaReceipt,
    " trace sends/acks/closes: ", omegaHandle.sends, "/",
    omegaHandle.acks, "/", omegaHandle.closes
  doAssert omegaReceipt == 1
  doAssert (omegaHandle.sends, omegaHandle.acks,
    omegaHandle.closes) == (1, 1, 1), "omega trace must match q1 trace"

  # Omega double send: succeeds at runtime (count 2). The q1 version
  # does not compile; see examples/ep/29a-linear-double-use-neg.ep.
  let doubleHandle = newJobHandle()
  discard omegaDoubleSend(doubleHandle)
  echo "  omega double send count: ", doubleHandle.sends
  doAssert doubleHandle.sends == 2, "omega double send must reach backend"

when isMainModule:
  main()
