## Issue #83: structured elaboration trace facility.
##
## Opt-in logging of the elaborator's decision process: check/infer
## entry/exit (nesting drives indentation), unification attempts and
## failures, metavariable assignments, implicit-argument insertions,
## conversion goals and handler discharges, quantity checks and qvar
## solutions. Complements #46 (provenance threaded into errors: where the
## *inputs* came from) with the dynamic view: what the elaborator *did* on
## the way to success or failure.
##
## Usage:
##   import elab_trace
##   setElabTrace(true)                    # all categories, stderr
##   setElabTrace(true, {tcUnify, tcMeta})  # allow-list filter
##   startTraceCapture()                   # route to memory (for tests)
##   ...
##   let evs = stopTraceCapture()
##
## From the shell, `EPON_TRACE` enables tracing for an elaboration run
## without code changes (the driver reads it at entry):
##   EPON_TRACE=unify,meta nim c -r myfile.nim     # only those categories
##   EPON_TRACE=1 nim c -r myfile.nim              # all categories
## This works on the `eponym`/`eponymBlock` macro path too: the macro
## elaborates at compile time inside the compiler VM, and `getEnv` is
## VM-readable, so the env var is honored there as well.
##
## Design decision (recorded in decisions.org #83): a *runtime* flag, not
## a compile-time const. Rationale: the elaborator runs at Nim compile
## time (inside the compiler VM on the macro path), where a runtime bool
## in the VM process is settable from the driver's EPON_TRACE read — no
## toolchain rebuild is needed to debug a failing program. The disabled
## path is a single boolean branch per event site (measured <2% overhead
## on the elaboration corpus; see issue #83). Compiling with
## `-d:elabTraceStrip` removes the hooks entirely for the paranoid.
##
## Trace output is implementer-facing by design (unlike ElabError text,
## which #34 keeps user-facing): payloads may use the kernel's `$`
## rendering with internal R123/V6 ids.

import std/os
import std/strutils

const ElabTraceStrip* {.booldefine.} = false
  ## Compile with `-d:elabTraceStrip` to remove all trace hooks.

type
  TraceCat* = enum
    tcCheck     ## checkTm entry/exit
    tcInfer     ## inferTm entry/exit
    tcUnify     ## unifyElab attempts and failures
    tcMeta      ## metavariable assignments (unify.solveMeta)
    tcImplicit  ## implicit-argument insertions (elab.insertImplicits)
    tcConv      ## conversion goals and handler discharges (elab.convElab)
    tcQty       ## quantity checks and qvar solutions (elab)

  TraceEvent* = tuple
    cat: TraceCat
    kind: string   ## dotted name: "check.in", "unify.fail", ...
    depth: int     ## nesting depth (indentation = 2 * depth)
    payload: string

const allTraceCats* = {tcCheck, tcInfer, tcUnify, tcMeta, tcImplicit,
                       tcConv, tcQty}

proc trunc*(s: string, n: int = 200): string =
  ## Keep trace payloads readable; pretty-printed terms can be enormous.
  if s.len <= n: s
  else: s[0 ..< n] & "…"

when not ElabTraceStrip:
  var traceOn = false
  var traceCats: set[TraceCat] = allTraceCats
  var traceDepth = 0
  var traceMaxDepth* = 40
    ## Events deeper than this are still elaborated, just not logged.
  var traceSink: File = nil  # nil = stderr
  var traceCapture: seq[TraceEvent] = @[]
  var traceCapturing = false
  var traceExplicit = false  # setElabTrace / env already applied

  proc setElabTrace*(on: bool, cats: set[TraceCat] = allTraceCats,
                     maxDepth: int = 40) =
    ## Enable or disable tracing; `cats` is an allow-list filter.
    ## Disabling resets the nesting depth, so an aborted traced
    ## elaboration cannot unbalance later output.
    traceOn = on
    traceCats = cats
    traceMaxDepth = maxDepth
    traceExplicit = true
    if not on:
      traceDepth = 0

  proc elabTraceEnabled*(): bool =
    ## True while tracing is on.
    traceOn

  proc startTraceCapture*() =
    ## Route events into an in-memory log instead of the sink (for tests).
    traceCapture.setLen(0)
    traceCapturing = true

  proc stopTraceCapture*(): seq[TraceEvent] =
    traceCapturing = false
    result = move(traceCapture)

  proc parseTraceCats*(s: string): set[TraceCat] =
    ## "unify,meta" -> {tcUnify, tcMeta}; "all", "1", "*" or "" -> all.
    ## Unknown names are ignored.
    let t = s.strip().toLowerAscii()
    if t in ["", "all", "1", "*"]:
      return allTraceCats
    for name in t.split(','):
      case name.strip()
      of "check": result.incl(tcCheck)
      of "infer": result.incl(tcInfer)
      of "unify": result.incl(tcUnify)
      of "meta": result.incl(tcMeta)
      of "implicit": result.incl(tcImplicit)
      of "conv": result.incl(tcConv)
      of "qty": result.incl(tcQty)
      else: discard

  proc maybeEnableTraceFromEnv*() =
    ## Called at elaborator driver entry (elabCheck*, ModuleDriver).
    ## EPON_TRACE=<cats> enables tracing for the run; unset means off.
    ## No-op once tracing was set explicitly (explicit beats env).
    if traceExplicit:
      return
    let v = getEnv("EPON_TRACE")
    if v == "":
      return
    traceExplicit = true  # env counts as explicit; read once per process
    traceOn = true
    traceCats = parseTraceCats(v)

  proc emitTrace(cat: TraceCat, kind: string, depth: int, payload: string) =
    if traceCapturing:
      traceCapture.add((cat, kind, depth, payload))
    else:
      let sink = if traceSink == nil: stderr else: traceSink
      sink.writeLine(spaces(depth * 2) & kind & ": " & payload)

  proc traceCatActive*(cat: TraceCat): bool =
    ## Fast path check: is tracing on for this category?
    traceOn and cat in traceCats

  proc traceEnter*(cat: TraceCat, kind: string, payload: string): int =
    ## Log `kind.in` at the current depth, bump the depth, return the
    ## entry depth for `traceExit` pairing. Caller must have checked
    ## `traceCatActive` (so `payload` was worth building).
    let d = traceDepth
    if d <= traceMaxDepth:
      emitTrace(cat, kind & ".in", d, payload)
    inc traceDepth
    d

  proc traceExit*(cat: TraceCat, kind: string, entryDepth: int) =
    dec traceDepth
    if entryDepth <= traceMaxDepth:
      emitTrace(cat, kind & ".out", entryDepth, "")

else:
  ## -d:elabTraceStrip: the whole facility compiles away. The public API
  ## stays callable (no-ops) so instrumented modules need no `when` guards.
  proc setElabTrace*(on: bool, cats: set[TraceCat] = allTraceCats,
                     maxDepth: int = 40) = discard
  proc elabTraceEnabled*(): bool = false
  proc startTraceCapture*() = discard
  proc stopTraceCapture*(): seq[TraceEvent] = @[]
  proc parseTraceCats*(s: string): set[TraceCat] = {}
  proc maybeEnableTraceFromEnv*() = discard
  proc traceCatActive*(cat: TraceCat): bool = false
  proc traceEnter*(cat: TraceCat, kind: string, payload: string): int = -1
  proc traceExit*(cat: TraceCat, kind: string, entryDepth: int) = discard

template traceEvt*(cat: TraceCat, kind: string, payload: string) =
  ## One structured event. `payload` is *not* evaluated when tracing is
  ## off or the category is filtered out (template laziness). Events
  ## deeper than `traceMaxDepth` are not logged (same rule as scopes).
  when not ElabTraceStrip:
    if traceOn and cat in traceCats and traceDepth <= traceMaxDepth:
      emitTrace(cat, kind, traceDepth, payload)

template traceGuard*(cat: TraceCat, kind: string, payload: string) =
  ## Entry/exit pair (`kind.in` now, `kind.out` at scope exit via defer,
  ## so exceptions still log the unwind point). Statement position only;
  ## `payload` is evaluated only when the category is active. When
  ## tracing is off this is one boolean branch plus a no-op defer.
  when not ElabTraceStrip:
    let traceDepthAtEntry = if traceCatActive(cat):
      traceEnter(cat, kind, payload)
    else:
      -1
    defer:
      if traceDepthAtEntry >= 0:
        traceExit(cat, kind, traceDepthAtEntry)
