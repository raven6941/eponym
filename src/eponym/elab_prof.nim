## Issue #55: lightweight cumulative per-phase elaboration timers.
##
## Phases: parse, checkTm, inferTm, unifyElab, zonk, convElab, plus
## `other` (driver-level work: elabDecl clause machinery, checkUsage,
## motive building — everything not charged to a nested phase).
##
## Zero overhead when disabled: everything is gated on the
## `-d:elabProfile` compile flag via `when ElabProfile`, so
## `profilePhase` compiles to exactly `body` in a normal build
## (verified: no timer code in the disabled build).
##
## Timing is *exclusive*: a stack tracks nested phases, and time spent
## in a child phase is subtracted from the enclosing phase. Recursive
## entries (checkTm calling checkTm, zonk calling zonk) are handled
## the same way — inner time is charged to the inner frame.

type ElabPhase* = enum
  epParse   ## parse_surf.parseProgram
  epCheck   ## elab.checkTm
  epInfer   ## elab.inferTm
  epUnify   ## elab.unifyElab
  epZonk    ## unify.zonk
  epConv    ## elab.convElab (handler-raised conversion)
  epClause  ## elab.elabClausesDecl (clause-matrix compilation, motives)
  epData    ## elab.elabDataDecl (data desugaring, eliminator generation)
  epUsage   ## usage_check.checkUsage (linear/erased usage verification)
  epKernel  ## eponym_init.check (Andromeda-style core re-check of each def)
  epEval    ## eponym_init.eval (kernel evaluation)
  epOther   ## driver-level remainder minus nested phases

const ElabProfile* {.booldefine.} = false
  ## Compile with `-d:elabProfile` to enable.

{.push warning[UnusedImport]: off.}
import std/monotimes  # MonoTime, getMonoTime
import std/times      # inNanoseconds on Duration
import std/strformat  # &"" in reportPhases
import std/strutils   # join in reportPhases
{.pop.}

when ElabProfile:
  type PhaseFrame = object
    phase: ElabPhase
    t0: MonoTime
    childNanos: int64

  var phaseNanos: array[ElabPhase, int64]
  var phaseStack: seq[PhaseFrame]

  proc pushPhase(ph: ElabPhase) =
    phaseStack.add(PhaseFrame(phase: ph, t0: getMonoTime()))

  proc popPhase() =
    let f = phaseStack.pop()
    let total = (getMonoTime() - f.t0).inNanoseconds
    phaseNanos[f.phase] += total - f.childNanos
    if phaseStack.len > 0:
      phaseStack[^1].childNanos += total

  proc resetPhases*() =
    ## Zero all accumulators (call between benchmark rounds).
    for ph in ElabPhase: phaseNanos[ph] = 0
    phaseStack.setLen(0)

  proc reportPhases*(): string =
    ## Multi-line breakdown: exclusive ms and % of tracked total per phase.
    var lines: seq[string] = @[]
    var total: int64 = 0
    for ph in ElabPhase: total += phaseNanos[ph]
    lines.add(&"elaboration phase breakdown (exclusive, total {total.float/1e6:.1f} ms):")
    for ph in ElabPhase:
      let ms = phaseNanos[ph].float / 1e6
      let pct = if total > 0: 100.0 * phaseNanos[ph].float / total.float
                else: 0.0
      lines.add(&"  {$ph:<9} {ms:10.1f} ms  {pct:5.1f}%")
    lines.join("\n")

template profilePhase*(ph: ElabPhase, body: untyped): untyped =
  ## Wrap a phase body. Disabled build: expands to exactly `body`.
  ## `defer` (rather than try/finally-as-expression) so the template works
  ## for both expression bodies (inferTm's case) and statement bodies that
  ## assign `result` (parseProgram): the block evaluates to the body's value
  ## and popPhase runs at block exit on all paths (return, raise, fallthrough).
  when ElabProfile:
    block:
      pushPhase(ph)
      defer: popPhase()
      body
  else:
    body
