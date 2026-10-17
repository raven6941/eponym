## Elaboration trace tests (issue #83).
##
## Drives elaboration directly (like error_snapshots.nim) with tracing
## enabled, capturing structured events in memory. Assertions are on
## event (category, kind) pairs and nesting depth — never on rendered
## text, which is allowed to change freely.
##
## Run from the repo root:
##   nim c -r --hints:off --path:src --path:src/eponym tests/elab_trace.nim
import os
import sequtils
import elab
import elab_trace

const srcOk = """
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
proc polyId {A : Type 0} (x : A) : A =
  x
proc usePolyId : Nat =
  polyId (suc zero)
proc useBare : Pi (x : Nat). Nat =
  polyId
proc applyLam : Nat =
  (lam (x : Nat). x) (suc zero)
"""

const srcBad = """
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
proc bad : Pi (x : Nat). Nat =
  lam (x : Type 0). x
"""

proc kindsOf(evs: seq[TraceEvent]): seq[string] =
  evs.mapIt(it.kind)

proc countKind(evs: seq[TraceEvent], k: string): int =
  evs.countIt(it.kind == k)

var failed = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    echo "FAIL: ", label
    inc failed

# 1. EPON_TRACE env var enables tracing at driver entry (before any
#    explicit setElabTrace call, which would take precedence).
putEnv("EPON_TRACE", "unify,meta")
maybeEnableTraceFromEnv()
check(elabTraceEnabled(), "env EPON_TRACE enables tracing")
check(parseTraceCats("unify,meta") == {tcUnify, tcMeta}, "parseTraceCats list")
check(parseTraceCats("1") == allTraceCats, "parseTraceCats 1 = all")
check(parseTraceCats("bogus") == {}, "parseTraceCats unknown = empty")
delEnv("EPON_TRACE")
setElabTrace(false)

# 2. Disabled by default: no events captured.
check(not elabTraceEnabled(), "tracing disabled by default")
startTraceCapture()
discard elabCheck(srcOk)
check(stopTraceCapture().len == 0, "disabled: no events captured")

# 3. All categories: the expected event kinds fire, scopes pair up,
#    and nesting produces depth > 0.
setElabTrace(true)
startTraceCapture()
discard elabCheck(srcOk)
let evs = stopTraceCapture()
let kinds = kindsOf(evs)
check("check.in" in kinds, "check.in fires")
check("check.out" in kinds, "check.out fires")
check("infer.in" in kinds, "infer.in fires")
check("unify.in" in kinds, "unify fires")
check("meta.assign" in kinds, "meta.assign fires")
check("implicit.insert" in kinds, "implicit.insert fires")
check("conv.goal" in kinds, "conv.goal fires")
check("conv.default" in kinds, "conv.default fires")
check("qty.check" in kinds, "qty.check fires")
check(countKind(evs, "check.in") == countKind(evs, "check.out"),
      "check scopes pair up")
check(countKind(evs, "infer.in") == countKind(evs, "infer.out"),
      "infer scopes pair up")
check(countKind(evs, "unify.in") == countKind(evs, "unify.out"),
      "unify scopes pair up")
check(evs.anyIt(it.depth > 0), "nesting produces depth > 0")

# 4. Category allow-list filtering.
setElabTrace(true, {tcUnify})
startTraceCapture()
discard elabCheck(srcOk)
let fevs = stopTraceCapture()
check(fevs.len > 0, "filtered run still emits unify events")
check(fevs.allIt(it.cat == tcUnify), "filter: only tcUnify events")
check("check.in" notin kindsOf(fevs), "filter: no check events")

# 5. Depth limit.
setElabTrace(true, allTraceCats, maxDepth = 1)
startTraceCapture()
discard elabCheck(srcOk)
let devs = stopTraceCapture()
check(devs.len > 0, "depth-limited run still emits events")
check(devs.allIt(it.depth <= 1), "depth limit respected")

# 6. Failure paths: each check logs its own .fail event, and the
#    enclosing scope still logs its .out (unwind is visible).
#    6a. Ascribed-lambda domain mismatch: since #88 the ascription site
#        is a *conversion* check (convElab), so a definitionally-unequal
#        domain logs conv.fail, not unify.fail.
setElabTrace(true)
startTraceCapture()
try:
  discard elabCheck(srcBad)
  check(false, "srcBad elaborated cleanly (expected ElabError)")
except ElabError:
  discard
let bevs = stopTraceCapture()
let bkinds = kindsOf(bevs)
check("conv.fail" in bkinds,
      "conv.fail fires on ascribed-domain mismatch (#88: conversion site)")
check(countKind(bevs, "check.in") == countKind(bevs, "check.out"),
      "check scopes pair up even on failure")

#    6b. A genuine unification failure still logs unify.fail: the pkLet
#        result check goes through unifyElab directly.
const srcBadLet = """
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
proc badLet : Type 0 =
  let x : Nat = zero in x
"""
setElabTrace(true)
startTraceCapture()
try:
  discard elabCheck(srcBadLet)
  check(false, "srcBadLet elaborated cleanly (expected ElabError)")
except ElabError:
  discard
let levs = stopTraceCapture()
let lkinds = kindsOf(levs)
check("unify.fail" in lkinds, "unify.fail fires on unification failure")
check(countKind(levs, "unify.in") == countKind(levs, "unify.out"),
      "unify scopes pair up even on failure")

setElabTrace(false)
echo "--- trace groups 1-6 done ---"

# 7. Conversion fast-fail: a constructor mismatch logs conv.noconfusion
#    at the failure point (the #80 noConfusion pre-check in defaultConv).
const srcNoConf = """
data Bit : Type 0 where
| b0 : Bit
| b1 : Bit
data Wrap : Bit -> Type 0 where
| wrap (b : Bit) : Wrap b
proc bad : Wrap b1 =
  wrap b0
"""
setElabTrace(true, {tcConv})
startTraceCapture()
try:
  discard elabCheck(srcNoConf)
  check(false, "srcNoConf elaborated cleanly (expected ElabError)")
except ElabError:
  discard
let nevs = stopTraceCapture()
let nkinds = kindsOf(nevs)
check("conv.goal" in nkinds, "conv.goal fires before the failure")
check("conv.noconfusion" in nkinds,
      "conv.noconfusion fires on constructor mismatch")
check("conv.fail" notin nkinds,
      "no conv.fail: the fast-fail pre-empts the NbE path")

setElabTrace(false)
echo "--- ", 7 - failed, "/7 trace groups ok ---"
if failed > 0: quit(1)
