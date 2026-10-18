## Runtime bridge checks for Eponym values that do not use the generated Int ABI.

import std/[os, tables]
import falsify
import eponym_embed
import elab
import eponym_init

const program = """
postulate Int : Type 0
proc double : Int -> Int = lam (n : Int). addInt n n
postulate Nat : Type 0
proc idNat : Nat -> Nat = lam (n : Nat). n
"""

proc hostStepNim(value: int): int = value + 7
proc hostTripleNim(value: int): int = value * 3
proc hostString(value: string): string = value

static:
  doAssert compiles(hostIntUnary(hostStepNim))
  doAssert not compiles(hostIntUnary(hostString))

when isMainModule:
  let baseDir = currentSourcePath().parentDir.parentDir
  var r = initRng(424242'u64)

  let intRoundTrips = forAll("runtime Int Values through checked definitions",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      let value = callValueFuncDir(baseDir, program, "double",
        @[intToValue(n)])
      valueToInt(value) == n * 2,
    shrinkInt)

  let natRoundTrips = forAll("runtime Nat Values through checked definitions",
    r, 200,
    proc(r: var Rng): int = r.genInt(0, 1000),
    proc(n: int): bool =
      let value = callValueFuncDir(baseDir, program, "idNat",
        @[natToValue(n)])
      valueToNat(value) == n,
    shrinkInt)

  # Keep the original generated-wrapper helper working through the shared
  # Value-based evaluator path.
  let compat = callIntFuncDir(baseDir, program, "double", @[21]) == 42

  var rejectedNegativeNat = false
  try:
    discard natToValue(-1)
  except ValueError:
    rejectedNegativeNat = true
  if not (intRoundTrips and natRoundTrips and compat and rejectedNegativeNat):
    quit(1)

  # The runtime-binding work needs the exact global identities assigned by
  # the checker. Confirm a definition body refers to the same postulate
  # reference exposed in the returned state.
  const identityProgram = """
import "tests/fixtures/runtime_host_step.ep"
proc throughHelper : Int -> Int = lam (n : Int). importedHelper n
"""
  let checked = elabCheckDirState(identityProgram, baseDir)
  let postulateId = checked.globals["hostStep"].tm.refId
  let cachedGlobals = getGlobalsDir(baseDir, identityProgram)
  if cachedGlobals["hostStep"].tm.refId != postulateId:
    quit(1)
  var runtimeBindings = initRuntimeBindings()
  runtimeBindings.bindHostIntUnary(cachedGlobals, "hostStep", hostStepNim)
  let hostResult = callValueFuncDir(baseDir, identityProgram,
    "throughHelper", @[intToValue(35)], runtimeBindings)
  if valueToInt(hostResult) != 42:
    quit(1)

  let hostDispatch = forAll("checked definitions dispatch to typed Nim postulates",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      var bindings = initRuntimeBindings()
      bindings.bindHostIntUnary(cachedGlobals, "hostStep", hostStepNim)
      let value = callValueFuncDir(baseDir, identityProgram, "throughHelper",
        @[intToValue(n)], bindings)
      valueToInt(value) == hostStepNim(n),
    shrinkInt)
  if not hostDispatch:
    quit(1)

  let alternateHostDispatch = forAll("runtime bindings stay local to each call",
    r, 200,
    proc(r: var Rng): int = r.genInt(-1000, 1000),
    proc(n: int): bool =
      var bindings = initRuntimeBindings()
      bindings.bindHostIntUnary(cachedGlobals, "hostStep", hostTripleNim)
      let value = callValueFuncDir(baseDir, identityProgram, "throughHelper",
        @[intToValue(n)], bindings)
      valueToInt(value) == hostTripleNim(n),
    shrinkInt)
  if not alternateHostDispatch:
    quit(1)

  var wrongEponymTypeRejected = false
  try:
    var wrongTypeBindings = initRuntimeBindings()
    wrongTypeBindings.bindHostIntUnary(cachedGlobals, "hostNat", hostStepNim)
  except ValueError:
    wrongEponymTypeRejected = true
  var duplicateBindingRejected = false
  try:
    runtimeBindings.bindHostIntUnary(cachedGlobals, "hostStep", hostStepNim)
  except ValueError:
    duplicateBindingRejected = true
  if not wrongEponymTypeRejected or not duplicateBindingRejected:
    quit(1)

  echo "test_runtime_value_bridge: Value calls, postulate identity, and typed host dispatch ok"
