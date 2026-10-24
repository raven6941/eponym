## Issue #413 slice 2: q1-gated in-place reuse at scalar type.
##
## Aaron's 2026-10-22 scope clarification: a chain of logically immutable
## INTs with a linearity finding is the same transform as the seq case —
## one `var acc: int` mutated per step — for NON-fold chains (an int
## accumulator threaded through separately compiled definitions, returned
## and re-entered). At the Nim level an int copy is a register move, so
## this is a stay-on-the-fast-path win rather than an asymptotic one; the
## q1 finding is what licenses treating the chain uniformly and keeps it
## off the paths that reintroduce per-step costs.
##
## Uses the shared `differentialBlockRepr` driver
## (`tests/codegen_phase2_differential.nim`): each repr proc is checked
## against the interpreter (`callValueFuncDir`) and its Phase-1 compiled
## twin, and the emitted ASTs are structurally asserted (lifted int
## chains emit one `var` with plain reassignment — no `move`, no `sink`
## on int formals; non-qualifying shapes keep ordinary `let` emission).
## Slice 2 also adds a closure-capture guard to the lift (a step that
## mentions the previous variable only under a lambda does not lift: a
## single syntactic occurrence under a binder is not an exactly-once
## runtime use, and `move` inside a multiply-invoked closure would be
## unsound). The guard is currently defensive — the repr fragment does
## not admit surviving closures in step position (immediately-applied
## lambdas are beta-reduced by the elaborator; let-bound or argument
## closures keep the whole def on the Phase-1 path) — so it is documented
## rather than differentially exercised here.

import std/macros
import codegen_phase2_differential

const progB = """postulate Int : Type 0
proc inc (1 acc : Int) (d : Int) : Int = addInt acc d
proc incTwice (1 acc : Int) (p : Int) (q : Int) : Int =
  let x = inc acc p in inc x q
proc chainI (a : Int) (p1 : Int) (p2 : Int) (p3 : Int) : Int =
  let x = inc a p1 in
  let y = inc x p2 in
  inc y p3
proc chainIAcross (a : Int) (p1 : Int) (p2 : Int) (p3 : Int) : Int =
  let x = inc a p1 in
  let y = incTwice x p2 p3 in
  inc y p1
proc chainIAlias (a : Int) (p1 : Int) (p2 : Int) : Int =
  let x = a in
  let y = inc x p1 in
  inc y p2
proc noLiftIntDup (a : Int) (p1 : Int) : Int =
  let x = inc a p1 in addInt x x
proc betaChain (a : Int) (p1 : Int) : Int =
  let x = inc a p1 in
  let y = (lam (u : Int). addInt x u) p1 in
  inc y p1
"""

differentialBlockRepr(progB, currentSourcePath(), "Int:int")

proc checkChainI(name: string, args: seq[Value], expected: int,
                reprCall: proc(): int) =
  ## Repr proc vs literal expectation, vs the interpreter, vs the Phase-1
  ## compiled twin.
  doAssert name in reprCompiledNames(), name & " has a repr proc"
  let gotRepr = reprCall()
  doAssert gotRepr == expected, name & " repr gave " & $gotRepr &
    ", want " & $expected
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", progB, name, args, bnd)
  doAssert valueToInt(want) == expected, name & " interpreter disagrees"
  let got1 = case name
    of "chainI": eponymCompiled_chainI(args, bnd)
    of "chainIAcross": eponymCompiled_chainIAcross(args, bnd)
    of "chainIAlias": eponymCompiled_chainIAlias(args, bnd)
    of "noLiftIntDup": eponymCompiled_noLiftIntDup(args, bnd)
    of "betaChain": eponymCompiled_betaChain(args, bnd)
    else: raise newException(ValueError, "unknown def " & name)
  doAssert valueToInt(got1) == expected, name & " value backend disagrees"

macro emissionFlags(p: typed): untyped =
  ## Structural facts about an emitted repr proc: does any formal use
  ## `sink`, does the body declare a `var` section (the lifted chain
  ## accumulator), and does it call `move`.
  let impl = getImpl(p)
  var hasSink = false
  var hasVarSection = false
  var hasMove = false
  proc walk(n: NimNode) =
    if n.kind == nnkCommand and n.len > 0 and $n[0] == "sink":
      hasSink = true
    if n.kind == nnkVarSection:
      hasVarSection = true
    if n.kind == nnkCall and n.len > 0 and $n[0] == "move":
      hasMove = true
    for c in n:
      walk(c)
  walk(impl)
  result = newTree(nnkTupleConstr,
    newTree(nnkExprColonExpr, ident"sink", newLit(hasSink)),
    newTree(nnkExprColonExpr, ident"varSection", newLit(hasVarSection)),
    newTree(nnkExprColonExpr, ident"move", newLit(hasMove)))

when isMainModule:
  # Structural assertions on the emitted code.
  block:
    let f = emissionFlags(eponymCompiledRepr_inc)
    doAssert not f.sink, "q1 INT formal is not sink (value type: no buffer)"
    doAssert not f.varSection, "inc has no chain to lift"
  block:
    let f = emissionFlags(eponymCompiledRepr_chainI)
    doAssert f.varSection, "chainI should lift to a single var accumulator"
    doAssert not f.move, "int steps reassign; they never move"
  block:
    let f = emissionFlags(eponymCompiledRepr_chainIAcross)
    doAssert f.varSection, "chainIAcross should lift its cross-call chain"
    doAssert not f.move, "int steps reassign; they never move"
  block:
    let f = emissionFlags(eponymCompiledRepr_chainIAlias)
    doAssert f.varSection, "int chain with alias head still lifts (value copy)"
    doAssert not f.move, "int steps reassign; they never move"
  block:
    let f = emissionFlags(eponymCompiledRepr_noLiftIntDup)
    doAssert not f.varSection, "noLiftIntDup reuses its binding: no lift"
  block:
    # As in betaChainSeq (Part A): the redex step is reduced by cgReprApp
    # to straight-line code, but the guard conservatively declines the
    # outer chain on the unreduced term; the single inner binding lifts.
    # Differential soundness below covers the shape.
    let f = emissionFlags(eponymCompiledRepr_betaChain)
    doAssert f.varSection, "betaChain's inner binding lifts"
    doAssert not f.move, "int steps reassign; they never move"

  # Differential soundness over several inputs.
  for a in @[0, 7, 41]:
    let args = @[intToValue(a), intToValue(1), intToValue(2), intToValue(3)]
    checkChainI("chainI", args, a + 6,
      proc(): int = eponymCompiledRepr_chainI(a, 1, 2, 3))
    checkChainI("chainIAcross", args, a + 7,
      proc(): int = eponymCompiledRepr_chainIAcross(a, 1, 2, 3))
    checkChainI("chainIAlias", @[intToValue(a), intToValue(1), intToValue(2)],
      a + 3, proc(): int = eponymCompiledRepr_chainIAlias(a, 1, 2))
    checkChainI("noLiftIntDup", @[intToValue(a), intToValue(1)],
      2 * (a + 1), proc(): int = eponymCompiledRepr_noLiftIntDup(a, 1))
    checkChainI("betaChain", @[intToValue(a), intToValue(1)],
      a + 3, proc(): int = eponymCompiledRepr_betaChain(a, 1))

  echo "test_codegen_q1_inplace_scalar: part B (scalar chains) passed"
