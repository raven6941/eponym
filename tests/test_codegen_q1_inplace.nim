## Issue #413: q1-gated in-place reuse — sink params + single-var chain lift.
##
## Part A uses the shared `differentialBlockRepr` driver
## (`tests/codegen_phase2_differential.nim`): a corpus of List chains over
## q1-parameter step definitions. Each repr proc is checked against the
## interpreter (`callValueFuncDir`) and its Phase-1 compiled twin
## (differential soundness of the lift), and the emitted ASTs are
## structurally asserted: q1 seq formals are `sink`, lifted chains emit
## one `var` with `move` at the step sites, and non-qualifying shapes keep
## ordinary `let` emission.
##
## Part B uses `eponymBlock` with `requireCompiled()` for the in-place
## host step: `lpush` is postulate-bound (`bindPostulate`) to a host proc
## that appends in place on a `sink` buffer. A chain of pushes must cost
## one head copy + amortized O(1) appends (the #19 framing: O(n + k) for
## k pushes, not O(k·n) buffer copies).

import std/macros
import codegen_phase2_differential

const progA = """postulate(Int, Univ)
data(List, [A : Univ], Univ) where
| nil : List A
| cons (x : A) (xs : List A) : List A
proc lcons1 (1 xs : List Int) (x : Int) : List Int =
  cons Int x xs
proc chain3 (xs : List Int) (p1 : Int) (p2 : Int) (p3 : Int) : List Int =
  let a = lcons1 xs p1 in
  let b = lcons1 a p2 in
  lcons1 b p3
proc ladd2 (1 ys : List Int) (q1 : Int) (q2 : Int) : List Int =
  let b = lcons1 ys q1 in
  lcons1 b q2
proc chainAcross (xs : List Int) (p1 : Int) (q1 : Int) (q2 : Int) : List Int =
  let a = lcons1 xs p1 in
  let b = ladd2 a q1 q2 in
  lcons1 b p1
proc lappendPure (xs : List Int) (ys : List Int) : List Int =
  listElim Int (lam(u: List Int) => List Int)
           ys
           (lam(x: Int) => lam(tl: List Int) => lam(ih: List Int) => cons Int x ih)
           xs
proc noLiftDup (xs : List Int) (p1 : Int) : List Int =
  let a = lcons1 xs p1 in
  lappendPure a a
proc noLiftAlias (1 xs : List Int) (p1 : Int) : List Int =
  let a = xs in
  lcons1 a p1
proc betaChainSeq (xs : List Int) (p1 : Int) : List Int =
  let a = lcons1 xs p1 in
  let b = (lam(u: Int) => lcons1 a u) p1 in
  lcons1 b p1
"""

differentialBlockRepr(progA, currentSourcePath(), "Int:int,List:list")

let qaGlobals = getGlobals(progA)

proc intEnc(x: int, g: Globals): Value = intToValue(x)
proc intDec(v: Value, g: Globals): int = valueToInt(v)

proc listArg(items: seq[int]): Value =
  seqToListValue(items, qaGlobals, "List", intEnc)

proc checkChain(name: string, args: seq[Value], expected: seq[int],
                reprCall: proc(): seq[int]) =
  ## Repr proc vs literal expectation, vs the interpreter, vs the Phase-1
  ## compiled twin.
  doAssert name in reprCompiledNames(), name & " has a repr proc"
  let gotRepr = reprCall()
  doAssert gotRepr == expected, name & " repr gave " & $gotRepr &
    ", want " & $expected
  let bnd = testPostulateBindings()
  let want = callValueFuncDir("", progA, name, args, bnd)
  doAssert listValueToSeq[int](want, qaGlobals, "List", intDec) == expected,
    name & " interpreter disagrees"
  let got1 = case name
    of "chain3": eponymCompiled_chain3(args, bnd)
    of "chainAcross": eponymCompiled_chainAcross(args, bnd)
    of "noLiftDup": eponymCompiled_noLiftDup(args, bnd)
    of "noLiftAlias": eponymCompiled_noLiftAlias(args, bnd)
    of "betaChainSeq": eponymCompiled_betaChainSeq(args, bnd)
    else: raise newException(ValueError, "unknown def " & name)
  doAssert listValueToSeq[int](got1, qaGlobals, "List", intDec) == expected,
    name & " value backend disagrees"

macro emissionFlags(p: typed): untyped =
  ## Structural facts about an emitted repr proc: does any formal use
  ## `sink`, does the body declare a `var` section (the lifted chain
  ## buffer), and does it call `move`.
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

## Part B: `requireCompiled()` + `bindPostulate` in-place host step.
##
## `lpush` is postulate-bound to a host proc that appends in place on a
## `sink` buffer. The forwarder must mark its q1 seq formal `sink` (so the
## lifted chain's `move`d buffer reaches the host proc without a copy), a
## chain of pushes through linear lets must lift to one `var` with moves,
## and the typed wrapper must not mutate a caller-retained buffer (the
## wrapper-boundary ownership rule: `sink` is a move hint only, so an lvalue
## argument is copied once at entry).

proc lpushHost(xs: sink seq[int], x: int): seq[int] =
  result = xs
  result.add(x)

eponymBlock:
  requireCompiled()
  import "../lib/list.ep"
  postulate(Int, Univ)
  runtimeType(Int, int)
  runtimeList(List)
  postulate(lpush, Pi(xs {.linear.}: List[Int], x: Int, List[Int]))
  bindPostulate(lpush, lpushHost, List, Int, List)
  proc pushChain(xs {.linear.}: List[Int], a: Int, b: Int,
                 c: Int): List[Int] =
    let x1 = lpush(xs, a)
    let x2 = lpush(x1, b)
    lpush(x2, c)

when isMainModule:
  # Structural assertions on the emitted code.
  block:
    let f = emissionFlags(eponymCompiledRepr_lcons1)
    doAssert f.sink, "q1 seq formal of lcons1 should be sink"
    doAssert not f.varSection, "lcons1 has no chain to lift"
  block:
    let f = emissionFlags(eponymCompiledRepr_chain3)
    doAssert f.sink, "chain3's used-once xs is inferred q1: sink formal"
    doAssert f.varSection, "chain3 should lift to a single var"
    doAssert f.move, "chain3 steps should move the buffer"
  block:
    let f = emissionFlags(eponymCompiledRepr_chainAcross)
    doAssert f.sink, "chainAcross's used-once xs is inferred q1: sink formal"
    doAssert f.varSection, "chainAcross should lift its local chain"
    doAssert f.move, "chainAcross steps should move the buffer"
  block:
    let f = emissionFlags(eponymCompiledRepr_noLiftDup)
    doAssert not f.varSection, "noLiftDup reuses its binding: no lift"
    doAssert not f.move, "noLiftDup must not move a reused buffer"
  block:
    let f = emissionFlags(eponymCompiledRepr_noLiftAlias)
    doAssert not f.varSection, "noLiftAlias head aliases a variable: no lift"
  block:
    # The redex step keeps its lambda textually, so the guard
    # conservatively declines the OUTER chain (the use is under a binder
    # in the unreduced term) — but `cgReprApp` beta-reduces the redex to
    # straight-line code whose inner call moves the buffer through its
    # `sink` formal, so nothing is copied either way. The single inner
    # binding still lifts; differential soundness below covers the shape.
    let f = emissionFlags(eponymCompiledRepr_betaChainSeq)
    doAssert f.varSection, "betaChainSeq's inner binding lifts"
    doAssert not f.move, "single-binding lift has no step to move"

  # Differential soundness over several inputs.
  for xs in [@[], @[7], @[1, 2, 3, 4]]:
    let args3 = @[listArg(xs), intToValue(1), intToValue(2), intToValue(3)]
    checkChain("chain3", args3, @[3, 2, 1] & xs,
      proc(): seq[int] = eponymCompiledRepr_chain3(xs, 1, 2, 3))
    checkChain("chainAcross", args3, @[1, 3, 2, 1] & xs,
      proc(): seq[int] = eponymCompiledRepr_chainAcross(xs, 1, 2, 3))
    checkChain("noLiftDup", @[listArg(xs), intToValue(1)],
      (@[1] & xs) & (@[1] & xs),
      proc(): seq[int] = eponymCompiledRepr_noLiftDup(xs, 1))
    checkChain("noLiftAlias", @[listArg(xs), intToValue(1)], @[1] & xs,
      proc(): seq[int] = eponymCompiledRepr_noLiftAlias(xs, 1))
    checkChain("betaChainSeq", @[listArg(xs), intToValue(1)],
      @[1, 1, 1] & xs,
      proc(): seq[int] = eponymCompiledRepr_betaChainSeq(xs, 1))

  echo "test_codegen_q1_inplace: part A (pure chains) passed"

  # Part B: in-place host step under requireCompiled().
  block:
    let f = emissionFlags(eponymCompiledRepr_lpush)
    doAssert f.sink, "lpush forwarder formal should be sink (q1 seq)"
    doAssert not f.varSection, "lpush forwarder has no chain to lift"
  block:
    let f = emissionFlags(eponymCompiledRepr_pushChain)
    doAssert f.sink, "pushChain's used-once xs is q1: sink formal"
    doAssert f.varSection, "pushChain should lift to a single var"
    doAssert f.move, "pushChain steps should move the buffer"
  # Runtime behavior: correct results.
  doAssert pushChain(@[1, 2], 3, 4, 5) == @[1, 2, 3, 4, 5],
    "pushChain result wrong"
  doAssert pushChain(@[], 1, 2, 3) == @[1, 2, 3],
    "pushChain on empty head wrong"
  # Wrapper-boundary ownership: a caller-retained buffer is never mutated.
  var retained = @[10, 20]
  let snapshot = retained
  doAssert pushChain(retained, 30, 40, 50) == @[10, 20, 30, 40, 50],
    "pushChain on retained buffer gave wrong result"
  doAssert retained == snapshot,
    "typed wrapper mutated the caller-retained buffer: " & $retained
  echo "test_codegen_q1_inplace: part B (in-place host step) passed"
