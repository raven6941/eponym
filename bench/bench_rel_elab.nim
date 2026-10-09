## Fair benchmark: unstaged relational vs staged relational vs direct elaborator
##
## Issue #26: clean comparison of the two styles on the Vec fragment.
## Methodology (from bench_vs_elab.nim):
## - Same terms on all sides, native representations, built once from a
##   shared spec — no parsing or translation inside the timed loop.
## - Staged side: stagedCheckoVec2 (compiled residual, ty=Vec(Nat,2) static).
## - Unstaged side: checko from rel_elab_dep.
## - Direct side: checkTermElab against Vec Nat 2 with fresh MetaStore.

import minikanren
import staging/relcompile
import staging/stage_rel_elab_dep
import rel_elab_dep
import elab
import preterm
import ett_init
import unify
import times

stagedCheckoVec2Procs()

const Iters = 50

type Case = object
  name: string
  rtm: RTerm      # relational-side term
  pre: PreTerm    # elaborator-side term
  expect: bool

proc buildCases(): seq[Case] =
  # Helper: cons A n x xs as PreTerm
  proc mkCons(a, n, x, xs: PreTerm): PreTerm =
    mkApp(mkApp(mkApp(mkApp(mkVar("cons"), a), n), x), xs)
  let natV = mkVar("Nat")
  let nilN = mkApp(mkVar("nil"), natV)
  result = @[]
  # Valid: cons-chains of length 2: [0, 0]
  let tail00 = mkCons(natV, mkInt(0), mkInt(0), nilN)
  let vec00 = mkCons(natV, mkInt(1), mkInt(0), tail00)
  result.add(Case(name: "cons(0,cons(0,nil))",
    rtm: consTm(zeroTm(), consTm(zeroTm(), nilTm())),
    pre: vec00,
    expect: true))
  # Valid: [1, 2]
  let tail12 = mkCons(natV, mkInt(0), mkInt(2), nilN)
  let vec12 = mkCons(natV, mkInt(1), mkInt(1), tail12)
  result.add(Case(name: "cons(1,cons(2,nil))",
    rtm: consTm(sucTm(zeroTm()), consTm(sucTm(sucTm(zeroTm())), nilTm())),
    pre: vec12,
    expect: true))
  # Invalid: wrong length (nil : Vec Nat 0, not Vec Nat 2)
  result.add(Case(name: "nil (wrong idx)",
    rtm: nilTm(),
    pre: nilN,
    expect: false))
  # Invalid: wrong length ([0] : Vec Nat 1, not Vec Nat 2)
  result.add(Case(name: "cons(0,nil) (wrong idx)",
    rtm: consTm(zeroTm(), nilTm()),
    pre: mkCons(natV, mkInt(0), mkInt(0), nilN),
    expect: false))
  # Invalid: wrong type (zero : Nat, not Vec)
  result.add(Case(name: "zero (not a vec)",
    rtm: zeroTm(),
    pre: mkVar("zero"),
    expect: false))

proc checkUnstaged(tm: RTerm): bool =
  let ty = vecTy(natTy(), sucTm(sucTm(zeroTm())))
  let g = checko(tm, ty, rnil())
  run(freshVar(), g, 1).len > 0

proc checkStaged(tm: RTerm): bool =
  let g = stagedCheckoVec2(tm, rnil())
  run(freshVar(), g, 1).len > 0

proc checkDirect(pre: PreTerm, globals: Globals, vecNat2: Term): bool =
  var ms = initMetaStore()
  var supply = Supply()
  try:
    discard checkTermElab(pre, @[], globals, ms, supply, vecNat2)
    true
  except ElabError:
    false

when isMainModule:
  let cases = buildCases()
  # Setup: elaborate prelude once, reuse state
  let setupSrc = """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
"""
  var (globals, ms0, supply0) = elabPrelude(setupSrc)
  # Build Vec Nat 2 as a Term: elaborate a dummy def and take its type
  let dummySrc = setupSrc & """
proc dummy : Vec Nat (suc (suc zero)) =
  cons Nat (suc zero) zero (cons Nat zero zero (nil Nat))
"""
  let dummyDefs = elabCheck(dummySrc)
  let vecNat2 = dummyDefs[^1].tyTm

  proc checkDirect(pre: PreTerm): bool =
    var ms = initMetaStore()
    var supply = Supply()
    try:
      discard checkTermElab(pre, @[], globals, ms, supply, vecNat2)
      true
    except ElabError:
      false

  echo "=== Correctness ==="
  for c in cases:
    let u = checkUnstaged(c.rtm)
    let s = checkStaged(c.rtm)
    let d = checkDirect(c.pre)
    let ok = (u == c.expect) and (s == c.expect) and (d == c.expect)
    echo c.name, ": unstaged=", u, " staged=", s, " direct=", d,
         " expected=", c.expect, " ", (if ok: "OK" else: "MISMATCH")

  echo "\n=== Performance (ms/iter, ", Iters, " iters) ==="
  for c in cases:
    # warmup
    discard checkUnstaged(c.rtm); discard checkStaged(c.rtm)
    discard checkDirect(c.pre)
    let t0 = cpuTime()
    for i in 0 ..< Iters: discard checkUnstaged(c.rtm)
    let tu = (cpuTime() - t0) / Iters * 1000
    let t1 = cpuTime()
    for i in 0 ..< Iters: discard checkStaged(c.rtm)
    let ts = (cpuTime() - t1) / Iters * 1000
    let t2 = cpuTime()
    for i in 0 ..< Iters: discard checkDirect(c.pre)
    let td = (cpuTime() - t2) / Iters * 1000
    echo c.name, ": unstaged=", tu, "ms staged=", ts, "ms direct=", td, "ms",
         " (staged/unstaged=", ts/tu, "x, staged/direct=", ts/td, "x)"
