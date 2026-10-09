## Scale test for issue #26: does the staged/unstaged ratio change with
## larger terms? Specializes checko(tm, Vec(Nat, 8), ctx) and compares
## unstaged relational / staged relational / direct elaborator on
## length-8 cons chains (valid and wrong-length).

import minikanren
import staging/relcompile
import staging/stage_rel_elab_dep
import rel_elab_dep
import elab
import preterm
import ett_init
import unify
import times

stagedCheckoVecNProcs(8)

const N = 8
const Iters = 30

type Case = object
  name: string
  rtm: RTerm
  pre: PreTerm
  expect: bool

proc sucN(n: int): RTerm =
  result = zeroTm()
  for i in 0 ..< n: result = sucTm(result)

proc mkCons(a, n, x, xs: PreTerm): PreTerm =
  mkApp(mkApp(mkApp(mkApp(mkVar("cons"), a), n), x), xs)

proc consChain(vals: seq[int]): RTerm =
  ## cons-chain of given Nat values, length = vals.len
  result = nilTm()
  for i in countdown(vals.len - 1, 0):
    result = consTm(sucN(vals[i]), result)

proc preChain(vals: seq[int]): PreTerm =
  let natV = mkVar("Nat")
  let nilN = mkApp(mkVar("nil"), natV)
  result = nilN
  # built inside-out: the i-th wrap has tail length vals.len-1-i
  for i in countdown(vals.len - 1, 0):
    result = mkCons(natV, mkInt(vals.len - 1 - i), mkInt(vals[i]), result)

proc buildCases(): seq[Case] =
  result = @[]
  let ascending = @[0, 1, 2, 3, 4, 5, 6, 7]
  result.add(Case(name: "cons-chain len 8 (valid)",
    rtm: consChain(ascending), pre: preChain(ascending), expect: true))
  let zeros = @[0, 0, 0, 0, 0, 0, 0, 0]
  result.add(Case(name: "cons-chain len 8 zeros (valid)",
    rtm: consChain(zeros), pre: preChain(zeros), expect: true))
  let short = @[0, 1, 2, 3, 4, 5, 6]
  result.add(Case(name: "cons-chain len 7 (wrong idx)",
    rtm: consChain(short), pre: preChain(short), expect: false))
  result.add(Case(name: "nil (wrong idx)",
    rtm: nilTm(), pre: preChain(@[]), expect: false))

proc checkUnstaged(tm: RTerm): bool =
  let ty = vecTy(natTy(), sucN(N))
  let g = checko(tm, ty, rnil())
  run(freshVar(), g, 1).len > 0

proc checkStaged(tm: RTerm): bool =
  let g = stagedCheckoVecN(tm, rnil())
  run(freshVar(), g, 1).len > 0

when isMainModule:
  let cases = buildCases()
  let setupSrc = """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
"""
  var (globals, ms0, supply0) = elabPrelude(setupSrc)
  # Build Vec Nat (suc^N zero) via a dummy def with a valid length-N body,
  # mirroring bench_rel_elab.nim.
  proc surfNat(i: int): string =
    result = "zero"
    for j in 0 ..< i: result = "suc (" & result & ")"
  let ascending = @[0, 1, 2, 3, 4, 5, 6, 7]
  var bodySrc = "nil Nat"
  for i in countdown(N - 1, 0):
    # built inside-out: the i-th wrap has tail length N-1-i
    bodySrc = "cons Nat (" & surfNat(N - 1 - i) & ") (" & surfNat(ascending[i]) &
      ") (" & bodySrc & ")"
  let dummySrc = setupSrc & "proc dummy : Vec Nat (" & surfNat(N) & ") =\n  " &
    bodySrc & "\n"
  let dummyDefs = elabCheck(dummySrc)
  let vecNatN = dummyDefs[^1].tyTm

  proc checkDirect(pre: PreTerm): bool =
    var ms = initMetaStore()
    var supply = Supply()
    try:
      discard checkTermElab(pre, @[], globals, ms, supply, vecNatN)
      true
    except ElabError:
      false

  echo "=== Correctness (N=", N, ") ==="
  for c in cases:
    let u = checkUnstaged(c.rtm)
    let s = checkStaged(c.rtm)
    let d = checkDirect(c.pre)
    let ok = (u == c.expect) and (s == c.expect) and (d == c.expect)
    echo c.name, ": unstaged=", u, " staged=", s, " direct=", d,
         " expected=", c.expect, " ", (if ok: "OK" else: "MISMATCH")

  echo "\n=== Performance (ms/iter, ", Iters, " iters) ==="
  for c in cases:
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
