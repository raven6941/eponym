## #170 benchmark: lattice-monotone prototype vs the staged-relational
## engine on invalid cases (fast-fail), and vs the direct elaborator on
## valid cases.
##
## Engines (same programs, native representations, built once outside the
## timed loop — the bench_elab_end_to_end.nim fairness discipline):
## - lattice:  checkLatTop from src/experimental/relational/lattice_elab.nim
## - engine:   stagedCheckoVec2 from tests/stage_rel_elab_dep.nim — the
##             #143 staged-relational engine (16.0-26.8x slower than direct
##             on invalids); ty = Vec Nat 2 is static, so it only runs the
##             invalid-scaling table where ty is fixed.
## - unstaged: run(freshVar(), checko(tm, ty, ctx), 1) — search-exhaustion
##             baseline.
## - residual: elaboD from src/experimental/staging/gen_elabo_full.nim (#57's
##             generated-direct residual, general ty).
## - direct:   checkTermElab with a fresh MetaStore + Supply per iteration.
##
## Corpus: scaled cons-chains (zeros). Invalid table: cons^n : Vec Nat 2
## for n != 2 (plus the two shape-mismatch corpus NEGs); valid table:
## cons^n : Vec Nat n. The issue's target: invalid-case latency
## proportional to input size on the lattice side, no exhaustion blowup.
##
## Usage: nim c -r --path:src --path:src/eponym --path:src/experimental/relational \
##   --path:src/experimental/staging --path:tests bench/bench_lattice_elab.nim

import minikanren
import staging/relcompile
import rel_elab_dep
import lattice_elab
import options
import stage_rel_elab_dep
import staging/gen_elabo_full
import elab
import preterm
import eponym_init
import unify
import times
import strformat
import strutils

stagedCheckoVec2Procs()

# --- Term builders ------------------------------------------------------------

proc mkConsChainR(n: int): RTerm =
  result = nilTm()
  for _ in 1 .. n: result = consTm(zeroTm(), result)

proc mkVecTyR(k: int): RTerm = vecTy(natTy(), rint(k))

type Case = object
  name: string
  rtm, rty, rctx: RTerm
  pre: PreTerm
  dty: Term
  expect: bool

# --- Engines ------------------------------------------------------------------

proc vLattice(tm, ty, ctx: RTerm): bool = checkLatTop(tm, ty, ctx).ok

proc vUnstaged(tm, ty, ctx: RTerm): bool =
  run(freshVar(), checko(tm, ty, ctx), 1).len > 0

proc vEngine(tm, ctx: RTerm): bool =
  ## #143's staged-relational engine; ty = Vec Nat 2 is compiled in.
  run(freshVar(), stagedCheckoVec2(tm, ctx), 1).len > 0

proc vResidual(tm, ty, ctx: RTerm): bool = elaboD(tm, ty, ctx).isSome

proc vDirect(pre: PreTerm, dty: Term, globals: Globals): bool =
  var ms = initMetaStore()
  var supply = Supply()
  try:
    discard checkTermElab(pre, @[], globals, ms, supply, dty)
    true
  except ElabError:
    false

# --- Timing -------------------------------------------------------------------

proc timeIt(reps: int, body: proc()): float =
  result = high(float)
  for _ in 1 .. reps:
    let t0 = cpuTime()
    body()
    result = min(result, (cpuTime() - t0) * 1e6)  # microseconds

proc timeAdaptive(work: proc()): tuple[us: float, note: string] =
  ## One warmup call sets the rep count; >10s single call is reported as
  ## a blowout rather than timed (that *is* the finding).
  let t0 = cpuTime()
  work()
  let single = (cpuTime() - t0) * 1e6
  if single > 10_000_000.0:
    return (single, ">10s")
  let reps = if single > 200_000.0: 3 elif single > 20_000.0: 10 else: 30
  (timeIt(reps, work), "")

proc fmtCell(us: float, note: string): string =
  if note != "": note.align(10)
  else: fmt"{us:>10.1f}"

when isMainModule:
  # --- Setup (mirrors bench_rel_elab.nim / bench_elab_end_to_end.nim) ---------
  let setupSrc = """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
"""
  var (globals, _, _) = elabPrelude(setupSrc)
  let dummySrc = setupSrc & """
proc dummy : Vec Nat (suc (suc zero)) =
  cons Nat (suc zero) zero (cons Nat zero zero (nil Nat))
"""
  let dummyDefs = elabCheck(dummySrc)
  let vecNat2 = dummyDefs[^1].tyTm

  let natV = mkVar("Nat")
  proc mkCons(a, n, x, xs: PreTerm): PreTerm =
    mkApp(mkApp(mkApp(mkApp(mkVar("cons"), a), n), x), xs)
  proc mkConsChainP(n: int): PreTerm =
    result = mkApp(mkVar("nil"), natV)
    for k in 0 ..< n:
      result = mkCons(natV, mkInt(k), mkInt(0), result)
  proc mkVecTyT(k: int): Term =
    var ms = initMetaStore(); var supply = Supply()
    checkTermElab(mkApp(mkApp(mkVar("Vec"), natV), mkInt(k)),
                  @[], globals, ms, supply, tmC(cStar))

  let vec2R = mkVecTyR(2)
  let nilCtxR = rnil()

  # --- Invalid-scaling table: cons^n (zeros) : Vec Nat 2, n != 2 --------------
  var invalidCases: seq[Case] = @[]
  for n in [0, 1, 4, 8, 16, 32, 64]:
    invalidCases.add(Case(
      name: "cons^" & $n & " : Vec Nat 2",
      rtm: mkConsChainR(n), rty: vec2R, rctx: nilCtxR,
      pre: mkConsChainP(n), dty: vecNat2, expect: false))
  invalidCases.add(Case(name: "NEG 1 : Vec Nat 2",
    rtm: sucTm(zeroTm()), rty: vec2R, rctx: nilCtxR,
    pre: mkInt(1), dty: vecNat2, expect: false))

  # --- Valid-scaling table: cons^n (zeros) : Vec Nat n ------------------------
  var validCases: seq[Case] = @[]
  for n in [2, 4, 8, 16]:
    validCases.add(Case(
      name: "cons^" & $n & " : Vec Nat " & $n,
      rtm: mkConsChainR(n), rty: mkVecTyR(n), rctx: nilCtxR,
      pre: mkConsChainP(n), dty: mkVecTyT(n), expect: true))

  # --- Correctness gate: every engine agrees with the expected verdict --------
  echo "== correctness =="
  var bad = 0
  for c in invalidCases & validCases:
    let l = vLattice(c.rtm, c.rty, c.rctx)
    let u = vUnstaged(c.rtm, c.rty, c.rctx)
    let r = vResidual(c.rtm, c.rty, c.rctx)
    let d = vDirect(c.pre, c.dty, globals)
    var line = c.name & ": lattice=" & $l & " unstaged=" & $u &
      " residual=" & $r & " direct=" & $d & " expected=" & $c.expect
    var ok = (l == c.expect) and (u == c.expect) and
             (r == c.expect) and (d == c.expect)
    if c.name.endsWith(": Vec Nat 2"):
      let e = vEngine(c.rtm, c.rctx)
      line &= " engine=" & $e
      ok = ok and (e == c.expect)
    echo line, " ", (if ok: "OK" else: "MISMATCH")
    if not ok: inc bad
  if bad > 0:
    echo bad, " verdict mismatches — aborting"
    quit(1)

  # --- Invalid-case latency: the #170 target ----------------------------------
  echo ""
  echo "== invalid cases: rejection latency (microseconds, best-of adaptive) =="
  echo "case".alignLeft(24) & "lattice".align(10) & "engine".align(10) &
    "unstaged".align(10) & "residual".align(10) & "direct".align(10) &
    " eng/dir".align(10) & " lat/dir".align(10)
  for c in invalidCases:
    let (tL, nL) = timeAdaptive(proc() = discard vLattice(c.rtm, c.rty, c.rctx))
    let (tE, nE) = timeAdaptive(proc() = discard vEngine(c.rtm, c.rctx))
    let (tU, nU) = timeAdaptive(proc() = discard vUnstaged(c.rtm, c.rty, c.rctx))
    let (tR, nR) = timeAdaptive(proc() = discard vResidual(c.rtm, c.rty, c.rctx))
    let (tD, nD) = timeAdaptive(proc() = discard vDirect(c.pre, c.dty, globals))
    let engDir = if nE == "" and nD == "" and tD > 0: fmt"{tE/tD:>9.1f}x" else: " ".align(10)
    let latDir = if nL == "" and nD == "" and tD > 0: fmt"{tL/tD:>9.1f}x" else: " ".align(10)
    echo c.name.alignLeft(24) & fmtCell(tL, nL) & fmtCell(tE, nE) &
      fmtCell(tU, nU) & fmtCell(tR, nR) & fmtCell(tD, nD) & engDir & latDir

  # --- Valid-case latency vs direct -------------------------------------------
  echo ""
  echo "== valid cases: latency (microseconds, best-of adaptive) =="
  echo "case".alignLeft(24) & "lattice".align(10) & "unstaged".align(10) &
    "residual".align(10) & "direct".align(10) & " lat/dir".align(10)
  for c in validCases:
    let (tL, nL) = timeAdaptive(proc() = discard vLattice(c.rtm, c.rty, c.rctx))
    let (tU, nU) = timeAdaptive(proc() = discard vUnstaged(c.rtm, c.rty, c.rctx))
    let (tR, nR) = timeAdaptive(proc() = discard vResidual(c.rtm, c.rty, c.rctx))
    let (tD, nD) = timeAdaptive(proc() = discard vDirect(c.pre, c.dty, globals))
    let latDir = if nL == "" and nD == "" and tD > 0: fmt"{tL/tD:>9.1f}x" else: " ".align(10)
    echo c.name.alignLeft(24) & fmtCell(tL, nL) & fmtCell(tU, nU) &
      fmtCell(tR, nR) & fmtCell(tD, nD) & latDir
