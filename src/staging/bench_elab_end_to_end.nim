## End-to-end benchmark for #57 closure: the generalized direct-style
## residual (elaboD in staging/gen_elabo_full.nim, staged from elabo/4 +
## inferoOut/4) vs the direct elaborator (checkTermElab, src/elab.nim) on
## the same programs.
##
## Corpus = the test_rel_elab_out differential corpus (8 cases, already
## proven to agree on verdict AND elaborated term) extended with larger
## Vec literals, larger nat literals, and a var case -- "realistic
## programs" on this fragment.
##
## Fairness design (same discipline as bench_vs_elab.nim):
## - Same programs on both sides, each in its native representation
##   (RTerm S-exprs for the residual, PreTerm for the elaborator), built
##   once from a shared spec -- no parsing or translation in the timed loop.
## - The prelude (Nat/Vec data decls) is elaborated once; per-iteration the
##   direct side gets a fresh MetaStore + Supply (each check independent,
##   as on the staged side).
## - Best-of-N wall-clock in microseconds; negatives timed too (rejection
##   cost is part of the story -- cf. #26's writeup).
##
## Usage: nim c -r --path:src src/staging/bench_elab_end_to_end.nim

import options
import minikanren
import rel_elab_dep
import rel_elab_out
import staging/gen_elabo_full
import elab
import preterm
import ett_init
import unify
import tables
import times
import strformat
import strutils
import math

const Reps = 100

# --- Setup (mirrors tests/test_rel_elab_out.nim) -----------------------------

let setupSrc = """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
"""
var (globals, _, _) = elabPrelude(setupSrc)

var nameOf = initTable[int, string]()
for name, ge in globals:
  if ge.tm.kind == tR: nameOf[ge.tm.refId] = name

proc termToCore(t: Term): RTerm =
  ## Direct elaborated Term -> core RTerm (mirrors test_rel_elab_out).
  case t.kind
  of tR:
    let n = nameOf.getOrDefault(t.refId, "R" & $t.refId)
    ratom(case n
      of "Nat": "nat"
      of "Vec": "vec"
      else: n)
  of tV: varTm(t.idx)
  of tLam: lamCore(termToCore(t.dom), termToCore(t.scope.bdy))
  of tApp: appTm(termToCore(t.fn), termToCore(t.arg))
  of tPi: piTy(termToCore(t.dom), termToCore(t.scope.bdy))
  of tC:
    doAssert t.c == cStar, "only cStar expected on this fragment"
    univTy()
  else:
    raise newException(ValueError,
      "termToCore: unexpected kind " & $t.kind & " on fragment")

# --- Corpus builders ----------------------------------------------------------

let natV = mkVar("Nat")
let natTyT = globals["Nat"].tm
let nilCtxR = rnil()

proc mkIntR(n: int): RTerm =
  result = zeroTm()
  for _ in 1 .. n: result = sucTm(result)

proc mkCons(a, n, x, xs: PreTerm): PreTerm =
  mkApp(mkApp(mkApp(mkApp(mkVar("cons"), a), n), x), xs)

proc mkConsChainR(n: int): RTerm =
  result = nilTm()
  for _ in 1 .. n: result = consTm(zeroTm(), result)

proc mkConsChainP(n: int): PreTerm =
  result = mkApp(mkVar("nil"), natV)
  for k in 0 ..< n:
    result = mkCons(natV, mkInt(k), mkInt(0), result)

proc mkVecTyR(n: int): RTerm = vecTy(natTy(), mkIntR(n))

proc mkVecTyT(n: int): Term =
  ## Elaborate `Vec Nat n` itself to get the direct expected type.
  var ms = initMetaStore(); var supply = Supply()
  checkTermElab(mkApp(mkApp(mkVar("Vec"), natV), mkInt(n)),
                @[], globals, ms, supply, tmC(cStar))

proc mkPiT(d, c: Term): Term =
  var ms = initMetaStore(); var supply = Supply()
  checkTermElab(mkPi("x", natV, natV), @[], globals, ms, supply, tmC(cStar))

let piNNT = mkPiT(natTyT, natTyT)
var piNNNT: Term
block:
  var ms = initMetaStore(); var supply = Supply()
  piNNNT = checkTermElab(mkPi("x", natV, mkPi("y", natV, natV)),
                         @[], globals, ms, supply, tmC(cStar))

type Case = object
  name: string
  rtm, rty, rctx: RTerm   # staged side
  pre: PreTerm             # direct side
  dty: Term
  ectx: Ctx
  expect: bool

let vec2R = mkVecTyR(2)
let vec0R = mkVecTyR(0)
let vec4R = mkVecTyR(4)
let vec8R = mkVecTyR(8)
let vec2T = mkVecTyT(2)
let vec0T = mkVecTyT(0)
let vec4T = mkVecTyT(4)
let vec8T = mkVecTyT(8)

let cases = @[
  Case(name: "cons(0,cons(0,nil)) : Vec Nat 2",
    rtm: consTm(zeroTm(), consTm(zeroTm(), nilTm())), rty: vec2R, rctx: nilCtxR,
    pre: mkCons(natV, mkInt(1), mkInt(0),
           mkCons(natV, mkInt(0), mkInt(0), mkApp(mkVar("nil"), natV))),
    dty: vec2T, ectx: @[], expect: true),
  Case(name: "cons(1,cons(2,nil)) : Vec Nat 2",
    rtm: consTm(sucTm(zeroTm()), consTm(sucTm(sucTm(zeroTm())), nilTm())),
    rty: vec2R, rctx: nilCtxR,
    pre: mkCons(natV, mkInt(1), mkInt(1),
           mkCons(natV, mkInt(0), mkInt(2), mkApp(mkVar("nil"), natV))),
    dty: vec2T, ectx: @[], expect: true),
  Case(name: "nil : Vec Nat 0",
    rtm: nilTm(), rty: vec0R, rctx: nilCtxR,
    pre: mkApp(mkVar("nil"), natV), dty: vec0T, ectx: @[], expect: true),
  Case(name: "lam x. x : Pi Nat Nat",
    rtm: lamTm(varTm(0)), rty: piTy(natTy(), natTy()), rctx: nilCtxR,
    pre: mkLam("x", natV, mkVar("x")), dty: piNNT, ectx: @[], expect: true),
  Case(name: "lam x. lam y. x : Pi Nat (Pi Nat Nat)",
    rtm: lamTm(lamTm(varTm(1))), rty: piTy(natTy(), piTy(natTy(), natTy())),
    rctx: nilCtxR,
    pre: mkLam("x", natV, mkLam("y", natV, mkVar("x"))),
    dty: piNNNT, ectx: @[], expect: true),
  Case(name: "(lam x. x) 0 : Nat",
    rtm: appTm(lamTm(varTm(0)), zeroTm()), rty: natTy(), rctx: nilCtxR,
    pre: mkApp(mkLam("x", natV, mkVar("x")), mkInt(0)),
    dty: natTyT, ectx: @[], expect: true),
  Case(name: "suc (suc zero) : Nat",
    rtm: sucTm(sucTm(zeroTm())), rty: natTy(), rctx: nilCtxR,
    pre: mkInt(2), dty: natTyT, ectx: @[], expect: true),
  Case(name: "Pi Nat Nat : ?",
    rtm: piTy(natTy(), natTy()), rty: univTy(), rctx: nilCtxR,
    pre: mkPi("x", natV, natV), dty: tmC(cStar), ectx: @[], expect: true),
  Case(name: "suc^8 : Nat",
    rtm: mkIntR(8), rty: natTy(), rctx: nilCtxR,
    pre: mkInt(8), dty: natTyT, ectx: @[], expect: true),
  Case(name: "suc^20 : Nat",
    rtm: mkIntR(20), rty: natTy(), rctx: nilCtxR,
    pre: mkInt(20), dty: natTyT, ectx: @[], expect: true),
  Case(name: "cons^4 : Vec Nat 4",
    rtm: mkConsChainR(4), rty: vec4R, rctx: nilCtxR,
    pre: mkConsChainP(4), dty: vec4T, ectx: @[], expect: true),
  Case(name: "cons^8 : Vec Nat 8",
    rtm: mkConsChainR(8), rty: vec8R, rctx: nilCtxR,
    pre: mkConsChainP(8), dty: vec8T, ectx: @[], expect: true),
  Case(name: "var 0 : Nat in [Nat]",
    rtm: varTm(0), rty: natTy(), rctx: rpair(natTy(), rnil()),
    pre: mkVar("a"), dty: natTyT,
    ectx: @[CtxEntry(name: "a", ty: natTyT)], expect: true),
  Case(name: "NEG nil : Vec Nat 2",
    rtm: nilTm(), rty: vec2R, rctx: nilCtxR,
    pre: mkApp(mkVar("nil"), natV), dty: vec2T, ectx: @[], expect: false),
  Case(name: "NEG cons(0,nil) : Vec Nat 2",
    rtm: consTm(zeroTm(), nilTm()), rty: vec2R, rctx: nilCtxR,
    pre: mkCons(natV, mkInt(0), mkInt(0), mkApp(mkVar("nil"), natV)),
    dty: vec2T, ectx: @[], expect: false),
  Case(name: "NEG 1 : Vec Nat 2",
    rtm: sucTm(zeroTm()), rty: vec2R, rctx: nilCtxR,
    pre: mkInt(1), dty: vec2T, ectx: @[], expect: false),
]

# --- Correctness: staged residual must agree with direct on verdict + output --

echo "== correctness =="
for c in cases:
  let staged = elaboD(c.rtm, c.rty, c.rctx)
  var directOut: Term
  var directOk = true
  block:
    var ms = initMetaStore(); var supply = Supply()
    try:
      directOut = checkTermElab(c.pre, c.ectx, globals, ms, supply, c.dty)
    except ElabError:
      directOk = false
  if c.expect:
    doAssert staged.isSome, c.name & ": staged residual rejected a valid term"
    doAssert directOk, c.name & ": direct elaborator rejected a valid term"
    let core = termToCore(directOut)
    doAssert $staged.get == $core,
      c.name & ":\n  staged: " & $staged.get & "\n  direct: " & $core
    echo "ok: ", c.name
  else:
    doAssert staged.isNone, c.name & ": staged accepted an invalid term"
    doAssert not directOk, c.name & ": direct accepted an invalid term"
    echo "ok: ", c.name, " (both reject)"

# --- Timing -------------------------------------------------------------------

proc timeIt(reps: int, body: proc()): float =
  result = high(float)
  for _ in 1 .. reps:
    let t0 = cpuTime()
    body()
    result = min(result, (cpuTime() - t0) * 1e6)  # microseconds

echo ""
echo "== wall-clock, best of ", Reps, " (microseconds) =="
echo "case".alignLeft(36) & "staged".align(10) & "direct".align(10) & "direct/staged".align(14)
var logSum = 0.0
var n = 0
for c in cases:
  let tStaged = timeIt(Reps, proc() = discard elaboD(c.rtm, c.rty, c.rctx))
  let tDirect = timeIt(Reps, proc() =
    var ms = initMetaStore(); var supply = Supply()
    try: discard checkTermElab(c.pre, c.ectx, globals, ms, supply, c.dty)
    except ElabError: discard)
  let ratio = tDirect / tStaged
  echo fmt"{c.name:<36}{tStaged:>10.2f}{tDirect:>10.2f}{ratio:>13.1f}x"
  logSum += ln(ratio)
  inc n
echo fmt"geometric mean direct/staged: {exp(logSum / float(n)):.2f}x"
