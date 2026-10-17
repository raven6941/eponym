## Differential test for issue #59: elabo/4 output vs checkTermElab output.
##
## For each corpus term: run `elabo(tm, ty, ctx, etm)` relationally and
## `checkTermElab(pre, ...)` directly; normalize the direct elaborated
## Term to the core RTerm representation and require structural equality
## with `etm` (not just verdict agreement). Also requires `etm` to be
## ground, agreement on negative cases, and verdict agreement with the
## existing staged checker (stage_rel_elab_dep pipeline) on the Vec
## fragment.

import minikanren
import rel_elab_dep
import rel_elab_out
import elab
import preterm
import eponym_init
import unify
import tables
import strutils
import staging/relcompile
import stage_rel_elab_dep  # test-side driver (tests/ is the main module's dir)

stagedCheckoVec2Procs()

# --- Setup (mirrors staging/bench_rel_elab.nim) ------------------------------

let setupSrc = """
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
data Vec (A : Type 0) : Nat -> Type 0 where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
"""
var (globals, ms0, supply0) = elabPrelude(setupSrc)
let dummyDefs = elabCheck(setupSrc & """
proc dummy : Vec Nat (suc (suc zero)) =
  cons Nat (suc zero) zero (cons Nat zero zero (nil Nat))
proc d0 : Vec Nat zero =
  nil Nat
""")
let vecNat2 = dummyDefs[0].tyTm
let vecNat0 = dummyDefs[1].tyTm

var nameOf = initTable[int, string]()
for name, ge in globals:
  if ge.tm.kind == tR: nameOf[ge.tm.refId] = name

# --- Normalizer: direct elaborated Term -> core RTerm -------------------------

proc termToCore(t: Term): RTerm =
  case t.kind
  of tR:
    # Globals are capitalized (Nat, Vec); the relational encoding uses
    # lowercase atoms (nat, vec). Constructor names are already lowercase.
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
  of tNatLit: rint(t.natLitVal)  # Issue #93: direct side now emits literals
  else:
    raise newException(ValueError,
      "termToCore: unexpected kind " & $t.kind & " on fragment")

proc isGround(t: RTerm): bool =
  case t.kind
  of rkVar: false
  of rkAtom: true
  of rkPair: isGround(t.head) and isGround(t.tail)

proc expandNatLits(t: RTerm): RTerm =
  ## Issue #93: rewrite primitive nat literals (rint) to unary suc-chains,
  ## so the relational side's chain-form numerals compare against the
  ## direct elaborator's literal form. The two are definitionally equal;
  ## this is the same oracle as staging/bench_elab_end_to_end.nim.
  ## Note: sucCore (the `(app suc …)` core encoding), not sucTm (the
  ## relational spec's `(suc …)` encoding) — both sides are core terms.
  case t.kind
  of rkVar: t
  of rkAtom:
    if isNatLit(t):
      var r = zeroTm()
      for _ in 1 .. parseInt(t.name): r = sucCore(r)
      r
    else: t
  of rkPair:
    # De Bruijn indices ("var", i) are not Nat literals — leave them alone.
    if t.head.kind == rkAtom and t.head.name == "var": t
    else: rpair(expandNatLits(t.head), expandNatLits(t.tail))

# --- Corpus ------------------------------------------------------------------

type Case = object
  name: string
  rtm: RTerm    # relational surface term
  rty: RTerm    # relational expected type
  pre: PreTerm  # direct surface term
  dty: Term     # direct expected type

let natV = mkVar("Nat")
let nilN = mkApp(mkVar("nil"), natV)
proc mkCons(a, n, x, xs: PreTerm): PreTerm =
  mkApp(mkApp(mkApp(mkApp(mkVar("cons"), a), n), x), xs)

let tail00 = mkCons(natV, mkInt(0), mkInt(0), nilN)
let vec00 = mkCons(natV, mkInt(1), mkInt(0), tail00)
let tail12 = mkCons(natV, mkInt(0), mkInt(2), nilN)
let vec12 = mkCons(natV, mkInt(1), mkInt(1), tail12)

var piNN, piNNN: Term
block:
  var ms = initMetaStore(); var supply = Supply()
  piNN = checkTermElab(mkPi("x", natV, natV), @[], globals, ms, supply, tmC(cStar))
  var ms2 = initMetaStore(); var supply2 = Supply()
  piNNN = checkTermElab(mkPi("x", natV, mkPi("y", natV, natV)),
                        @[], globals, ms2, supply2, tmC(cStar))

let natTyT = globals["Nat"].tm
let vec2 = vecTy(natTy(), sucTm(sucTm(zeroTm())))
let vec0 = vecTy(natTy(), zeroTm())

let cases = @[
  Case(name: "cons(0,cons(0,nil)) : Vec Nat 2",
    rtm: consTm(zeroTm(), consTm(zeroTm(), nilTm())), rty: vec2,
    pre: vec00, dty: vecNat2),
  Case(name: "cons(1,cons(2,nil)) : Vec Nat 2",
    rtm: consTm(sucTm(zeroTm()), consTm(sucTm(sucTm(zeroTm())), nilTm())),
    rty: vec2, pre: vec12, dty: vecNat2),
  Case(name: "nil : Vec Nat 0",
    rtm: nilTm(), rty: vec0, pre: nilN, dty: vecNat0),
  Case(name: "lam x. x : Pi Nat Nat",
    rtm: lamTm(varTm(0)), rty: piTy(natTy(), natTy()),
    pre: mkLam("x", natV, mkVar("x")), dty: piNN),
  Case(name: "lam x. lam y. x : Pi Nat (Pi Nat Nat)",
    rtm: lamTm(lamTm(varTm(1))), rty: piTy(natTy(), piTy(natTy(), natTy())),
    pre: mkLam("x", natV, mkLam("y", natV, mkVar("x"))), dty: piNNN),
  Case(name: "(lam x. x) 0 : Nat",
    rtm: appTm(lamTm(varTm(0)), zeroTm()), rty: natTy(),
    pre: mkApp(mkLam("x", natV, mkVar("x")), mkInt(0)), dty: natTyT),
  Case(name: "suc (suc zero) : Nat",
    rtm: sucTm(sucTm(zeroTm())), rty: natTy(),
    pre: mkInt(2), dty: natTyT),
  Case(name: "Pi Nat Nat : Type 0",
    rtm: piTy(natTy(), natTy()), rty: univTy(),
    pre: mkPi("x", natV, natV), dty: tmC(cStar)),
]

# --- Positive differential ---------------------------------------------------

for c in cases:
  let q = freshVar()
  let sols = run(q, elabo(c.rtm, c.rty, rnil(), q), 1)
  doAssert sols.len == 1, c.name & ": elabo failed"
  let etm = sols[0]
  doAssert isGround(etm), c.name & ": etm not ground: " & $etm
  var ms = initMetaStore(); var supply = Supply()
  let directOut =
    try: checkTermElab(c.pre, @[], globals, ms, supply, c.dty)
    except ElabError as e:
      raise newException(AssertionDefect, c.name & ": direct failed: " & e.msg)
  let core = termToCore(directOut)
  doAssert $expandNatLits(etm) == $expandNatLits(core),
    c.name & ":\n  elabo:  " & $etm & "\n  direct: " & $core
  echo "ok: ", c.name, "  ~~>  ", $etm

# --- Negative agreement ------------------------------------------------------

block:
  # nil : Vec Nat 2 must fail on both sides
  let q = freshVar()
  let sols = run(q, elabo(nilTm(), vec2, rnil(), q), 1)
  doAssert sols.len == 0, "elabo accepted nil : Vec Nat 2"
  var ms = initMetaStore(); var supply = Supply()
  var directFailed = false
  try: discard checkTermElab(nilN, @[], globals, ms, supply, vecNat2)
  except ElabError: directFailed = true
  doAssert directFailed, "direct accepted nil : Vec Nat 2"
  echo "ok: nil : Vec Nat 2 rejected by both"

block:
  # cons(0,nil) : Vec Nat 2 must fail on both sides
  let q = freshVar()
  let sols = run(q, elabo(consTm(zeroTm(), nilTm()), vec2, rnil(), q), 1)
  doAssert sols.len == 0, "elabo accepted cons(0,nil) : Vec Nat 2"
  let badPre = mkCons(natV, mkInt(0), mkInt(0), nilN)
  var ms = initMetaStore(); var supply = Supply()
  var directFailed = false
  try: discard checkTermElab(badPre, @[], globals, ms, supply, vecNat2)
  except ElabError: directFailed = true
  doAssert directFailed, "direct accepted cons(0,nil) : Vec Nat 2"
  echo "ok: cons(0,nil) : Vec Nat 2 rejected by both"

# --- Staged pipeline verdict agreement (Vec fragment) ------------------------

for c in cases[0..2]:
  let q = freshVar()
  let relOk = run(q, elabo(c.rtm, c.rty, rnil(), q), 1).len == 1
  let stagedOk =
    if $c.rty == $vec2: run(freshVar(), stagedCheckoVec2(c.rtm, rnil()), 1).len > 0
    else: true  # staged checker is specialized to Vec Nat 2 only
  doAssert relOk and stagedOk, c.name & ": elabo/staged verdict mismatch"
  echo "ok: staged pipeline agrees on ", c.name

echo "--- all rel_elab_out differential tests passed ---"
