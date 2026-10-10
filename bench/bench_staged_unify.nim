## Issue #63: staged unifier micro-benchmark (L1 of the tower).
##
## Synthetic term pairs for the corpus's top zonked shapes. Baseline
## `unify` (general) vs `unifyStagedImpl` (kind-pair-specialized) in one
## binary — no flags needed. Reports ns/op, speedup, and an agreement
## check (same outcome + same error message).
##
## Compile:  nim c -r -d:release --path:src --path:src/eponym \
##               --path:src/relational --path:src/staging bench/bench_staged_unify.nim

import strutils
import times
import unify
import ett_init
import preterm  # noLoc

let loc = noLoc

proc nsPerOp(iters: int, body: proc() {.closure.}): float =
  let t0 = cpuTime()
  for i in 0 ..< iters: body()
  (cpuTime() - t0) * 1e9 / iters.float

proc tryUnify(ms: var MetaStore, a, b: Term, staged: bool): tuple[ok: bool, msg: string] =
  try:
    if staged: unifyStagedImpl(ms, a, b, loc)
    else: unify(ms, a, b, loc)
    (true, "")
  except UnifyError as e:
    (false, e.msg)

proc benchPair(name: string, iters: int, a, b: Term, freshStores: int = 0) =
  ## Rigid cases reuse one store; flex cases pre-create `freshStores`
  ## stores (solveMeta writes, so each iteration needs a fresh one).
  var tBase, tStaged: float
  var rBase: tuple[ok: bool, msg: string]
  var agree: bool
  if freshStores > 0:
    # flex-rigid: solveMeta writes, so each iteration needs a fresh store
    # and a fresh meta. Agreement is checked on the first pair of stores.
    var storesB = newSeq[MetaStore](freshStores)
    var storesS = newSeq[MetaStore](freshStores)
    for i in 0 ..< freshStores:
      storesB[i] = initMetaStore()
      storesS[i] = initMetaStore()
    let m0 = freshMeta(storesB[0], tmC(cStar), 1, 0, loc)
    rBase = tryUnify(storesB[0], m0, tmC(cOne), false)
    let t0 = cpuTime()
    for i in 1 ..< freshStores:
      let m = freshMeta(storesB[i], tmC(cStar), 1, 0, loc)
      discard tryUnify(storesB[i], m, tmC(cOne), false)
    tBase = (cpuTime() - t0) * 1e9 / (freshStores - 1).float
    let m1 = freshMeta(storesS[0], tmC(cStar), 1, 0, loc)
    let rStaged = tryUnify(storesS[0], m1, tmC(cOne), true)
    agree = rBase == rStaged
    let t1 = cpuTime()
    for i in 1 ..< freshStores:
      let m = freshMeta(storesS[i], tmC(cStar), 1, 0, loc)
      discard tryUnify(storesS[i], m, tmC(cOne), true)
    tStaged = (cpuTime() - t1) * 1e9 / (freshStores - 1).float
  else:
    var ms = initMetaStore()
    rBase = tryUnify(ms, a, b, false)
    var ms2 = initMetaStore()
    let rStaged = tryUnify(ms2, a, b, true)
    agree = rBase == rStaged
    tBase = nsPerOp(iters, proc() {.closure.} = discard tryUnify(ms, a, b, false))
    tStaged = nsPerOp(iters, proc() {.closure.} = discard tryUnify(ms2, a, b, true))
  let speed = if tStaged > 0: tBase / tStaged else: 0.0
  echo name, "  agree=", agree, " (", rBase, ")",
       "  base=", tBase.formatFloat(ffDecimal, 1), "ns",
       "  staged=", tStaged.formatFloat(ffDecimal, 1), "ns",
       "  speedup=", speed.formatFloat(ffDecimal, 2), "x"

proc rTerm(refId: int): Term =
  Term(kind: tR, refId: refId, refTyp: nil, refIsDefn: false, refVal: nil)

echo "=== micro-benchmarks (synthetic pairs, top corpus shapes) ==="
let r99 = rTerm(99)
benchPair("C=C ok        ", 200_000, tmC(cStar), tmC(cStar))
benchPair("C=C fail      ", 200_000, tmC(cStar), tmC(cOne))
benchPair("R=R ok        ", 200_000, r99, r99)
benchPair("R=R fail      ", 200_000, r99, rTerm(100))
benchPair("V=V ok        ", 200_000, vv(0), vv(0))
benchPair("A(A(R,V),V) ok", 100_000, tmApp(tmApp(r99, vv(0)), vv(1)),
                                 tmApp(tmApp(r99, vv(0)), vv(1)))
benchPair("Pi(V,V) ok    ", 100_000, tmPi(tmC(cStar), "A", vv(0)),
                                 tmPi(tmC(cStar), "A", vv(0)))
benchPair("Lam ok        ", 100_000, tmLam(tmC(cStar), "x", vv(0)),
                                 tmLam(tmC(cStar), "x", vv(0)))
benchPair("Pair ok       ", 100_000, tmPair(tmC(cStar), vv(0), "p", vv(1)),
                                 tmPair(tmC(cStar), vv(0), "p", vv(1)))
benchPair("flex-rigid    ", 0, nil, nil, freshStores = 20_000)
benchPair("C vs V fail   ", 200_000, tmC(cStar), vv(0))
benchPair("eta lam vs R  ", 50_000, tmLam(tmC(cStar), "x", tmApp(r99, vv(0))), r99)
