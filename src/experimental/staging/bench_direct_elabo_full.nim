## Benchmark for #57 (generalized fragment): direct-style residual
## (gen_elabo_full.nim) vs unstaged relational elabo/inferoOut.
##
## Corpus spans the full fragment: atoms, var, suc, app (redex + var
## head), pi, vec, lam, nil, cons. Reports per-case wall-clock and the
## direct/relational speedup.

import options
import times
import math
import minikanren
import rel_elab_dep
import rel_elab_out
import staging/gen_elabo_full

proc timeIt(reps: int, body: proc()): float =
  result = high(float)
  for _ in 1 .. reps:
    let t0 = cpuTime()
    body()
    result = min(result, (cpuTime() - t0) * 1e6)  # microseconds

type Case = object
  name: string
  checkMode: bool
  tm, ty, ctx: RTerm

let nilCtx = rnil()
let natCtx = rpair(natTy(), rnil())
let piCtx = rpair(piTy(natTy(), natTy()), rnil())
let vec2ty = vecTy(natTy(), sucTm(sucTm(zeroTm())))
let vec4ty = vecTy(natTy(), sucTm(sucTm(sucTm(sucTm(zeroTm())))))
let piNN = piTy(natTy(), natTy())

proc mkVecLit(n: int): RTerm =
  result = nilTm()
  for _ in 1 .. n:
    result = consTm(zeroTm(), result)

let cases = @[
  Case(name: "zero : Nat", checkMode: true,
    tm: zeroTm(), ty: natTy(), ctx: nilCtx),
  Case(name: "suc^8 : Nat", checkMode: true,
    tm: block:
      var t = zeroTm()
      for _ in 1 .. 8: t = sucTm(t)
      t,
    ty: natTy(), ctx: nilCtx),
  Case(name: "lam x. x : Pi Nat Nat", checkMode: true,
    tm: lamTm(varTm(0)), ty: piNN, ctx: nilCtx),
  Case(name: "lam x. lam y. x : Pi Nat (Pi Nat Nat)", checkMode: true,
    tm: lamTm(lamTm(varTm(1))), ty: piTy(natTy(), piNN), ctx: nilCtx),
  Case(name: "cons^4 : Vec Nat 4", checkMode: true,
    tm: mkVecLit(4), ty: vec4ty, ctx: nilCtx),
  Case(name: "app(lam x. x, 0) : Nat", checkMode: true,
    tm: appTm(lamTm(varTm(0)), zeroTm()), ty: natTy(), ctx: nilCtx),
  Case(name: "infer app(var 0, zero) in [Pi Nat Nat]", checkMode: false,
    tm: appTm(varTm(0), zeroTm()), ctx: piCtx),
  Case(name: "infer Pi Nat Nat", checkMode: false,
    tm: piNN, ctx: nilCtx),
  Case(name: "infer Vec Nat 2", checkMode: false,
    tm: vec2ty, ctx: nilCtx),
]

echo "case | direct us | relational us | speedup"
var speedups: seq[float] = @[]
for c in cases:
  var dOk = false
  let tD = timeIt(200, proc() =
    if c.checkMode: dOk = elaboD(c.tm, c.ty, c.ctx).isSome
    else: dOk = inferD(c.tm, c.ctx).isSome)
  var rOk = false
  let tR = timeIt(200, proc() =
    if c.checkMode:
      rOk = run(freshVar(), elabo(c.tm, c.ty, c.ctx, freshVar()), 1).len > 0
    else:
      let qp = freshVar()
      rOk = run(qp, fresh2(proc(ty2, et2: RTerm): Goal =
        conj(inferoOut(c.tm, ty2, c.ctx, et2),
          `==`(qp, rpair(ty2, rpair(et2, rnil()))))), 1).len > 0)
  doAssert dOk and rOk, c.name & ": verdict mismatch"
  let sp = tR / max(tD, 1e-9)
  speedups.add(sp)
  echo c.name, " | ", tD, " | ", tR, " | ", sp, "x"

var geo = 1.0
for s in speedups: geo *= s
geo = pow(geo, 1.0 / speedups.len.float)
echo "geometric mean speedup: ", geo, "x"
