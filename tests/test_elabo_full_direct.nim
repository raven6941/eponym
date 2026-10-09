## Differential test for #57 (generalized fragment): gen_elabo_full.nim
## (direct-style residual) vs the elabo/4 + inferoOut/4 relations.
##
## For each corpus case: run the relation, require a ground first answer,
## and require the direct residual to agree on verdict AND elaborated term
## (string equality on RTerm). Negative cases must fail on both sides.

import options
import minikanren
import rel_elab_dep
import rel_elab_out
import staging/gen_elabo_full

proc isGround(t: RTerm): bool =
  case t.kind
  of rkVar: false
  of rkAtom: true
  of rkPair: isGround(t.head) and isGround(t.tail)

type
  Mode = enum mCheck, mInfer
  Case = object
    name: string
    mode: Mode
    tm: RTerm
    ty: RTerm   # expected type for mCheck; ignored for mInfer
    ctx: RTerm

let nilCtx = rnil()
let natCtx = rpair(natTy(), rnil())
let piCtx = rpair(piTy(natTy(), natTy()), rnil())
let vec2ty = vecTy(natTy(), sucTm(sucTm(zeroTm())))
let vec1ty = vecTy(natTy(), sucTm(zeroTm()))
let vec0ty = vecTy(natTy(), zeroTm())

let checkCases = @[
  Case(name: "zero : Nat", mode: mCheck, tm: zeroTm(), ty: natTy(), ctx: nilCtx),
  Case(name: "suc (suc zero) : Nat", mode: mCheck,
    tm: sucTm(sucTm(zeroTm())), ty: natTy(), ctx: nilCtx),
  Case(name: "lam x. x : Pi Nat Nat", mode: mCheck,
    tm: lamTm(varTm(0)), ty: piTy(natTy(), natTy()), ctx: nilCtx),
  Case(name: "lam x. lam y. x : Pi Nat (Pi Nat Nat)", mode: mCheck,
    tm: lamTm(lamTm(varTm(1))), ty: piTy(natTy(), piTy(natTy(), natTy())), ctx: nilCtx),
  Case(name: "nil : Vec Nat 0", mode: mCheck,
    tm: nilTm(), ty: vec0ty, ctx: nilCtx),
  Case(name: "cons(0,cons(0,nil)) : Vec Nat 2", mode: mCheck,
    tm: consTm(zeroTm(), consTm(zeroTm(), nilTm())), ty: vec2ty, ctx: nilCtx),
  Case(name: "cons(1,nil) : Vec Nat 1", mode: mCheck,
    tm: consTm(sucTm(zeroTm()), nilTm()), ty: vec1ty, ctx: nilCtx),
  Case(name: "app(lam x. x, 0) : Nat (redex, check)", mode: mCheck,
    tm: appTm(lamTm(varTm(0)), zeroTm()), ty: natTy(), ctx: nilCtx),
  Case(name: "var 0 : Nat in [Nat]", mode: mCheck,
    tm: varTm(0), ty: natTy(), ctx: natCtx),
  Case(name: "nat : univ (formation, check)", mode: mCheck,
    tm: ratom("nat"), ty: univTy(), ctx: nilCtx),
  Case(name: "Pi Nat Nat : univ (check)", mode: mCheck,
    tm: piTy(natTy(), natTy()), ty: univTy(), ctx: nilCtx),
  Case(name: "Vec Nat 2 : univ (check)", mode: mCheck,
    tm: vec2ty, ty: univTy(), ctx: nilCtx),
]

let inferCases = @[
  Case(name: "infer zero", mode: mInfer, tm: zeroTm(), ctx: nilCtx),
  Case(name: "infer nat", mode: mInfer, tm: ratom("nat"), ctx: nilCtx),
  Case(name: "infer univ", mode: mInfer, tm: ratom("univ"), ctx: nilCtx),
  Case(name: "infer suc (suc zero)", mode: mInfer,
    tm: sucTm(sucTm(zeroTm())), ctx: nilCtx),
  Case(name: "infer var 0 in [Nat]", mode: mInfer, tm: varTm(0), ctx: natCtx),
  Case(name: "infer Pi Nat Nat", mode: mInfer,
    tm: piTy(natTy(), natTy()), ctx: nilCtx),
  Case(name: "infer Vec Nat 2", mode: mInfer, tm: vec2ty, ctx: nilCtx),
  Case(name: "infer (lam x. x) 0 (redex)", mode: mInfer,
    tm: appTm(lamTm(varTm(0)), zeroTm()), ctx: nilCtx),
  Case(name: "infer app(var 0, zero) in [Pi Nat Nat]", mode: mInfer,
    tm: appTm(varTm(0), zeroTm()), ctx: piCtx),
  Case(name: "infer app(suc, zero) -- ill-typed head", mode: mInfer,
    tm: appTm(ratom("suc"), zeroTm()), ctx: nilCtx),
]

let negCheck = @[
  Case(name: "nil : Vec Nat 2", mode: mCheck, tm: nilTm(), ty: vec2ty, ctx: nilCtx),
  Case(name: "cons(0,nil) : Vec Nat 2", mode: mCheck,
    tm: consTm(zeroTm(), nilTm()), ty: vec2ty, ctx: nilCtx),
  Case(name: "lam x. x : Nat", mode: mCheck,
    tm: lamTm(varTm(0)), ty: natTy(), ctx: nilCtx),
  Case(name: "zero : Vec Nat 0", mode: mCheck, tm: zeroTm(), ty: vec0ty, ctx: nilCtx),
  Case(name: "cons(0,nil) : Nat", mode: mCheck,
    tm: consTm(zeroTm(), nilTm()), ty: natTy(), ctx: nilCtx),
  Case(name: "suc nat : Nat", mode: mCheck,
    tm: sucTm(ratom("nat")), ty: natTy(), ctx: nilCtx),
]

let negInfer = @[
  Case(name: "infer nil (needs type)", mode: mInfer, tm: nilTm(), ctx: nilCtx),
  Case(name: "infer lam x. x (needs type)", mode: mInfer,
    tm: lamTm(varTm(0)), ctx: nilCtx),
  Case(name: "infer var 5 in [Nat] (out of range)", mode: mInfer,
    tm: varTm(5), ctx: natCtx),
  Case(name: "infer app(zero, zero)", mode: mInfer,
    tm: appTm(zeroTm(), zeroTm()), ctx: nilCtx),
]

var npass = 0

for c in checkCases:
  let q = freshVar()
  let sols = run(q, elabo(c.tm, c.ty, c.ctx, q), 1)
  doAssert sols.len == 1, c.name & ": elabo failed"
  doAssert isGround(sols[0]), c.name & ": non-ground etm: " & $sols[0]
  let d = elaboD(c.tm, c.ty, c.ctx)
  doAssert d.isSome, c.name & ": elaboD failed"
  doAssert $d.get == $sols[0],
    c.name & ":\n  rel:    " & $sols[0] & "\n  direct: " & $d.get
  inc npass
  echo "ok: ", c.name

for c in inferCases:
  # capture (ty, etm) as a pair through one query
  let qp = freshVar()
  let sols2 = run(qp,
    fresh2(proc(ty2, et2: RTerm): Goal =
      conj(inferoOut(c.tm, ty2, c.ctx, et2),
        `==`(qp, rpair(ty2, rpair(et2, rnil()))))), 1)
  let d = inferD(c.tm, c.ctx)
  if c.name == "infer app(suc, zero) -- ill-typed head":
    doAssert sols2.len == 0, c.name & ": relation unexpectedly succeeded"
    doAssert d.isNone, c.name & ": elaboD unexpectedly succeeded"
  else:
    doAssert sols2.len == 1, c.name & ": inferoOut failed"
    let rty = sols2[0].head
    let retm = sols2[0].tail.head
    doAssert isGround(rty) and isGround(retm),
      c.name & ": non-ground: " & $sols2[0]
    doAssert d.isSome, c.name & ": inferD failed"
    doAssert $d.get.ty == $rty and $d.get.etm == $retm,
      c.name & ":\n  rel:    (" & $rty & ", " & $retm & ")" &
      "\n  direct: (" & $d.get.ty & ", " & $d.get.etm & ")"
  inc npass
  echo "ok: ", c.name

for c in negCheck:
  let q = freshVar()
  let sols = run(q, elabo(c.tm, c.ty, c.ctx, q), 1)
  doAssert sols.len == 0, c.name & ": elabo unexpectedly succeeded: " & $sols[0]
  doAssert elaboD(c.tm, c.ty, c.ctx).isNone,
    c.name & ": elaboD unexpectedly succeeded"
  inc npass
  echo "ok (rejected): ", c.name

for c in negInfer:
  let qp = freshVar()
  let sols = run(qp,
    fresh2(proc(ty2, et2: RTerm): Goal =
      conj(inferoOut(c.tm, ty2, c.ctx, et2),
        `==`(qp, rpair(ty2, rpair(et2, rnil()))))), 1)
  doAssert sols.len == 0, c.name & ": inferoOut unexpectedly succeeded"
  doAssert inferD(c.tm, c.ctx).isNone,
    c.name & ": inferD unexpectedly succeeded"
  inc npass
  echo "ok (rejected): ", c.name

echo "--- ", npass, " differential checks passed ---"
