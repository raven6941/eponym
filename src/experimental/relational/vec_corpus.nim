## Shared Vec-fragment corpus for #170 — the RTerm side of the 16 cases in
## src/staging/bench_elab_end_to_end.nim (which also carries the PreTerm /
## direct-elaborator sides). The lattice prototype is checked against these
## for verdict agreement.

import minikanren
import rel_elab_dep

type
  VCase* = object
    name*: string
    tm*, ty*, ctx*: RTerm
    expect*: bool

proc mkConsChainR(n: int): RTerm =
  result = nilTm()
  for _ in 1 .. n: result = consTm(zeroTm(), result)

proc vecCorpus*(): seq[VCase] =
  let vec2 = vecTy(natTy(), rint(2))
  let vec0 = vecTy(natTy(), rint(0))
  let vec4 = vecTy(natTy(), rint(4))
  let vec8 = vecTy(natTy(), rint(8))
  let nilCtx = rnil()
  result = @[
    VCase(name: "cons(0,cons(0,nil)) : Vec Nat 2",
      tm: consTm(zeroTm(), consTm(zeroTm(), nilTm())),
      ty: vec2, ctx: nilCtx, expect: true),
    VCase(name: "cons(1,cons(2,nil)) : Vec Nat 2",
      tm: consTm(sucTm(zeroTm()), consTm(sucTm(sucTm(zeroTm())), nilTm())),
      ty: vec2, ctx: nilCtx, expect: true),
    VCase(name: "nil : Vec Nat 0",
      tm: nilTm(), ty: vec0, ctx: nilCtx, expect: true),
    VCase(name: "lam x. x : Pi Nat Nat",
      tm: lamTm(varTm(0)), ty: piTy(natTy(), natTy()), ctx: nilCtx,
      expect: true),
    VCase(name: "lam x. lam y. x : Pi Nat (Pi Nat Nat)",
      tm: lamTm(lamTm(varTm(1))),
      ty: piTy(natTy(), piTy(natTy(), natTy())), ctx: nilCtx, expect: true),
    VCase(name: "(lam x. x) 0 : Nat",
      tm: appTm(lamTm(varTm(0)), zeroTm()), ty: natTy(), ctx: nilCtx,
      expect: true),
    VCase(name: "suc (suc zero) : Nat",
      tm: sucTm(sucTm(zeroTm())), ty: natTy(), ctx: nilCtx, expect: true),
    VCase(name: "Pi Nat Nat : Type 0",
      tm: piTy(natTy(), natTy()), ty: univTy(), ctx: nilCtx, expect: true),
    VCase(name: "8 : Nat (primitive lit)",
      tm: rint(8), ty: natTy(), ctx: nilCtx, expect: true),
    VCase(name: "20 : Nat (primitive lit)",
      tm: rint(20), ty: natTy(), ctx: nilCtx, expect: true),
    VCase(name: "cons^4 : Vec Nat 4",
      tm: mkConsChainR(4), ty: vec4, ctx: nilCtx, expect: true),
    VCase(name: "cons^8 : Vec Nat 8",
      tm: mkConsChainR(8), ty: vec8, ctx: nilCtx, expect: true),
    VCase(name: "var 0 : Nat in [Nat]",
      tm: varTm(0), ty: natTy(), ctx: rpair(natTy(), rnil()), expect: true),
    VCase(name: "NEG nil : Vec Nat 2",
      tm: nilTm(), ty: vec2, ctx: nilCtx, expect: false),
    VCase(name: "NEG cons(0,nil) : Vec Nat 2",
      tm: consTm(zeroTm(), nilTm()), ty: vec2, ctx: nilCtx, expect: false),
    VCase(name: "NEG 1 : Vec Nat 2",
      tm: sucTm(zeroTm()), ty: vec2, ctx: nilCtx, expect: false),
  ]
