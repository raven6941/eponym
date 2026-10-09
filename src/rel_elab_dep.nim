## Relational dependent elaborator — Track C step 3
##
## Fragment (v2, no general substitution):
## - Non-dependent functions: Pi(x:A).B where B doesn't use x (STLC-style),
##   plus dependent Vec as the interesting dependent case.
## - Types: `?` (univ), `Nat`, `Vec A n`, `Pi A B` (non-dep)
## - Terms: vars, `lam`, app, `zero`/`suc`, `nil`/`cons`
##
## Rationale: General dependent Pi needs substitution B[x:=a], which requires
## the miniKanren state to handle bound logic vars. For the MVP comparison,
## we use non-dependent Pi (like typeo) + dependent Vec via specialized rules.
## The Vec case demonstrates dependency (index refinement) without general
## substitution.
##
## Encoding as RTerm S-exprs.

import minikanren
import strutils

proc fail*(): Goal =
  return proc(s: State): Stream = emptyStream()

# --- Constructors --------------------------------------------------------

proc varTm*(i: int): RTerm = rpair(ratom("var"), rpair(ratom($i), rnil()))
proc lamTm*(b: RTerm): RTerm = rpair(ratom("lam"), rpair(b, rnil()))
proc appTm*(f, a: RTerm): RTerm = rpair(ratom("app"), rpair(f, rpair(a, rnil())))
proc piTy*(d, c: RTerm): RTerm = rpair(ratom("pi"), rpair(d, rpair(c, rnil())))
proc zeroTm*(): RTerm = ratom("zero")
proc sucTm*(n: RTerm): RTerm = rpair(ratom("suc"), rpair(n, rnil()))
proc nilTm*(): RTerm = ratom("nil")
proc consTm*(h, t: RTerm): RTerm = rpair(ratom("cons"), rpair(h, rpair(t, rnil())))
proc natTy*(): RTerm = ratom("nat")
proc vecTy*(a, n: RTerm): RTerm = rpair(ratom("vec"), rpair(a, rpair(n, rnil())))
proc univTy*(): RTerm = ratom("univ")

proc tagOf(t: RTerm): string =
  if t.kind == rkPair and t.head.kind == rkAtom: t.head.name else: ""

proc varIdx(t: RTerm): int = parseInt(t.tail.head.name)

# --- Inference -----------------------------------------------------------

proc lookupO(ctx: RTerm, i: int, ty: RTerm): Goal =
  if i == 0:
    fresh(proc(tl: RTerm): Goal = `==`(ctx, rpair(ty, tl)))
  else:
    fresh2(proc(h, tl: RTerm): Goal =
      conj(`==`(ctx, rpair(h, tl)), lookupO(tl, i - 1, ty)))

proc checko*(tm, ty, ctx: RTerm): Goal  # forward

proc infero*(tm, ty, ctx: RTerm): Goal =
  if tm.kind == rkVar: return fail()
  # atoms
  if tm.kind == rkAtom:
    if tm.name == "zero": return `==`(ty, natTy())
    return fail()  # nil needs expected type
  let tag = tagOf(tm)
  if tag == "var": return lookupO(ctx, varIdx(tm), ty)
  if tag == "suc":
    return conj(infero(tm.tail.head, natTy(), ctx), `==`(ty, natTy()))
  if tag == "app":
    # f : Pi(d,c), a : d  =>  f a : c   (non-dependent: no substitution)
    let f = tm.tail.head; let a = tm.tail.tail.head
    if tagOf(f) == "lam":
      # f is lam: check against fresh Pi(d,c)
      return fresh2(proc(d, c: RTerm): Goal =
        conj(checko(f, piTy(d, c), ctx),
          conj(checko(a, d, ctx), `==`(ty, c))))
    else:
      return fresh2(proc(d, c: RTerm): Goal =
        conj(infero(f, piTy(d, c), ctx),
          conj(checko(a, d, ctx), `==`(ty, c))))
  if tag == "pi":
    # Pi(d,c) : univ if d:univ, c:univ
    let d = tm.tail.head; let c = tm.tail.tail.head
    return conj(checko(d, univTy(), ctx),
      conj(checko(c, univTy(), rpair(d, ctx)), `==`(ty, univTy())))
  if tag == "vec":
    # Vec(A,n) : univ if A:univ, n:Nat
    let a = tm.tail.head; let n = tm.tail.tail.head
    return conj(checko(a, univTy(), ctx),
      conj(checko(n, natTy(), ctx), `==`(ty, univTy())))
  # lam, cons: need expected type
  return fail()

proc checko*(tm, ty, ctx: RTerm): Goal =
  if tm.kind == rkVar: return fail()
  if tm.kind == rkAtom:
    if tm.name == "zero": return `==`(ty, natTy())
    if tm.name == "nil":
      # nil : Vec(A, zero). ty must be vec(A, zero).
      if tagOf(ty) == "vec":
        return `==`(ty.tail.tail.head, zeroTm())
      return fail()
    # Type formation (issue #59): nat, univ : univ. (The fragment keeps
    # `? : ?`; universe hierarchy is issue #52.)
    if tm.name == "nat": return `==`(ty, univTy())
    if tm.name == "univ": return `==`(ty, univTy())
    return fail()
  let tag = tagOf(tm)
  if tag == "lam":
    # lam(b) : Pi(d,c) if b : c in (d.ctx)
    if tagOf(ty) == "pi":
      return checko(tm.tail.head, ty.tail.tail.head,
                    rpair(ty.tail.head, ctx))
    return fail()
  if tag == "cons":
    # cons(h,t) : Vec(A, suc(n)) if h:A, t:Vec(A,n)
    if tagOf(ty) == "vec":
      let a = ty.tail.head
      let nv = ty.tail.tail.head
      if tagOf(nv) == "suc":
        let n = nv.tail.head
        let h = tm.tail.head; let t = tm.tail.tail.head
        return conj(checko(h, a, ctx),
                 checko(t, vecTy(a, n), ctx))
      return fail()
    return fail()
  # fallback: infer and unify
  fresh(proc(ty2: RTerm): Goal =
    conj(infero(tm, ty2, ctx), `==`(ty, ty2)))
