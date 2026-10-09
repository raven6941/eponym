## Relational elaborator with output terms — GH issue #59
##
## `elabo(tm, ty, ctx, etm)`: like `checko` from rel_elab_dep, but `etm`
## is an output logic variable that ends up ground and equal to the
## elaborated core term. `inferoOut(tm, ty, ctx, etm)`: like `infero`,
## with output.
##
## Elaborated core representation (RTerm S-exprs). The core uses the
## direct elaborator's application-spine shape: data constructors are
## atoms applied through ("app", f, a), exactly as checkTermElab nests
## tApp nodes around tR globals. Surface constructors keep their names:
##   ("var", i)              de Bruijn variable (same as surface)
##   ("lam", d, b)           lambda with elaborated domain d, body b
##                           (surface lam is ("lam", b): the domain is
##                           elaboration's insertion, from the pi type)
##   ("app", f, a)           application (same as surface)
##   ("pi", d, c)            non-dependent pi (same as surface)
##   ("zero")                zero (same as surface)
##   ("app", "suc", n)       suc applied (surface ("suc", n) is the
##                           unapplied-constructor shorthand)
##   ("app", "nil", a)       nil with element type A reified from the
##                           expected Vec type (surface nil is ("nil"))
##   (((("app", "cons"), a), n), h), t
##                           cons with A and index n reified from the
##                           expected type (surface ("cons", h, t))
##   ("nat") / ("vec", a, n) / ("univ")
##
## The reification of A and n from the expected type is the relational
## counterpart of what the direct elaborator inserts: on this fragment
## the surface syntax carries no implicit arguments, so elaboration's
## real work is (a) reifying them from the type and (b) recursively
## elaborating subterms. `etm` is ground on success whenever `tm` is
## ground and `ty`'s head constructor is manifest (same restriction as
## `checko`: host-side tag dispatch, no synthesis of pi/vec skeletons
## against a variable type — see decisions.org #59).

import minikanren
import rel_elab_dep
import strutils

proc failOut(): Goal =
  return proc(s: State): Stream = emptyStream()

# --- Core-term constructors ------------------------------------------------
#
# The elaborated core uses the direct elaborator's own application-spine
# shape: constructors are atoms applied via ("app", f, a), exactly as
# checkTermElab's output nests tApp nodes around tR globals. This makes
# the differential comparison against the direct side a 1:1 structural
# match (modulo atom-vs-refId for globals), and it is the shape #57's
# direct-style codegen will residualize.

proc lamCore*(d, b: RTerm): RTerm =
  rpair(ratom("lam"), rpair(d, rpair(b, rnil())))
proc nilCore*(a: RTerm): RTerm =
  appTm(ratom("nil"), a)
proc consCore*(a, n, h, t: RTerm): RTerm =
  appTm(appTm(appTm(appTm(ratom("cons"), a), n), h), t)
proc sucCore*(n: RTerm): RTerm = appTm(ratom("suc"), n)

proc tagOf(t: RTerm): string =
  if t.kind == rkPair and t.head.kind == rkAtom: t.head.name else: ""

# --- Elaboration with output -----------------------------------------------

proc elabo*(tm, ty, ctx, etm: RTerm): Goal
proc inferoOut*(tm, ty, ctx, etm: RTerm): Goal

proc lookupO(ctx: RTerm, i: int, ty: RTerm): Goal =
  if i == 0:
    fresh(proc(tl: RTerm): Goal = `==`(ctx, rpair(ty, tl)))
  else:
    fresh2(proc(h, tl: RTerm): Goal =
      conj(`==`(ctx, rpair(h, tl)), lookupO(tl, i - 1, ty)))

proc inferoOut*(tm, ty, ctx, etm: RTerm): Goal =
  if tm.kind == rkVar: return failOut()
  # atoms
  if tm.kind == rkAtom:
    if tm.name == "zero":
      return conj(`==`(ty, natTy()), `==`(etm, zeroTm()))
    # Type formation: nat, univ : univ (mirrors checko; `? : ?` per #52)
    if tm.name == "nat":
      return conj(`==`(ty, univTy()), `==`(etm, natTy()))
    if tm.name == "univ":
      return conj(`==`(ty, univTy()), `==`(etm, univTy()))
    return failOut()  # nil needs expected type
  let tag = tagOf(tm)
  if tag == "var":
    return conj(lookupO(ctx, parseInt(tm.tail.head.name), ty),
                `==`(etm, tm))
  if tag == "suc":
    return fresh(proc(en: RTerm): Goal =
      conj(inferoOut(tm.tail.head, natTy(), ctx, en),
        conj(`==`(ty, natTy()), `==`(etm, sucCore(en)))))
  if tag == "app":
    # f : Pi(d,c), a : d  =>  f a : c   (non-dependent: no substitution)
    let f = tm.tail.head; let a = tm.tail.tail.head
    if tagOf(f) == "lam":
      # f is lam: check against fresh Pi(d,c)
      return fresh4(proc(d, c, ef, ea: RTerm): Goal =
        conj(elabo(f, piTy(d, c), ctx, ef),
          conj(elabo(a, d, ctx, ea),
            conj(`==`(ty, c), `==`(etm, appTm(ef, ea))))))
    else:
      return fresh4(proc(d, c, ef, ea: RTerm): Goal =
        conj(inferoOut(f, piTy(d, c), ctx, ef),
          conj(elabo(a, d, ctx, ea),
            conj(`==`(ty, c), `==`(etm, appTm(ef, ea))))))
  if tag == "pi":
    # Pi(d,c) : univ if d:univ, c:univ
    let d = tm.tail.head; let c = tm.tail.tail.head
    return fresh2(proc(ed, ec: RTerm): Goal =
      conj(elabo(d, univTy(), ctx, ed),
        conj(elabo(c, univTy(), rpair(ed, ctx), ec),
          conj(`==`(ty, univTy()), `==`(etm, piTy(ed, ec))))))
  if tag == "vec":
    # Vec(A,n) : univ if A:univ, n:Nat
    let a = tm.tail.head; let n = tm.tail.tail.head
    return fresh2(proc(ea, en: RTerm): Goal =
      conj(elabo(a, univTy(), ctx, ea),
        conj(elabo(n, natTy(), ctx, en),
          conj(`==`(ty, univTy()), `==`(etm, vecTy(ea, en))))))
  # lam, cons: need expected type
  return failOut()

proc elabo*(tm, ty, ctx, etm: RTerm): Goal =
  if tm.kind == rkVar: return failOut()
  if tm.kind == rkAtom:
    if tm.name == "zero":
      return conj(`==`(ty, natTy()), `==`(etm, zeroTm()))
    if tm.name == "nil":
      # nil : Vec(A, zero). Reify A from the expected type.
      return fresh(proc(a: RTerm): Goal =
        conj(`==`(ty, vecTy(a, zeroTm())), `==`(etm, nilCore(a))))
    # Other atoms (nat/univ type formation) fall through to infer-mode.
  let tag = tagOf(tm)
  if tag == "lam":
    # lam(b) : Pi(d,c) if b : c in (d.ctx); domain reified from the type.
    if tagOf(ty) == "pi":
      let d = ty.tail.head; let c = ty.tail.tail.head
      return fresh(proc(eb: RTerm): Goal =
        conj(elabo(tm.tail.head, c, rpair(d, ctx), eb),
          `==`(etm, lamCore(d, eb))))
    return failOut()
  if tag == "cons":
    # cons(h,t) : Vec(A, suc(n)) if h:A, t:Vec(A,n); A and n reified.
    # The index n is itself a surface Nat term, so it is elaborated
    # (suc-shorthand -> applied form); the element type A is already
    # in core form on this fragment (nat/vec/univ/pi elaborate to
    # themselves), so it is spliced as-is.
    if tagOf(ty) == "vec":
      let a = ty.tail.head
      let nv = ty.tail.tail.head
      if tagOf(nv) == "suc":
        let n = nv.tail.head
        let h = tm.tail.head; let t = tm.tail.tail.head
        return fresh3(proc(eh, et, en: RTerm): Goal =
          conj(elabo(h, a, ctx, eh),
            conj(elabo(t, vecTy(a, n), ctx, et),
              conj(elabo(n, natTy(), ctx, en),
                `==`(etm, consCore(a, en, eh, et))))))
      return failOut()
    return failOut()
  # fallback: infer with output and unify
  fresh2(proc(ty2, et2: RTerm): Goal =
    conj(inferoOut(tm, ty2, ctx, et2),
      conj(`==`(ty, ty2), `==`(etm, et2))))
