## Relational type inference (typeo) — Track C
##
## Uses the independent minikanren.nim engine.
## Defines typeo(tm, ty, ctx) for STLC + Nat.
##
## Terms (S-expr encoding):
##   (var i)     — variable (de Bruijn index as atom)
##   (lam body)  — lambda
##   (app f a)   — application
##   zero        — Nat zero (atom)
##   (suc n)     — Nat successor
##
## Types:
##   nat         — atom
##   (arr d c)   — function type

import minikanren

# --- Term constructors ------------------------------------------------

proc natTy*(): RTerm = ratom("nat")
proc arrTy*(d, c: RTerm): RTerm =
  rpair(ratom("arr"), rpair(d, rpair(c, rnil())))
proc varTm*(i: int): RTerm =
  rpair(ratom("var"), rpair(ratom($i), rnil()))
proc lamTm*(body: RTerm): RTerm =
  rpair(ratom("lam"), rpair(body, rnil()))
proc appTm*(f, a: RTerm): RTerm =
  rpair(ratom("app"), rpair(f, rpair(a, rnil())))
proc zeroTm*(): RTerm = ratom("zero")
proc sucTm*(n: RTerm): RTerm =
  rpair(ratom("suc"), rpair(n, rnil()))

# --- The typeo relation -----------------------------------------------

proc typeo*(tm, ty, ctx: RTerm): Goal =
  ## typeo(tm, ty, ctx): tm has type ty in context ctx.
  ## ctx is a list of types, innermost first.
  disj(
    # zero : nat
    conj(`==`(tm, zeroTm()), `==`(ty, natTy())),
    disj(
      # suc(n) : nat if n : nat
      fresh(proc(n: RTerm): Goal =
        conj(`==`(tm, sucTm(n)),
          conj(typeo(n, natTy(), ctx),
            `==`(ty, natTy())))),
      disj(
        # var(0) : ty0 if ctx = (ty0 . _)
        fresh2(proc(ty0, ctxTail: RTerm): Goal =
          conj(`==`(tm, varTm(0)),
            conj(`==`(ctx, rpair(ty0, ctxTail)),
              `==`(ty, ty0)))),
        disj(
          # lam(b) : (arr d c) if b : c in (d . ctx)
          fresh3(proc(b, d, c: RTerm): Goal =
            conj(`==`(tm, lamTm(b)),
              conj(`==`(ty, arrTy(d, c)),
                typeo(b, c, rpair(d, ctx))))),
          # app(f, a) : c if f : (arr d c), a : d
          fresh4(proc(f, a, d, c: RTerm): Goal =
            conj(`==`(tm, appTm(f, a)),
              conj(typeo(f, arrTy(d, c), ctx),
                conj(typeo(a, d, ctx),
                  `==`(ty, c)))))
        )
      )
    )
  )
