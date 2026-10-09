## Relational interpreter for Nat arithmetic — Track C
##
## evalo(tm, v): closed term tm evaluates to value v.
## Language: zero, (suc n), (add a b), (mul a b)
## Values: zero, (suc v) (canonical Nats)
##
## Forward direction: tm is ground. The interpreter has no search;
## the term structure determines control flow. Staging eliminates
## the interpretive dispatch.

import minikanren
import rel_elab  # zeroTm, sucTm

proc addTm*(a, b: RTerm): RTerm =
  rpair(ratom("add"), rpair(a, rpair(b, rnil())))
proc mulTm*(a, b: RTerm): RTerm =
  rpair(ratom("mul"), rpair(a, rpair(b, rnil())))

proc addo*(a, b, c: RTerm): Goal =
  ## addo(a, b, c): a + b = c, relational Nat addition.
  disj(
    conj(`==`(a, zeroTm()), `==`(c, b)),
    fresh3(proc(ap, cp, unused: RTerm): Goal =
      conj(`==`(a, sucTm(ap)),
        conj(`==`(c, sucTm(cp)),
          addo(ap, b, cp))))
  )

proc mulo*(a, b, c: RTerm): Goal =
  ## mulo(a, b, c): a * b = c, relational Nat multiplication.
  disj(
    conj(`==`(a, zeroTm()), `==`(c, zeroTm())),
    fresh4(proc(ap, cp, pb, unused: RTerm): Goal =
      conj(`==`(a, sucTm(ap)),
        conj(mulo(ap, b, pb),
          conj(addo(pb, b, cp),
            `==`(c, cp)))))
  )

proc evalo*(tm, v: RTerm): Goal =
  ## evalo(tm, v): closed arithmetic term tm evaluates to v.
  disj(
    conj(`==`(tm, zeroTm()), `==`(v, zeroTm())),
    disj(
      fresh2(proc(n, vn: RTerm): Goal =
        conj(`==`(tm, sucTm(n)),
          conj(evalo(n, vn),
            `==`(v, sucTm(vn))))),
      disj(
        fresh4(proc(a, b, va, vb: RTerm): Goal =
          conj(`==`(tm, addTm(a, b)),
            conj(evalo(a, va),
              conj(evalo(b, vb),
                addo(va, vb, v))))),
        fresh4(proc(a, b, va, vb: RTerm): Goal =
          conj(`==`(tm, mulTm(a, b)),
            conj(evalo(a, va),
              conj(evalo(b, vb),
                mulo(va, vb, v)))))
      )
    )
  )

when isMainModule:
  import times
  echo "=== evalo: relational arithmetic interpreter ==="
  echo ""
  
  # 1 + 2 = 3
  let q = freshVar()
  let tm = addTm(sucTm(zeroTm()), sucTm(sucTm(zeroTm())))
  let start = cpuTime()
  let r = run(q, evalo(tm, q), 2)
  let time = cpuTime() - start
  echo "eval(add(1, 2)): ", r.len, " result(s) in ", time*1000, "ms"
  for t in r: echo "  ", t
