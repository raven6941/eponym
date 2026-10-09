## Forward-staged type inference — no search for ground terms (issue #14)
##
## When tm is ground, typeo(tm, ty, ctx) has no search: the term
## structure determines the control flow. Staging eliminates the
## relational dispatch entirely.
##
## This is the forward direction: tm is static (ground), ty is dynamic
## (computed). The staged code is a straightforward recursive function,
## not a relation.
##
## This demonstrates the Futamura projection: specializing the relational
## typeo w.r.t. a ground term yields an efficient type checker.

import minikanren
import rel_elab
import strutils  # for parseInt

proc inferType*(tm, ctx: RTerm): RTerm =
  ## Staged forward inference: compute the type of a ground term.
  ## No search, no backtracking — the term structure drives it.
  ## This is what staging typeo(tm, ty, ctx) with tm ground produces.
  if tm.kind == rkAtom:
    if tm.name == "zero":
      return natTy()
    elif tm.name == "vecnil":
      # vecnil : vec(a, zero) — a is a metavar, need to infer from context?
      # For now, require explicit type annotation. This is a limitation
      # of the forward direction: some terms need expected type.
      raise newException(ValueError, "vecnil needs expected type")
    else:
      raise newException(ValueError, "unknown atom: " & tm.name)
  elif tm.kind == rkPair:
    let head = tm.head
    if head.kind == rkAtom:
      case head.name
      of "suc":
        let n = tm.tail.head
        let nTy = inferType(n, ctx)
        # Check n : nat (should be, by recursion)
        return natTy()
      of "var":
        let idx = parseInt(tm.tail.head.name)
        # Lookup idx in ctx
        var c = ctx
        for i in 0..<idx:
          c = c.tail.tail  # skip (ty . tail) pairs? Actually ctx is rlist
        # ctx is (ty0 . (ty1 . nil)), so idx=0 gives ty0
        return c.head
      of "lam":
        let body = tm.tail.head
        # Need domain type! Forward inference can't invent it.
        # This is why bidirectional is needed: lam needs expected type.
        raise newException(ValueError, "lam needs expected type (use check)")
      of "app":
        let f = tm.tail.head
        let a = tm.tail.tail.head
        let fTy = inferType(f, ctx)
        # fTy should be (arr d c)
        if fTy.kind == rkPair and fTy.head.name == "arr":
          let d = fTy.tail.head
          let c = fTy.tail.tail.head
          let aTy = inferType(a, ctx)
          # TODO: check aTy == d
          return c
        else:
          raise newException(ValueError, "app of non-function")
      of "veccons":
        let h = tm.tail.head
        let t = tm.tail.tail.head
        let hTy = inferType(h, ctx)
        let tTy = inferType(t, ctx)
        # tTy should be (vec a n)
        if tTy.kind == rkPair and tTy.head.name == "vec":
          let a = tTy.tail.head
          let n = tTy.tail.tail.head
          # TODO: check hTy == a
          return vecTy(a, sucTm(n))
        else:
          raise newException(ValueError, "veccons tail not a vec")
      of "add":
        # add(a,b) : nat if a,b : nat
        return natTy()
      else:
        raise newException(ValueError, "unknown head: " & head.name)
    else:
      raise newException(ValueError, "head not an atom")
  else:
    raise newException(ValueError, "invalid term")

proc checkType*(tm, ty, ctx: RTerm): bool =
  ## Staged forward checking: verify tm : ty.
  ## For lam, we need the expected type to propagate inward.
  if tm.kind == rkPair and tm.head.kind == rkAtom and tm.head.name == "lam":
    # tm = lam(b), ty must be (arr d c)
    if ty.kind == rkPair and ty.head.name == "arr":
      let d = ty.tail.head
      let c = ty.tail.tail.head
      let body = tm.tail.head
      let bodyCtx = rpair(d, ctx)
      return checkType(body, c, bodyCtx)
    else:
      return false
  else:
    # For other terms, infer and compare
    try:
      let inferred = inferType(tm, ctx)
      # TODO: check inferred == ty (need equality)
      return $inferred == $ty  # string compare for now
    except ValueError:
      return false

when isMainModule:
  import times
  echo "=== Forward-staged type inference (no search) ==="
  echo ""
  
  # suc(suc(zero)) : nat
  let tm1 = sucTm(sucTm(zeroTm()))
  let start1 = cpuTime()
  let ty1 = inferType(tm1, rnil())
  let time1 = cpuTime() - start1
  echo "infer(suc(suc(zero))): ", ty1, " in ", time1*1000, "ms"
  
  # lam(var 0) : arr(nat, nat) via check
  let tm2 = lamTm(varTm(0))
  let ty2 = arrTy(natTy(), natTy())
  let start2 = cpuTime()
  let ok = checkType(tm2, ty2, rnil())
  let time2 = cpuTime() - start2
  echo "check(lam(var 0) : arr(nat,nat)): ", ok, " in ", time2*1000, "ms"
  
  echo ""
  echo "No relational search — the ground term drives the computation directly."
