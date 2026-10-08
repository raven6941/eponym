## Staged typeo via Nim macro — automated branch pruning (issue #14)
##
## The `stagedTypeo` macro analyzes the query pattern at compile time
## and prunes statically-impossible branches.
##
## Supported patterns:
## - ty: `natTy()` (ground), `arrTy(d,c)` (ground), or var (ident)
## - ctx: `rnil()` (ground nil), `rpair(h,t)` (ground cons), or var
##
## Pruning rules:
## - zero/suc branches: require ty=nat. Prune if ty is ground non-nat.
## - var branch: requires ctx=(h.t). Prune if ctx is ground nil.
## - lam branch: produces ty=(arr d c). Prune if ty is ground nat.
## - app branch: always kept (cannot prune statically).

import macros
import minikanren
import rel_elab

proc isNatTy(n: NimNode): bool =
  ## True if n is `natTy()` call
  n.kind == nnkCall and n.len >= 1 and
    n[0].kind == nnkIdent and $n[0] == "natTy"

proc isArrTy(n: NimNode): bool =
  ## True if n is `arrTy(...)` call
  n.kind == nnkCall and n.len >= 1 and
    n[0].kind == nnkIdent and $n[0] == "arrTy"

proc isRnil(n: NimNode): bool =
  ## True if n is `rnil()` call
  n.kind == nnkCall and n.len >= 1 and
    n[0].kind == nnkIdent and $n[0] == "rnil"

proc isRpair(n: NimNode): bool =
  n.kind == nnkCall and n.len >= 1 and
    n[0].kind == nnkIdent and $n[0] == "rpair"

proc isVar(n: NimNode): bool =
  ## True if n is a simple identifier (logic variable)
  n.kind == nnkIdent

macro stagedTypeo*(tm, ty, ctx: untyped): untyped =
  ## Generate specialized typeo with pruned branches.
  ## tm, ty, ctx are RTerm expressions.
  let tyIsNat = isNatTy(ty)
  let tyIsArr = isArrTy(ty)
  let tyIsVar = isVar(ty)
  let ctxIsNil = isRnil(ctx)
  let ctxIsCons = isRpair(ctx)
  let ctxIsVar = isVar(ctx)
  
  # Pruning: conservative (keep if not definitely impossible)
  let keepZero = not tyIsArr
  let keepSuc = not tyIsArr
  let keepVar = not ctxIsNil
  let keepLam = not tyIsNat
  let keepApp = true  # always keep (conservative)
  
  # Build branches as NimNode calls
  # We use newCall to avoid hygiene issues with `==`
  var branches: seq[NimNode] = @[]
  
  # Helper to create `==`(a, b) call resolving to minikanren.==
  proc mkEq(a, b: NimNode): NimNode =
    # Use eq (non-operator alias) to avoid hygiene issues
    newCall(newDotExpr(ident("minikanren"), ident("eq")), a, b)
  
  proc mkConj(g1, g2: NimNode): NimNode =
    newCall(newDotExpr(ident("minikanren"), ident("conj")), g1, g2)
  
  proc mkDisj(g1, g2: NimNode): NimNode =
    newCall(newDotExpr(ident("minikanren"), ident("disj")), g1, g2)
  
  if keepZero:
    # conj(==(tm, zeroTm()), ==(ty, natTy()))
    let eq1 = mkEq(tm, newCall(ident("zeroTm")))
    let eq2 = mkEq(ty, newCall(ident("natTy")))
    branches.add(mkConj(eq1, eq2))
  
  if keepSuc:
    # fresh(n => conj(==(tm, sucTm(n)), conj(typeo(n, nat, ctx), ==(ty, nat))))
    # For now, use interpretive typeo for the recursive call
    # Construct the fresh body as a lambda
    let n = ident("n")
    let eqTm = mkEq(tm, newCall(ident("sucTm"), n))
    let recCall = newCall(ident("typeo"), n, newCall(ident("natTy")), ctx)
    let eqTy = mkEq(ty, newCall(ident("natTy")))
    let inner = mkConj(recCall, eqTy)
    let body = mkConj(eqTm, inner)
    # Use quote for the fresh wrapper
    branches.add(quote do:
      minikanren.fresh(proc(`n`: RTerm): Goal = `body`))
  
  if keepVar:
    branches.add(quote do:
      minikanren.fresh2(proc(ty0, ctxTail: RTerm): Goal =
        minikanren.conj(minikanren.eq(`tm`, varTm(0)),
          minikanren.conj(minikanren.eq(`ctx`, rpair(ty0, ctxTail)),
            minikanren.eq(`ty`, ty0)))))
  
  if keepLam:
    branches.add(quote do:
      minikanren.fresh3(proc(b, d, c: RTerm): Goal =
        minikanren.conj(minikanren.eq(`tm`, lamTm(b)),
          minikanren.conj(minikanren.eq(`ty`, arrTy(d, c)),
            typeo(b, c, rpair(d, `ctx`))))))
  
  if keepApp:
    branches.add(quote do:
      minikanren.fresh4(proc(f, a, d, c: RTerm): Goal =
        minikanren.conj(minikanren.eq(`tm`, appTm(f, a)),
          minikanren.conj(typeo(f, arrTy(d, c), `ctx`),
            minikanren.conj(typeo(a, d, `ctx`),
              minikanren.eq(`ty`, c))))))
  
  if branches.len == 0:
    result = newCall(newDotExpr(ident("minikanren"), ident("emptyStream")))
    # Actually need a Goal, not a Stream. Return a failing goal:
    result = quote do:
      (proc(s: Subst): Stream = minikanren.emptyStream())
  elif branches.len == 1:
    result = branches[0]
  else:
    result = branches[^1]
    for i in countdown(branches.high - 1, 0):
      result = mkDisj(branches[i], result)

when isMainModule:
  import times
  
  echo "=== stagedTypeo macro test ==="
  echo ""
  
  # Test 1: synth nat (q, nat, nil) — should prune var/lam
  echo "Test 1: stagedTypeo(q, natTy(), rnil())"
  let start1 = cpuTime()
  let q1 = freshVar()
  let r1 = run(q1, stagedTypeo(q1, natTy(), rnil()), 5)
  let time1 = cpuTime() - start1
  echo "  Results: ", r1.len
  for t in r1: echo "    ", t
  echo "  Time: ", time1 * 1000, "ms"
  echo ""
  
  # Test 2: infer type of zero (zero, ?ty, nil) — should keep zero, prune others?
  # ty is var, so keep all that could match
  echo "Test 2: stagedTypeo(zeroTm(), q, rnil())"
  let q2 = freshVar()
  let r2 = run(q2, stagedTypeo(zeroTm(), q2, rnil()), 3)
  echo "  Results: ", r2.len
  for t in r2: echo "    ", t
  echo ""
  
  echo "Macro staging works!"
