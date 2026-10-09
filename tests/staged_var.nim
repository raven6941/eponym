## Staged synthesis with context — var branch (issue #14)
##
## Extends the staged macro to handle non-empty contexts.
## Pattern: typeo(q, natTy(), rpair(natTy(), rnil()))
##   - Synthesize Nat terms with var(0) : Nat in scope.
##
## Branches (pruned):
## - zero: q = zero ✓
## - suc: q = suc(n), recurse ✓
## - var: q = var(0) ✓ (ctx head is nat, matches ty=nat)
## - lam: prune (produces arr)
## - app: prune (conservative)

import macros
import minikanren
import rel_elab

macro stagedWithVar*(tm: untyped): untyped =
  ## Generate staged synthesizer for Nat with var(0):Nat in context.
  let procName = genSym(nskProc, "stagedNatVar")
  let q = genSym(nskParam, "q")
  let n = genSym(nskParam, "n")
  
  # zero: eq(q, zeroTm())
  let zeroBranch = newCall(
    newDotExpr(ident("minikanren"), ident("eq")),
    q, newCall(ident("zeroTm")))
  
  # suc: fresh(n => conj(eq(q, sucTm(n)), procName(n)))
  let recCall = newCall(procName, n)
  let sucEq = newCall(
    newDotExpr(ident("minikanren"), ident("eq")),
    q, newCall(ident("sucTm"), n))
  let sucConj = newCall(
    newDotExpr(ident("minikanren"), ident("conj")),
    sucEq, recCall)
  let sucLambda = newProc(
    params = @[ident("Goal"), newIdentDefs(n, ident("RTerm"))],
    body = newStmtList(sucConj))
  let sucBranch = newCall(
    newDotExpr(ident("minikanren"), ident("fresh")),
    sucLambda)
  
  # var: eq(q, varTm(0)) — no recursion, ctx head is statically nat
  let varBranch = newCall(
    newDotExpr(ident("minikanren"), ident("eq")),
    q, newCall(ident("varTm"), newLit(0)))
  
  # disj(zero, disj(suc, var))
  let innerDisj = newCall(
    newDotExpr(ident("minikanren"), ident("disj")),
    sucBranch, varBranch)
  let outerDisj = newCall(
    newDotExpr(ident("minikanren"), ident("disj")),
    zeroBranch, innerDisj)
  
  let procDef = newProc(
    name = procName,
    params = @[ident("Goal"), newIdentDefs(q, ident("RTerm"))],
    body = newStmtList(outerDisj))
  
  let call = newCall(procName, tm)
  result = quote do:
    block:
      `procDef`
      `call`

when isMainModule:
  import times
  echo "=== Staged synthesis with var ==="
  let q = freshVar()
  let start = cpuTime()
  let r = run(q, stagedWithVar(q), 5)
  let time = cpuTime() - start
  echo "Results: ", r.len, " in ", time*1000, "ms"
  for t in r: echo "  ", t
  echo ""
  echo "Expected: zero, (suc zero), (var 0), ... (order may vary)"
