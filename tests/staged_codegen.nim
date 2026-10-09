## Full codegen staged macro — generates the proc, not just dispatch (issue #14)
##
## The `stagedCodegen` macro fully generates a specialized recursive proc
## for the (tm, natTy(), rnil()) pattern. Unlike `stagedTypeoRec` which
## dispatches to a pre-written `synthNat`, this macro *emits* the proc body.

import macros
import minikanren
import rel_elab

macro stagedCodegen*(tm: untyped): untyped =
  ## Generate a specialized synthesizer for Nat terms.
  ## Equivalent to synthNat, but the code is generated, not hand-written.
  ##
  ## Generates:
  ##   block:
  ##     proc staged(q: RTerm): Goal =
  ##       disj(eq(q, zeroTm()),
  ##            fresh(n => conj(eq(q, sucTm(n)), staged(n))))
  ##     staged(tm)
  
  let procName = genSym(nskProc, "stagedNat")
  let q = genSym(nskParam, "q")
  let n = genSym(nskParam, "n")
  
  # Build: proc stagedNat(q: RTerm): Goal = ...
  # Body: disj(eq(q, zeroTm()), fresh(n => conj(eq(q, sucTm(n)), stagedNat(n))))
  
  let zeroBranch = newCall(
    newDotExpr(ident("minikanren"), ident("eq")),
    q, newCall(ident("zeroTm")))
  
  # The recursive call: stagedNat(n)
  let recCall = newCall(procName, n)
  
  # fresh body: proc(n: RTerm): Goal = conj(eq(q, sucTm(n)), stagedNat(n))
  let sucEq = newCall(
    newDotExpr(ident("minikanren"), ident("eq")),
    q, newCall(ident("sucTm"), n))
  let conjBody = newCall(
    newDotExpr(ident("minikanren"), ident("conj")),
    sucEq, recCall)
  let freshLambda = newProc(
    params = @[ident("Goal"), newIdentDefs(n, ident("RTerm"))],
    body = newStmtList(conjBody))
  let freshCall = newCall(
    newDotExpr(ident("minikanren"), ident("fresh")),
    freshLambda)
  
  let sucBranch = freshCall
  
  let disjCall = newCall(
    newDotExpr(ident("minikanren"), ident("disj")),
    zeroBranch, sucBranch)
  
  let procDef = newProc(
    name = procName,
    params = @[ident("Goal"), newIdentDefs(q, ident("RTerm"))],
    body = newStmtList(disjCall))
  
  # Return: block: proc ...; procName(tm)
  let call = newCall(procName, tm)
  result = newStmtList(
    newBlockStmt(newStmtList(procDef)),
    call)
  # Actually, need the block to return the call value
  result = quote do:
    block:
      `procDef`
      `call`

when isMainModule:
  import times
  echo "=== Full codegen staged macro ==="
  let q = freshVar()
  let start = cpuTime()
  let r = run(q, stagedCodegen(q), 5)
  let time = cpuTime() - start
  echo "Results: ", r.len, " in ", time*1000, "ms"
  for t in r: echo "  ", t
