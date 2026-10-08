## Staged program synthesis: evalo backwards, no miniKanren overhead
##
## The relational program: evalo(expr, target) run backwards.
## - Static (staging time): the language (zero, suc, add, mul), the
##   evaluation rules, the search structure
## - Dynamic (runtime): the target value to synthesize expressions for
##
## Staging eliminates the miniKanren interpretive overhead:
## - No RTerm S-exprs (use dedicated Expr ADT)
## - No generic unification (direct structural recursion)
## - No Stream tree (direct seq accumulation)
## - No worklist (direct recursion, not iterative search)
##
## What remains: the search itself (it's a synthesis problem), but
## without the interpretive layer. Compare:
## - Relational: 300ms for 3 exprs = 3 (via fair search + unify + Stream)
## - Staged: direct generation via recursion on target structure

import times

# --- Dedicated Expr type (not RTerm) ---

type
  ExprKind = enum
    eZero, eSuc, eAdd, eMul
  
  Expr = ref object
    case kind: ExprKind
    of eZero: nil
    of eSuc: pred: Expr
    of eAdd, eMul: left, right: Expr

proc `$`(e: Expr): string =
  case e.kind
  of eZero: "zero"
  of eSuc: "(suc " & $e.pred & ")"
  of eAdd: "(add " & $e.left & " " & $e.right & ")"
  of eMul: "(mul " & $e.left & " " & $e.right & ")"

proc evalExpr(e: Expr): int =
  case e.kind
  of eZero: 0
  of eSuc: 1 + evalExpr(e.pred)
  of eAdd: evalExpr(e.left) + evalExpr(e.right)
  of eMul: evalExpr(e.left) * evalExpr(e.right)

# --- Staged synthesizer ---
# Takes target (runtime input), generates exprs via direct recursion.
# No miniKanren: no unify, no Stream, no worklist, no Subst.

proc synthStaged(target: int, maxDepth: int): seq[Expr] =
  ## Synthesize expressions evaluating to target, up to maxDepth.
  ## Direct structural recursion — the search structure from evalo,
  ## but without the relational machinery.
  result = @[]
  if maxDepth <= 0:
    return
  
  # Base: zero (if target is 0)
  if target == 0:
    result.add(Expr(kind: eZero))
  
  # suc: if target > 0, synthesize for target-1 then wrap
  if target > 0:
    for e in synthStaged(target - 1, maxDepth - 1):
      result.add(Expr(kind: eSuc, pred: e))
  
  # add: for each a+b=target, synthesize both sides
  # (limit to avoid explosion; in practice we'd bound this)
  if maxDepth >= 2:
    for a in 0..target:
      let b = target - a
      # Avoid duplicate symmetric cases and trivial zeros for brevity
      if a <= b:  # symmetry breaking
        for ea in synthStaged(a, maxDepth - 1):
          for eb in synthStaged(b, maxDepth - 1):
            # Skip if both are zero (would be infinite)
            if not (ea.kind == eZero and eb.kind == eZero):
              result.add(Expr(kind: eAdd, left: ea, right: eb))
  
  # mul: for each a*b=target
  if maxDepth >= 2 and target > 1:
    for a in 2..target:
      if target mod a == 0:
        let b = target div a
        if a <= b:  # symmetry breaking
          for ea in synthStaged(a, maxDepth - 1):
            for eb in synthStaged(b, maxDepth - 1):
              result.add(Expr(kind: eMul, left: ea, right: eb))

when isMainModule:
  import minikanren
  import rel_elab
  import rel_interp
  
  echo "=== Staged synthesis vs relational synthesis ==="
  echo ""
  echo "Task: synthesize expressions evaluating to 3"
  echo "Runtime input: target = 3"
  echo ""
  
  # Relational (via fair search)
  let q = freshVar()
  let targetRT = sucTm(sucTm(sucTm(zeroTm())))
  let start1 = cpuTime()
  let r1 = run(q, evalo(q, targetRT), 3)
  let t1 = cpuTime() - start1
  echo "Relational (miniKanren, fair search):"
  echo "  ", r1.len, " exprs in ", t1*1000, "ms"
  for e in r1: echo "    ", e
  echo "  Overhead: RTerm, unify, Stream, worklist, Subst"
  echo ""
  
  # Staged (direct)
  let start2 = cpuTime()
  let r2 = synthStaged(3, 4)
  let t2 = cpuTime() - start2
  echo "Staged (direct recursion, no miniKanren):"
  echo "  ", r2.len, " exprs in ", t2*1000, "ms"
  for e in r2[0..min(2, r2.high)]: echo "    ", e
  if r2.len > 3: echo "    ... (", r2.len - 3, " more)"
  echo "  Overhead: none (dedicated Expr, direct recursion)"
  echo ""
  
  # Verify correctness: all staged results evaluate to 3
  var allCorrect = true
  for e in r2:
    if evalExpr(e) != 3:
      allCorrect = false
      echo "  ERROR: ", e, " evaluates to ", evalExpr(e)
  if allCorrect:
    echo "  ✓ All ", r2.len, " staged results correctly evaluate to 3"
  
  if t2 > 0:
    echo ""
    echo "  Speedup: ", t1/t2, "x"
    echo "  (The search remains; only the interpretive overhead is gone.)"
