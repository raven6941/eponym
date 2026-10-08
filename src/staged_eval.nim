## Staged evaluator: evalo specialized to ground terms
##
## This is illuminating not because it's fast (though it is), but because
## it shows exactly what forward staging does to a relation:
##
## 1. The term tm is static (ground). The relation evalo(tm, v) has exactly
##    one derivation — no search, no backtracking.
## 2. Staging eliminates the relational machinery: no disj, no unify,
##    no Stream, no worklist. What remains is direct recursion on tm.
## 3. The relational addo/mulo become direct addVals/mulVals: the search
##    for the sum/product is replaced by computation.
## 4. Composition: stageEval(add(a,b)) = addVals(stageEval(a), stageEval(b)).
##    The staged pieces call each other, mirroring the term structure.
##
## The lesson: forward staging turns a relation into a function by fixing
## the "input" arguments and computing the "output" directly. The relational
## spec is the source; the staged code is the compiled result.
##
## Limit: this only works for fully ground tm. If tm has variables, we'd
## need to generate code with those as parameters (a compiler, not just
## an evaluator). That's the next step.

import minikanren
import rel_elab
import rel_interp
import strutils

proc addVals(a, b: RTerm): RTerm =
  ## Staged addo: direct computation, no search.
  ## addo(a,b,c) with a,b ground becomes c = addVals(a,b).
  if a.kind == rkAtom and a.name == "zero":
    return b
  elif a.kind == rkPair and a.head.kind == rkAtom and a.head.name == "suc":
    return sucTm(addVals(a.tail.head, b))
  else:
    raise newException(ValueError, "addVals: not a ground Nat, got " & $a)

proc mulVals(a, b: RTerm): RTerm =
  ## Staged mulo: direct computation, no search.
  if a.kind == rkAtom and a.name == "zero":
    return zeroTm()
  elif a.kind == rkPair and a.head.kind == rkAtom and a.head.name == "suc":
    return addVals(b, mulVals(a.tail.head, b))
  else:
    raise newException(ValueError, "mulVals: not a ground Nat, got " & $a)

proc stageEval(tm: RTerm): RTerm =
  ## Staged evalo: evalo(tm, v) with tm ground becomes v = stageEval(tm).
  ## No disj, no unify, no Stream — just structural recursion.
  case tm.kind
  of rkAtom:
    if tm.name == "zero":
      return tm
    else:
      raise newException(ValueError, "stageEval: unknown atom " & tm.name)
  of rkVar:
    raise newException(ValueError, "stageEval: term has variables, not ground")
  of rkPair:
    let head = tm.head
    if head.kind != rkAtom:
      raise newException(ValueError, "stageEval: head not an atom")
    case head.name
    of "suc":
      return sucTm(stageEval(tm.tail.head))
    of "add":
      let av = stageEval(tm.tail.head)
      let bv = stageEval(tm.tail.tail.head)
      return addVals(av, bv)
    of "mul":
      let av = stageEval(tm.tail.head)
      let bv = stageEval(tm.tail.tail.head)
      return mulVals(av, bv)
    else:
      raise newException(ValueError, "stageEval: unknown op " & head.name)

when isMainModule:
  import times
  
  echo "=== Staged evalo: what forward staging teaches ==="
  echo ""
  echo "The relation evalo(tm, v) with tm ground has one derivation."
  echo "Staging removes the search; what remains is direct recursion."
  echo ""
  
  # (1 + 2) * 3 = 9
  let tm = mulTm(
    addTm(sucTm(zeroTm()), sucTm(sucTm(zeroTm()))),
    sucTm(sucTm(sucTm(zeroTm()))))
  
  echo "Term: (mul (add 1 2) 3), expected: 9"
  echo ""
  
  # Interpretive
  let q = freshVar()
  let start1 = cpuTime()
  let r1 = run(q, evalo(tm, q), 1)
  let time1 = cpuTime() - start1
  echo "Interpretive evalo:"
  echo "  result: ", if r1.len > 0: $r1[0] else: "(none)"
  echo "  time: ", time1*1000, "ms"
  echo "  machinery: disj, unify, Stream, worklist, subst"
  echo ""
  
  # Staged
  let start2 = cpuTime()
  let r2 = stageEval(tm)
  let time2 = cpuTime() - start2
  echo "Staged stageEval:"
  echo "  result: ", r2
  echo "  time: ", time2*1000, "ms"
  echo "  machinery: direct recursion, no relational overhead"
  echo ""
  
  # Verify they agree
  if r1.len > 0 and $r1[0] == $r2:
    echo "✓ Both agree: ", r2
  else:
    echo "✗ MISMATCH: interpretive=", if r1.len>0: $r1[0] else: "(none)", " staged=", r2
