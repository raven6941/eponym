## Benchmark for #57: generated direct-style elaborator vs relational vs direct.
##
## Compares three approaches on Vec(Nat, N) elaboration:
##   1. Generated direct-style (gen_elabo_vec.nim): no Goal/Stream, just matching
##   2. Unstaged relational (elabo from rel_elab_out.nim)
##   3. Direct elaborator (checkTermElab via elabCheck)
##
## Differential correctness + wall-clock at N=2 and N=8.

import options
import times
import minikanren
import rel_elab_dep
import rel_elab_out
import staging/gen_elabo_vec
import elab

proc timeIt(reps: int, body: proc()): float =
  result = high(float)
  for _ in 1 .. reps:
    let t0 = cpuTime()
    body()
    result = min(result, (cpuTime() - t0) * 1e6)  # microseconds

proc makeVec(n: int): RTerm =
  ## Build cons(0, cons(0, ... nil)) with n elements
  result = nilTm()
  for _ in 1 .. n:
    result = consTm(zeroTm(), result)

proc makeVecTy(n: int): RTerm =
  var idx = zeroTm()
  for _ in 1 .. n:
    idx = sucTm(idx)
  vecTy(natTy(), idx)

proc benchN(n: int) =
  echo "=== N=", n, " ==="
  let tm = makeVec(n)
  let ty = makeVecTy(n)

  # 1. Generated direct-style
  var genRes: Option[RTerm]
  let tGen = timeIt(100, proc() =
    genRes = case n
      of 2: elaboVec2(tm)
      of 8: elaboVec8(tm)
      else: none(RTerm))
  echo "generated direct: ", tGen, " us, success=", genRes.isSome

  # 2. Unstaged relational elabo
  var relRes: seq[RTerm]
  let tRel = timeIt(100, proc() =
    let etm = freshVar()
    relRes = run(etm, elabo(tm, ty, rnil(), etm), 1))
  echo "unstaged relational: ", tRel, " us, success=", relRes.len > 0

  # 3. Direct elaborator (checkTermElab via elabCheck)
  # Build surface syntax for Vec(Nat, n)
  var src = "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\n"
  src &= "data Vec (A : Type 0) : Nat -> Type 0 where\n| nil : Vec A zero\n| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)\n"
  var idxStr = "zero"
  for _ in 1 .. n: idxStr = "(suc " & idxStr & ")"
  src &= "proc t : Vec Nat " & idxStr & " =\n  "
  # Build: cons Nat <len-of-tail> zero <tail>, innermost first
  var consStr = "nil Nat"
  for i in 1 .. n:
    var idx2 = "zero"
    for _ in 1 ..< i: idx2 = "suc (" & idx2 & ")"
    consStr = "cons Nat (" & idx2 & ") zero (" & consStr & ")"
  src &= consStr & "\n"

  var directOk = false
  let tDir = timeIt(20, proc() =
    try:
      discard elabCheck(src)
      directOk = true
    except ElabError:
      directOk = false)
  echo "direct checkTermElab: ", tDir, " us, success=", directOk

  # Differential: generated vs relational output
  if genRes.isSome and relRes.len > 0:
    echo "gen vs rel match: ", $genRes.get == $relRes[0]
  echo ""

when isMainModule:
  benchN(2)
  benchN(8)
