## Embedded Nim conditionals evaluate only the selected Eponym branch.

import eponym_mac

type BranchResult = int
var branchCalls = 0

proc countBranch(value: int): int =
  inc branchCalls
  value

eponymBlock:
  import "../lib/bool.ep"
  postulate(Int, Univ)
  postulate(countBranchPostulate, Int -> Int)
  bindPostulate(countBranchPostulate, countBranch)
  proc chooseTrue(): Int =
    if true: countBranchPostulate(10) else: countBranchPostulate(20)
  proc chooseFalse(): Int =
    if false: countBranchPostulate(10) else: countBranchPostulate(20)
  proc addOne(value: Int): Int = value + 1

when isMainModule:
  doAssert addOne(41) == 42
  branchCalls = 0
  doAssert chooseTrue() == 10
  doAssert branchCalls == 1
  branchCalls = 0
  doAssert chooseFalse() == 20
  doAssert branchCalls == 1
  echo "test_embedded_if_effects: one selected branch evaluated"
