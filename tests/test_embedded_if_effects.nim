## Embedded Nim conditionals evaluate only the selected Eponym branch.

import falsify
import eponym_mac
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
  proc chooseElif(): Int =
    if false: countBranchPostulate(10)
    elif true: countBranchPostulate(30)
    else: countBranchPostulate(20)
  proc chooseLinear(flag: Bool, value {.linear.}: Int): Int =
    if flag: countBranchPostulate(value)
    else: countBranchPostulate(value)
  proc addOne(value: Int): Int = value + 1

var rng = initRng(0x1F1F)
let cases = forAll(
  "embedded conditional evaluates only its selected branch", rng, 200,
  proc(r: var Rng): int = r.genInt(0, 2),
  proc(branch: int): bool =
    branchCalls = 0
    let actual = case branch
      of 0: chooseTrue()
      of 1: chooseFalse()
      else: chooseElif()
    actual == (case branch
      of 0: 10
      of 1: 20
      else: 30) and branchCalls == 1)
let intCases = forAll(
  "embedded Int addition accepts literal one", rng, 200,
  proc(r: var Rng): int = r.genInt(-1_000_000, 1_000_000),
  proc(value: int): bool = addOne(value) == value + 1)
let linearBranchCases = forAll(
  "linear value used once in either conditional branch", rng, 200,
  proc(r: var Rng): tuple[flag: bool, value: int] =
    (r.genBool(), r.genInt(-1000, 1000)),
  proc(input: tuple[flag: bool, value: int]): bool =
    branchCalls = 0
    chooseLinear(input.flag, input.value) == input.value and branchCalls == 1)
if not cases or not intCases or not linearBranchCases:
  quit(1)
echo "test_embedded_if_effects: conditional and Int literal properties passed"
