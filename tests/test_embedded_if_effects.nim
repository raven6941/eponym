## Embedded Nim conditionals evaluate only the selected Eponym branch.

import falsify
import eponym_mac
import std/options
var branchCalls = 0

proc countBranch(value: int): int =
  inc branchCalls
  value

eponymRuntimeBridgeTestBlock:
  import "../lib/bool.ep"
  import "../lib/option.ep"
  import "../lib/list.ep"
  postulate(Int, Univ)
  runtimeOption(Option)
  runtimeList(List)
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
  proc chooseOptionalLinear(optionValue: Option[Int],
                            value {.linear.}: Int): Int =
    (optionElim[Int, lam(u: Option[Int]) => Pi(unit: unitTy, Int)](
      lam(unit: unitTy) => countBranchPostulate(value),
      lam(payload: Int) => lam(unit: unitTy) => countBranchPostulate(value),
      optionValue))(unitv)
  proc chooseChainLinear(values: List[Int], value {.linear.}: Int): Int =
    listElim[Int, lam(u: List[Int]) => Int](
      countBranchPostulate(value),
      lam(item: Int) => lam(tail: List[Int]) => lam(ih: Int) => ih,
      values)
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
let payloadBranchCases = forAll(
  "linear use is checked across payload-bearing Option cases", rng, 200,
  proc(r: var Rng): tuple[present: bool, payload: int, value: int] =
    (r.genBool(), r.genInt(-1000, 1000), r.genInt(-1000, 1000)),
  proc(input: tuple[present: bool, payload: int, value: int]): bool =
    branchCalls = 0
    let optionValue = if input.present: some(input.payload) else: none(int)
    chooseOptionalLinear(optionValue, input.value) == input.value and
      branchCalls == 1)
let strictNilCaseCases = forAll(
  "strict nil-case result evaluates once for every generated List length", rng, 200,
  proc(r: var Rng): int = r.genInt(0, 20),
  proc(length: int): bool =
    branchCalls = 0
    let value = length + 17
    let values = newSeq[int](length)
    chooseChainLinear(values, value) == value and branchCalls == 1,
  shrinkInt)
branchCalls = 0
let noneCaseWorks = chooseOptionalLinear(none(int), 17) == 17 and
  branchCalls == 1
branchCalls = 0
let someCaseWorks = chooseOptionalLinear(some(9), 23) == 23 and
  branchCalls == 1
branchCalls = 0
let emptyChainWorks = chooseChainLinear(newSeq[int](0), 31) == 31 and
  branchCalls == 1
branchCalls = 0
let recursiveChainWorks = chooseChainLinear(@[2, 3, 5, 7], 37) == 37 and
  branchCalls == 1
if not cases or not intCases or not linearBranchCases or not payloadBranchCases or
    not strictNilCaseCases or not noneCaseWorks or not someCaseWorks or
    not emptyChainWorks or not recursiveChainWorks:
  quit(1)
echo "test_embedded_if_effects: conditional and Int literal properties passed"
