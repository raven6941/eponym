import std/tables
import ../src/eponym/[staged_inject, eponym_init, elab]

proc check(ok: bool, msg: string) =
  if not ok: quit("FAIL: " & msg, 1)

macro staticArrow(): untyped =
  var globals = initTable[string, GEntry]()
  let nat = Term(kind: tR, refId: 1, refTyp: nil, refIsDefn: false,
    refVal: nil)
  let str = Term(kind: tR, refId: 2, refTyp: nil, refIsDefn: false,
    refVal: nil)
  globals["Nat"] = GEntry(tm: nat)
  globals["String"] = GEntry(tm: str)
  stageFamily(tmPi(nat, "n", str), globals, "StaticArrow", @[])

let descriptor = staticArrow()
check(descriptor == arrowRep(natRep(), stringRep()),
  "stageFamily emits a closed Arrow descriptor")

echo "test_stage_family: passed"
