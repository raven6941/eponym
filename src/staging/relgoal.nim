## RelGoal prototype: relations as data
##
## Implements the Phase 3 design: RelGoal as inspectable data (not closures),
## with toGoal() interpreting via the existing engine.

import minikanren
import tables
import sequtils

type
  RelGoalKind* = enum
    rgFail, rgSucceed,
    rgEq, rgNeq,
    rgConj, rgDisj,
    rgFresh,
    rgCall,
    rgSetEq,
    rgBranch

  RelGoal* = ref object
    case kind*: RelGoalKind
    of rgFail, rgSucceed:
      discard
    of rgEq, rgNeq:
      left*, right*: RTerm
    of rgConj, rgDisj:
      leftG*, rightG*: RelGoal
    of rgFresh:
      varName*: string
      body*: RelGoal
    of rgCall:
      relName*: string
      args*: seq[RTerm]
    of rgSetEq:
      cells*, values*: seq[RTerm]
    of rgBranch:
      vars*: seq[RTerm]

proc rgFail*(): RelGoal = RelGoal(kind: rgFail)
proc rgSucceed*(): RelGoal = RelGoal(kind: rgSucceed)
proc rgEq*(a, b: RTerm): RelGoal = RelGoal(kind: rgEq, left: a, right: b)
proc rgNeq*(a, b: RTerm): RelGoal = RelGoal(kind: rgNeq, left: a, right: b)
proc rgConj*(a, b: RelGoal): RelGoal = RelGoal(kind: rgConj, leftG: a, rightG: b)
proc rgDisj*(a, b: RelGoal): RelGoal = RelGoal(kind: rgDisj, leftG: a, rightG: b)
proc rgFresh*(name: string, body: RelGoal): RelGoal =
  RelGoal(kind: rgFresh, varName: name, body: body)
proc rgCall*(name: string, args: seq[RTerm]): RelGoal =
  RelGoal(kind: rgCall, relName: name, args: args)

proc `$`*(rg: RelGoal): string =
  case rg.kind
  of rgFail: "fail"
  of rgSucceed: "succeed"
  of rgEq: "(" & $rg.left & " == " & $rg.right & ")"
  of rgNeq: "(" & $rg.left & " =/= " & $rg.right & ")"
  of rgConj: "(" & $rg.leftG & " ∧ " & $rg.rightG & ")"
  of rgDisj: "(" & $rg.leftG & " ∨ " & $rg.rightG & ")"
  of rgFresh: "(fresh " & rg.varName & " " & $rg.body & ")"
  of rgCall: "(" & rg.relName & " " & $rg.args & ")"
  of rgSetEq: "(setEq " & $rg.cells & " " & $rg.values & ")"
  of rgBranch: "(branch " & $rg.vars & ")"

# --- Substitution (before toGoal) ---

proc substTermAtom(t: RTerm, placeholder: RTerm, replacement: RTerm): RTerm =
  if t.kind == rkAtom and t.name == placeholder.name:
    replacement
  elif t.kind == rkPair:
    rpair(substTermAtom(t.head, placeholder, replacement),
          substTermAtom(t.tail, placeholder, replacement))
  else:
    t

proc substAtom*(rg: RelGoal, placeholder: RTerm, replacement: RTerm): RelGoal =
  case rg.kind
  of rgFail, rgSucceed: rg
  of rgEq: rgEq(substTermAtom(rg.left, placeholder, replacement),
                substTermAtom(rg.right, placeholder, replacement))
  of rgNeq: rgNeq(substTermAtom(rg.left, placeholder, replacement),
                  substTermAtom(rg.right, placeholder, replacement))
  of rgConj: rgConj(substAtom(rg.leftG, placeholder, replacement),
                    substAtom(rg.rightG, placeholder, replacement))
  of rgDisj: rgDisj(substAtom(rg.leftG, placeholder, replacement),
                    substAtom(rg.rightG, placeholder, replacement))
  of rgFresh:
    rgFresh(rg.varName, substAtom(rg.body, placeholder, replacement))
  of rgCall:
    rgCall(rg.relName, rg.args.mapIt(substTermAtom(it, placeholder, replacement)))
  of rgSetEq:
    RelGoal(kind: rgSetEq,
            cells: rg.cells.mapIt(substTermAtom(it, placeholder, replacement)),
            values: rg.values.mapIt(substTermAtom(it, placeholder, replacement)))
  of rgBranch:
    RelGoal(kind: rgBranch,
            vars: rg.vars.mapIt(substTermAtom(it, placeholder, replacement)))

# --- toGoal: interpret via existing engine ---

proc toGoal*(rg: RelGoal, relEnv: Table[string, RelGoal] = initTable[string, RelGoal]()): Goal =
  case rg.kind
  of rgFail:
    proc(s: State): Stream = Stream(kind: skEmpty)
  of rgSucceed:
    proc(s: State): Stream = Stream(kind: skCons, head: s, tail: Stream(kind: skEmpty))
  of rgEq:
    `==`(rg.left, rg.right)
  of rgNeq:
    `=/=`(rg.left, rg.right)
  of rgConj:
    conj(toGoal(rg.leftG, relEnv), toGoal(rg.rightG, relEnv))
  of rgDisj:
    disj(toGoal(rg.leftG, relEnv), toGoal(rg.rightG, relEnv))
  of rgFresh:
    let v = freshVar()
    let placeholder = ratom("__var_" & rg.varName)
    let bodySubst = substAtom(rg.body, placeholder, v)
    toGoal(bodySubst, relEnv)
  of rgCall:
    if rg.relName in relEnv:
      toGoal(relEnv[rg.relName], relEnv)
    else:
      raise newException(ValueError, "Unknown relation: " & rg.relName)
  of rgSetEq:
    setEqo(rg.cells, rg.values)
  of rgBranch:
    branchMostConstrained(rg.vars)

when isMainModule:
  echo "=== RelGoal prototype: relations as data ==="
  echo ""
  let xPlaceholder = ratom("__var_x")
  let g = rgFresh("x", rgEq(xPlaceholder, rint(5)))
  echo "RelGoal: ", g
  echo ""
  let goal = toGoal(g)
  let q = freshVar()
  let results = run(q, goal, 1)
  echo "Results: ", results.len
  if results.len > 0:
    echo "  ", results[0]
  echo ""
  echo "RelGoal as data works."
