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
#
# Capture-avoiding: rgFresh binders are respected.
# - If the binder shadows the placeholder (__var_<name> matches), the
#   substitution stops at the binder (occurrences inside belong to it).
# - If the replacement mentions the binder's placeholder, the binder is
#   freshened first. Without this, inlining a recursive call (issue #20)
#   merges the caller's argument variables with the callee's fresh
#   variables of the same name, e.g. typeo's outer `n` with the inlined
#   body's inner `n`, producing bogus self-referential residuals like
#   (n == suc(n)) that reject valid programs.

var substFreshCounter = 0

proc freshBinderName(base: string): string =
  inc substFreshCounter
  base & "$" & $substFreshCounter

proc termMentionsPH(t: RTerm, name: string): bool =
  case t.kind
  of rkAtom: t.name == name
  of rkPair: termMentionsPH(t.head, name) or termMentionsPH(t.tail, name)
  of rkVar: false

proc rgMentionsPH*(rg: RelGoal, name: string): bool =
  ## Does the placeholder atom `name` (e.g. "__var_tm") occur free in rg?
  ## Used to skip no-op substitutions when instantiating specialized calls.
  case rg.kind
  of rgFail, rgSucceed: false
  of rgEq, rgNeq: termMentionsPH(rg.left, name) or termMentionsPH(rg.right, name)
  of rgConj, rgDisj:
    rgMentionsPH(rg.leftG, name) or rgMentionsPH(rg.rightG, name)
  of rgFresh:
    if "__var_" & rg.varName == name: false  # shadowed by inner binder
    else: rgMentionsPH(rg.body, name)
  of rgCall: rg.args.anyIt(termMentionsPH(it, name))
  of rgSetEq:
    rg.cells.anyIt(termMentionsPH(it, name)) or
      rg.values.anyIt(termMentionsPH(it, name))
  of rgBranch: rg.vars.anyIt(termMentionsPH(it, name))

proc substTermAtom(t: RTerm, placeholder: RTerm, replacement: RTerm): RTerm =
  if t.kind == rkAtom and t.name == placeholder.name:
    replacement
  elif t.kind == rkPair:
    rpair(substTermAtom(t.head, placeholder, replacement),
          substTermAtom(t.tail, placeholder, replacement))
  else:
    t

proc renameBoundTerm(t: RTerm, oldName, newName: string): RTerm =
  if t.kind == rkAtom and t.name == "__var_" & oldName:
    ratom("__var_" & newName)
  elif t.kind == rkPair:
    rpair(renameBoundTerm(t.head, oldName, newName),
          renameBoundTerm(t.tail, oldName, newName))
  else:
    t

proc renameBound(rg: RelGoal, oldName, newName: string): RelGoal =
  ## Rename __var_<oldName> occurrences bound by the current binder.
  ## Stops at a shadowing inner binder of the same name.
  case rg.kind
  of rgFail, rgSucceed: rg
  of rgEq: rgEq(renameBoundTerm(rg.left, oldName, newName),
                renameBoundTerm(rg.right, oldName, newName))
  of rgNeq: rgNeq(renameBoundTerm(rg.left, oldName, newName),
                  renameBoundTerm(rg.right, oldName, newName))
  of rgConj: rgConj(renameBound(rg.leftG, oldName, newName),
                    renameBound(rg.rightG, oldName, newName))
  of rgDisj: rgDisj(renameBound(rg.leftG, oldName, newName),
                    renameBound(rg.rightG, oldName, newName))
  of rgFresh:
    if rg.varName == oldName: rg  # shadowed: inner binder owns these
    else: rgFresh(rg.varName, renameBound(rg.body, oldName, newName))
  of rgCall:
    rgCall(rg.relName, rg.args.mapIt(renameBoundTerm(it, oldName, newName)))
  of rgSetEq:
    RelGoal(kind: rgSetEq,
            cells: rg.cells.mapIt(renameBoundTerm(it, oldName, newName)),
            values: rg.values.mapIt(renameBoundTerm(it, oldName, newName)))
  of rgBranch:
    RelGoal(kind: rgBranch,
            vars: rg.vars.mapIt(renameBoundTerm(it, oldName, newName)))

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
    let boundPH = "__var_" & rg.varName
    if boundPH == placeholder.name:
      rg  # binder shadows the placeholder: substitution stops here
    elif termMentionsPH(replacement, boundPH):
      # Replacement would be captured by this binder: freshen it first.
      let newName = freshBinderName(rg.varName)
      rgFresh(newName, substAtom(renameBound(rg.body, rg.varName, newName),
                                 placeholder, replacement))
    else:
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

type
  RelEntry* = object
    ## A (possibly specialized) relation definition for the data-driven
    ## interpreter: param names + body using __var_<param> placeholders.
    params*: seq[string]
    body*: RelGoal

proc toGoal*(rg: RelGoal, relEnv: Table[string, RelEntry] = initTable[string, RelEntry]()): Goal =
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
      let e = relEnv[rg.relName]
      if e.params.len == rg.args.len:
        # LAZY expansion: substitute args and interpret one level when
        # the goal *runs*, not when it is built. Eager expansion would
        # diverge on recursive relations (interpreting the body requires
        # interpreting the recursive call inside it, ad infinitum).
        # Capture-avoiding: substAtom freshens binders the args would
        # otherwise be captured by (e.g. a recursive call's rgFresh("n")
        # vs the caller's __var_n).
        let args = rg.args
        let entry = e
        let renv = relEnv
        return proc(s: State): Stream =
          var inst = entry.body
          for i, p in entry.params:
            # Skip params that don't occur: substAtom walks the whole
            # body, so a no-op substitution is pure overhead at every
            # recursive call (e.g. __var_ty never occurs in typeo_s0).
            let ph = ratom("__var_" & p)
            if rgMentionsPH(inst, ph.name):
              inst = substAtom(inst, ph, args[i])
          toGoal(inst, renv)(s)
      else:
        raise newException(ValueError,
          "arity mismatch for relation " & rg.relName & ": expected " &
          $e.params.len & " args, got " & $rg.args.len)
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
