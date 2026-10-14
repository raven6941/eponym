## relcompile.nim — Residual compiler (issue #35)
##
## Follow-up to issue #19's decision: the stageGoal-derived 1st projection
## of typeo is *correct* (9/9 differential agreement) but *slower* (0.49x)
## when interpreted via toGoal — per-call substAtom + closure-tree rebuild
## dominate the branch-pruning savings. This module compiles specialized
## RelGoal relations (SpecCtx.specs) to native Nim procs, removing the
## interpreter from the residual's hot path.
##
## Compilation scheme (per SpecCtx entry RelEntry(params, body)):
##   proc <specName>(p1..pn: RTerm): Goal = <compiled body>
## - rgEq/rgNeq  -> `==` / `=/=` on compiled terms
## - rgConj/rgDisj -> conj / disj
## - rgFresh(name, body) -> fresh(proc(rc_fK: RTerm): Goal = <body>)
##   (the fresh-binder placeholder __var_<name> becomes the proc param)
## - rgCall(name, args) -> direct proc call wrapped in a run-time thunk:
##     proc(rc_s: State): Stream = name(<args>)(rc_s)
##   The thunk preserves toGoal's lazy-expansion semantics: the callee's
##   proc body (goal-tree construction) runs when the goal runs, not when
##   it is built — so recursive calls cannot infinitely recurse at
##   goal-build time. Same laziness as the interpreted version, but no
##   relEnv lookup and no substAtom walk.
## - rgSetEq/rgBranch -> setEqo / branchMostConstrained
## - __var_<param> placeholders -> the proc's Nim params
## - ground terms -> ratom/rpair/rvar constructor expressions
##
## The specializer runs at compile time inside a Nim macro
## (staging-plan.md: "Generator = Nim macro"), so specialization +
## compilation is a single build step. See stagedTypeoProcs below.
##
## Requirements on the using module: import minikanren (Goal, State,
## Stream, RTerm, conj, disj, ==, =/=, fresh, setEqo, branchMostConstrained,
## ratom, rpair, rvar) and rel_elab if the entry template's static
## arguments need its constructors (e.g. natTy).

import macros
import staging/relgoal
import staging/stagegoal
import staging/modes
import staging/typeo_relgoal  # typeoData for the typeo driver macro (issue #85: data lives in src/, not tests/)
import rel_elab  # natTy for the static ty=nat specialization
import minikanren
import tables
import sets
import strutils
import algorithm

# --- Helpers for fail/succeed residuals (mirror toGoal) ---

proc rgFailGoal*(): Goal =
  proc(s: State): Stream = Stream(kind: skEmpty)

proc rgSucceedGoal*(): Goal =
  proc(s: State): Stream = Stream(kind: skCons, head: s,
                                 tail: Stream(kind: skEmpty))

# --- Compiler ---

type
  CCtx = object
    varEnv: Table[string, NimNode]  # "__var_tm" -> ident node
    freshCounter: int

proc compileTerm(t: RTerm, c: var CCtx): NimNode =
  case t.kind
  of rkVar:
    newCall(ident("rvar"), newLit(t.id))
  of rkAtom:
    if t.name.startsWith("__var_"):
      if t.name notin c.varEnv:
        error("relcompile: unmapped placeholder " & t.name &
              " (not a spec param nor an enclosing rgFresh binder)")
      c.varEnv[t.name]
    else:
      newCall(ident("ratom"), newLit(t.name))
  of rkPair:
    newCall(ident("rpair"), compileTerm(t.head, c), compileTerm(t.tail, c))

proc compileGoal(rg: RelGoal, c: var CCtx): NimNode =
  case rg.kind
  of rgFail:
    result = newCall(ident("rgFailGoal"))
  of rgSucceed:
    result = newCall(ident("rgSucceedGoal"))
  of rgEq:
    let a = compileTerm(rg.left, c)
    let b = compileTerm(rg.right, c)
    result = nnkInfix.newTree(ident("=="), a, b)
  of rgNeq:
    let a = compileTerm(rg.left, c)
    let b = compileTerm(rg.right, c)
    result = nnkInfix.newTree(ident("=/="), a, b)
  of rgConj:
    let l = compileGoal(rg.leftG, c)
    let r = compileGoal(rg.rightG, c)
    result = newCall(ident("conj"), l, r)
  of rgDisj:
    let l = compileGoal(rg.leftG, c)
    let r = compileGoal(rg.rightG, c)
    result = newCall(ident("disj"), l, r)
  of rgFresh:
    let f = ident("rc_f" & $c.freshCounter)
    inc c.freshCounter
    c.varEnv["__var_" & rg.varName] = f
    let b = compileGoal(rg.body, c)
    c.varEnv.del("__var_" & rg.varName)
    # fresh takes proc(x: RTerm): Goal {.closure.}; the anonymous proc
    # literal is a closure by default (same shape as staged_codegen.nim).
    result = quote do:
      fresh(proc(`f`: RTerm): Goal = `b`)
  of rgCall:
    var callNode = newCall(ident(rg.relName))
    for a in rg.args:
      callNode.add(compileTerm(a, c))
    let s = ident("rc_s")
    # Run-time thunk: build the callee's goal tree when the goal runs.
    result = quote do:
      proc(`s`: State): Stream = `callNode`(`s`)
  of rgSetEq:
    var cells = nnkBracket.newTree()
    for t in rg.cells: cells.add(compileTerm(t, c))
    var vals = nnkBracket.newTree()
    for t in rg.values: vals.add(compileTerm(t, c))
    result = quote do:
      setEqo(`cells`, `vals`)
  of rgBranch:
    var vars = nnkBracket.newTree()
    for t in rg.vars: vars.add(compileTerm(t, c))
    result = quote do:
      branchMostConstrained(`vars`)

proc checkCalls(rg: RelGoal, known: seq[string]) =
  ## Every rgCall target must be a compiled spec; a residual call to an
  ## *original* (unspecialized) relation has no proc to call. Fail at
  ## compile time with a clear message rather than emitting broken code.
  case rg.kind
  of rgCall:
    if rg.relName notin known:
      error("relcompile: residual calls unspecialized relation '" &
            rg.relName & "' (no compiled proc; fuel-exhausted or unknown?)")
  of rgConj, rgDisj:
    checkCalls(rg.leftG, known); checkCalls(rg.rightG, known)
  of rgFresh:
    checkCalls(rg.body, known)
  else: discard

proc fwdDecl(name: string, e: RelEntry): NimNode =
  ## Forward declaration so (mutually) recursive specs typecheck
  ## regardless of emission order.
  var params = nnkFormalParams.newTree(ident("Goal"))
  for p in e.params:
    params.add(newIdentDefs(ident(p), ident("RTerm")))
  # ProcDef shape (7 children): name, genericParams, pattern, formalParams,
  # pragmas, <extra>, body. Empty body = forward declaration.
  nnkProcDef.newTree(ident(name), newEmptyNode(), newEmptyNode(),
                     params, newEmptyNode(), newEmptyNode(), newEmptyNode())

proc procDef(name: string, e: RelEntry): NimNode =
  var c = CCtx(varEnv: initTable[string, NimNode](), freshCounter: 0)
  var pnodes: seq[NimNode] = @[ident("Goal")]
  for p in e.params:
    let id = ident(p)
    c.varEnv["__var_" & p] = id
    pnodes.add(newIdentDefs(id, ident("RTerm")))
  let body = compileGoal(e.body, c)
  newProc(ident(name), pnodes, newStmtList(body))

proc compileSpecCtx*(spCtx: SpecCtx): NimNode =
  ## Compile every specialized relation in spCtx to a Nim proc.
  ## Returns a stmtList: forward decls, then definitions.
  var names: seq[string] = @[]
  for name in spCtx.specs.keys: names.add(name)
  names.sort()
  for name in names:
    checkCalls(spCtx.specs[name].body, names)
  result = newStmtList()
  for name in names:
    result.add(fwdDecl(name, spCtx.specs[name]))
  for name in names:
    result.add(procDef(name, spCtx.specs[name]))

# --- Driver macro: specialize + compile typeo at compile time ---

macro stagedTypeoProcs*(): untyped =
  ## Specialize typeo(tm, nat, ctx) at compile time (Nim VM) and emit one
  ## Nim proc per specialized relation, plus a `stagedTypeo(tm, ctx)`
  ## template naming the top-level checker. Single build step: the using
  ## module just calls stagedTypeoProcs() then stagedTypeo(tm, ctx).
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mIn, mIn], body: typeoData())
  var spCtx = newSpecCtx(relEnv, fuel = 8)
  var staticParams = initTable[string, RTerm]()
  staticParams["ty"] = natTy()
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")
  let top = specializeRelation(spCtx, "typeo", staticParams, dynamicVars)
  result = compileSpecCtx(spCtx)
  let topIdent = ident(top)
  # Entry template (manual AST: quote would gensym the template name).
  result.add(nnkTemplateDef.newTree(
    ident("stagedTypeo"), newEmptyNode(), newEmptyNode(),
    nnkFormalParams.newTree(ident("Goal"),
      newIdentDefs(ident("tm"), ident("RTerm")),
      newIdentDefs(ident("ctx"), ident("RTerm"))),
    newEmptyNode(), newEmptyNode(),
    newStmtList(newCall(topIdent, ident("tm"),
                        newCall(ident("natTy")), ident("ctx")))))
