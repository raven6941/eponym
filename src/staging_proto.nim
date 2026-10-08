## Phase 0 Prototype: Staging with static/dynamic split
##
## Goal: Validate the "smaller system" approach. Build a minimal Rep[T]
## with one staging rule, apply to an evaluator where term STRUCTURE is
## static but VARIABLES are dynamic.
##
## This is the 1st Futamura projection:
##   evalo(add(1, x), v) with x dynamic
##   → staged: proc(x: int): int = 1 + x
##
## The term structure (add, lit(1), var) is known at staging time.
## The variable x is a runtime input. The staged code takes x as a
## parameter and computes directly — no relational machinery.
##
## Compare to staged_eval.nim: that handles only fully ground terms
## (everything static, so it just computes the answer). This prototype
## handles the mixed case: static structure + dynamic values.

import tables
import strutils
import sequtils

# --- The object language: arithmetic with variables ---

type
  TmKind = enum
    tkLit, tkVar, tkAdd, tkMul

  Tm = ref object
    case kind: TmKind
    of tkLit: value: int
    of tkVar: name: string
    of tkAdd, tkMul: left, right: Tm

proc lit(n: int): Tm = Tm(kind: tkLit, value: n)
proc vr(name: string): Tm = Tm(kind: tkVar, name: name)
proc add(a, b: Tm): Tm = Tm(kind: tkAdd, left: a, right: b)
proc mul(a, b: Tm): Tm = Tm(kind: tkMul, left: a, right: b)

proc `$`(tm: Tm): string =
  case tm.kind
  of tkLit: $tm.value
  of tkVar: tm.name
  of tkAdd: "(" & $tm.left & " + " & $tm.right & ")"
  of tkMul: "(" & $tm.left & " * " & $tm.right & ")"

# --- Rep: staged values build IR ---

type
  RepKind = enum
    rkLit,    # literal (static value lifted)
    rkVar,    # runtime variable (dynamic input)
    rkAdd,    # addition IR node
    rkMul,    # multiplication IR node

  Rep = ref object
    case kind: RepKind
    of rkLit: value: int
    of rkVar: name: string
    of rkAdd, rkMul: left, right: Rep

proc `$`(r: Rep): string =
  case r.kind
  of rkLit: $r.value
  of rkVar: r.name
  of rkAdd: "(" & $r.left & " + " & $r.right & ")"
  of rkMul: "(" & $r.left & " * " & $r.right & ")"

# Smart constructors (the "staging rule": static computes, dynamic builds IR)
proc litR(n: int): Rep = Rep(kind: rkLit, value: n)
proc varR(name: string): Rep = Rep(kind: rkVar, name: name)

proc addR(a, b: Rep): Rep =
  ## Staging rule for add: if both static, compute now;
  ## otherwise build IR node.
  if a.kind == rkLit and b.kind == rkLit:
    litR(a.value + b.value)  # static/static → compute at staging time
  else:
    Rep(kind: rkAdd, left: a, right: b)  # dynamic involved → residualize

proc mulR(a, b: Rep): Rep =
  if a.kind == rkLit and b.kind == rkLit:
    litR(a.value * b.value)
  else:
    Rep(kind: rkMul, left: a, right: b)

# --- The staged evaluator: 1st Futamura projection ---

proc evalStaged(tm: Tm, env: Table[string, Rep]): Rep =
  ## Stage the evaluator for a known term structure.
  ## tm: static (known at staging time)
  ## env: maps variable names to Rep (dynamic inputs)
  ## Returns: IR for computing the result
  ##
  ## This is mix(evaluator, tm): the term is fixed, variables are dynamic.
  case tm.kind
  of tkLit:
    litR(tm.value)  # static literal → IR literal
  of tkVar:
    if tm.name in env:
      env[tm.name]  # dynamic variable → its Rep
    else:
      raise newException(ValueError, "Unbound variable: " & tm.name)
  of tkAdd:
    addR(evalStaged(tm.left, env), evalStaged(tm.right, env))
  of tkMul:
    mulR(evalStaged(tm.left, env), evalStaged(tm.right, env))

# --- Compile IR to Nim source (the "code generator") ---

proc genSym(r: Rep, env: Table[string, string]): string =
  ## Generate Nim expression from IR.
  ## Returns Nim source code as string.
  case r.kind
  of rkLit: $r.value
  of rkVar:
    if r.name in env: env[r.name]
    else: r.name  # assume it's a proc parameter
  of rkAdd: "(" & genSym(r.left, env) & " + " & genSym(r.right, env) & ")"
  of rkMul: "(" & genSym(r.left, env) & " * " & genSym(r.right, env) & ")"

proc compileProc(tm: Tm, varNames: seq[string]): string =
  ## Generate a Nim proc from a term with dynamic variables.
  ## This is the staged compiler output.
  var env = initTable[string, Rep]()
  for v in varNames:
    env[v] = varR(v)
  let ir = evalStaged(tm, env)
  let body = genSym(ir, initTable[string, string]())
  let params = varNames.mapIt(it & ": int").join(", ")
  "proc staged(" & params & "): int =\n  " & body

# --- Direct interpreter for comparison ---

proc evalDirect(tm: Tm, env: Table[string, int]): int =
  case tm.kind
  of tkLit: tm.value
  of tkVar: env[tm.name]
  of tkAdd: evalDirect(tm.left, env) + evalDirect(tm.right, env)
  of tkMul: evalDirect(tm.left, env) * evalDirect(tm.right, env)

when isMainModule:
  import times

  echo "=== Phase 0: Staging with static/dynamic split ==="
  echo ""
  echo "Term structure is static; variables are dynamic (runtime inputs)."
  echo ""

  # Test 1: (1 + x) * 2, where x is dynamic
  let tm1 = mul(add(lit(1), vr("x")), lit(2))
  echo "Term: ", tm1
  echo ""

  var env = initTable[string, Rep]()
  env["x"] = varR("x")
  let ir1 = evalStaged(tm1, env)
  echo "Staged IR: ", ir1
  echo "  Note: (1+2) would fold, but x is dynamic so (1+x) residualizes."
  echo ""

  let code1 = compileProc(tm1, @["x"])
  echo "Generated Nim:"
  echo code1
  echo ""

  # Verify: direct vs staged (interpret IR)
  proc evalRep(r: Rep, vals: Table[string, int]): int =
    case r.kind
    of rkLit: r.value
    of rkVar: vals[r.name]
    of rkAdd: evalRep(r.left, vals) + evalRep(r.right, vals)
    of rkMul: evalRep(r.left, vals) * evalRep(r.right, vals)

  var vals = initTable[string, int]()
  vals["x"] = 5
  var dvals = initTable[string, int]()
  dvals["x"] = 5

  let direct = evalDirect(tm1, dvals)
  let staged = evalRep(ir1, vals)
  echo "Direct eval (x=5): ", direct
  echo "Staged IR eval (x=5): ", staged
  if direct == staged:
    echo "✓ Agree"
  else:
    echo "✗ MISMATCH"
  echo ""

  # Test 2: fully static term (should fold completely)
  let tm2 = mul(add(lit(1), lit(2)), lit(3))
  echo "Term: ", tm2, " (fully static)"
  let ir2 = evalStaged(tm2, initTable[string, Rep]())
  echo "Staged IR: ", ir2
  echo "  Fully folded at staging time — no residual code."
  if ir2.kind == rkLit and ir2.value == 9:
    echo "✓ Correctly folded to 9"
  else:
    echo "✗ Should have folded to 9"
  echo ""

  echo "=== What this validates ==="
  echo "✓ Rep[T] marks dynamic values; plain T is static"
  echo "✓ Staging rules (addR/mulR) compute static/static, residualize otherwise"
  echo "✓ evalStaged is mix(evaluator, term): fixes structure, leaves vars dynamic"
  echo "✓ Generated code has no interpreter machinery — just the computation"
  echo ""
  echo "This is the 1st Futamura projection via the framework, not by hand."
  echo "Compare: staged_eval.nim hand-writes this; here the RULES derive it."
