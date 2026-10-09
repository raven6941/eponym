## Framework validation: arithmetic DSL via Layer 1
##
## Proves the framework is generic (not tied to Phase 0's specific Rep).
## Builds a fresh arithmetic DSL using only framework primitives:
## Rep[T], IRNode, lift, dynamic, smartOp.
##
## Acceptance (from #16): framework stages a non-ETT, non-relational toy.

import staging/framework

# --- DSL-specific IR nodes (extend IRNode) ---

type
  ArithNodeKind = enum akAdd, akMul, akVar

  ArithNode = ref object of IRNode
    case kind: ArithNodeKind
    of akVar: varName: string
    of akAdd, akMul: left, right: Rep[int]

proc `$`(n: ArithNode): string =
  # Forward declaration: Rep[int] $ defined below
  case n.kind
  of akVar: n.varName
  of akAdd, akMul: "(...)"  # placeholder, full def after Rep $

proc `$`(r: Rep[int]): string =
  if r.isStatic: "static(" & $r.staticVal & ")"
  else:
    let n = ArithNode(r.node)
    case n.kind
    of akVar: "dynamic(" & n.varName & ")"
    of akAdd: "dynamic((" & $n.left & " + " & $n.right & "))"
    of akMul: "dynamic((" & $n.left & " * " & $n.right & "))"

# --- DSL smart constructors via framework smartOp ---

proc addNode(a, b: Rep[int]): ArithNode =
  ArithNode(kind: akAdd, left: a, right: b)

proc mulNode(a, b: Rep[int]): ArithNode =
  ArithNode(kind: akMul, left: a, right: b)

proc varNode(name: string): ArithNode =
  ArithNode(kind: akVar, varName: name)

proc addR(a, b: Rep[int]): Rep[int] =
  smartOp[int](a, b,
    proc(x, y: int): int = x + y,
    proc(x, y: Rep[int]): IRNode = addNode(x, y))

proc mulR(a, b: Rep[int]): Rep[int] =
  smartOp[int](a, b,
    proc(x, y: int): int = x * y,
    proc(x, y: Rep[int]): IRNode = mulNode(x, y))

proc varR(name: string): Rep[int] =
  dynamic[int](varNode(name))

# --- Tagless-final DSL ---

type
  ArithSym[R] = object
    lit*: proc(n: int): R
    vr*: proc(name: string): R
    add*: proc(a, b: R): R
    mul*: proc(a, b: R): R

proc directArith(): ArithSym[int] =
  ArithSym[int](
    lit: proc(n: int): int = n,
    vr: proc(name: string): int = raise newException(ValueError, "unbound: " & name),
    add: proc(a, b: int): int = a + b,
    mul: proc(a, b: int): int = a * b,
  )

proc stagedArith(): ArithSym[Rep[int]] =
  ArithSym[Rep[int]](
    lit: proc(n: int): Rep[int] = lift(n),
    vr: proc(name: string): Rep[int] = varR(name),
    add: addR,
    mul: mulR,
  )

# --- Test programs ---

proc prog1[R](s: ArithSym[R]): R =
  ## (1 + 2) * 3 — fully static, should fold
  s.mul(s.add(s.lit(1), s.lit(2)), s.lit(3))

proc prog2[R](s: ArithSym[R]): R =
  ## (x + 1) * 2 — x dynamic, should residualize
  s.mul(s.add(s.vr("x"), s.lit(1)), s.lit(2))

when isMainModule:
  echo "=== Layer 1 validation: generic arithmetic DSL ==="
  echo ""

  # Direct execution
  let d = directArith()
  echo "Direct prog1: ", prog1(d), " (expected 9)"
  echo ""

  # Staged: fully static should fold
  let s = stagedArith()
  let r1 = prog1(s)
  echo "Staged prog1: ", r1
  if r1.isStatic and r1.staticVal == 9:
    echo "✓ Fully static folded to 9 at staging time"
  else:
    echo "✗ Should have folded"
  echo ""

  # Staged: dynamic var should residualize
  let r2 = prog2(s)
  echo "Staged prog2: ", r2
  if not r2.isStatic:
    echo "✓ Dynamic variable residualized to IR"
  else:
    echo "✗ Should have residualized"
  echo ""

  echo "=== Framework is generic ==="
  echo "This DSL uses only: Rep[T], IRNode, lift, dynamic, smartOp."
  echo "No ETT, no relations, no Phase-0-specific code."
  echo "Any tagless-final DSL can plug in the same way."
