## LMS-style staging via Sym[R]
##
## Lightweight Modular Staging: write the program once, polymorphically
## over the representation type R. Instantiate R with:
## - A direct value type → the program executes
## - A Rep (staged) type → the program builds IR
##
## This is LMS in the style of Rompf: staging driven by types, not by
## explicit brackets (that's MetaML). The same `prog` text yields both
## an interpreter and a compiler, selected by the type parameter.
##
## Compare with our hand-staged versions (staged_eval.nim, etc.):
## - Hand-staged: write the staged version manually, separately
## - LMS-style: write once, get both by instantiating R differently

# Note: ett.nim has Sym[R] for the full ETT language, but this demo
# uses a minimal ArithSym to keep the LMS pattern clear.

# --- The Rep type: staged computations build IR ---

type
  RepKind = enum
    rkLit,      # literal integer
    rkAdd,      # addition node
    rkMul,      # multiplication node

  Rep = ref object
    case kind: RepKind
    of rkLit: value: int
    of rkAdd, rkMul: left, right: Rep

proc `$`(r: Rep): string =
  case r.kind
  of rkLit: $r.value
  of rkAdd: "(" & $r.left & " + " & $r.right & ")"
  of rkMul: "(" & $r.left & " * " & $r.right & ")"

# Actually, Sym[R] in ett.nim is for the full ETT language.
# For this LMS demo, let's define a smaller arithmetic language
# to keep the staging clear.

type
  ArithSym[R] = object
    lit*: proc(n: int): R
    add*: proc(a, b: R): R
    mul*: proc(a, b: R): R

# Direct instance: R = int (execute immediately)
proc directArith(): ArithSym[int] =
  ArithSym[int](
    lit: proc(n: int): int = n,
    add: proc(a, b: int): int = a + b,
    mul: proc(a, b: int): int = a * b,
  )

# Staged instance: R = Rep (build IR)
proc stagedArith(): ArithSym[Rep] =
  ArithSym[Rep](
    lit: proc(n: int): Rep = Rep(kind: rkLit, value: n),
    add: proc(a, b: Rep): Rep = Rep(kind: rkAdd, left: a, right: b),
    mul: proc(a, b: Rep): Rep = Rep(kind: rkMul, left: a, right: b),
  )

# --- The program: written once, polymorphically ---

proc prog[R](s: ArithSym[R]): R =
  ## (1 + 2) * 3 — the same text, staged or not based on R
  s.mul(s.add(s.lit(1), s.lit(2)), s.lit(3))

# --- Compile IR to efficient code ---

proc compile(r: Rep): int =
  ## The "compiler": IR → efficient execution.
  ## In real LMS this would generate machine code or Nim source;
  ## here we just interpret the IR directly (it's already optimal:
  ## no search, no dispatch overhead beyond the IR structure).
  case r.kind
  of rkLit: r.value
  of rkAdd: compile(r.left) + compile(r.right)
  of rkMul: compile(r.left) * compile(r.right)

# --- Constant folding: optimize at staging time ---

proc fold(r: Rep): Rep =
  ## Partial evaluation on the IR: fold constants during staging.
  ## This is where LMS shines — the staged program is optimized
  ## *before* runtime.
  case r.kind
  of rkLit: r
  of rkAdd:
    let l = fold(r.left)
    let r2 = fold(r.right)
    if l.kind == rkLit and r2.kind == rkLit:
      Rep(kind: rkLit, value: l.value + r2.value)
    else:
      Rep(kind: rkAdd, left: l, right: r2)
  of rkMul:
    let l = fold(r.left)
    let r2 = fold(r.right)
    if l.kind == rkLit and r2.kind == rkLit:
      Rep(kind: rkLit, value: l.value * r2.value)
    else:
      Rep(kind: rkMul, left: l, right: r2)

when isMainModule:
  import times
  
  echo "=== LMS-style staging: same program, different R ==="
  echo ""
  
  # Direct: R = int
  let direct = directArith()
  let start1 = cpuTime()
  let v1 = prog(direct)
  let t1 = cpuTime() - start1
  echo "Direct (R=int): ", v1, " in ", t1*1000, "ms"
  echo "  The program executed immediately."
  echo ""
  
  # Staged: R = Rep (build IR)
  let staged = stagedArith()
  let start2 = cpuTime()
  let ir = prog(staged)
  let t2 = cpuTime() - start2
  echo "Staged (R=Rep): IR = ", ir, " built in ", t2*1000, "ms"
  echo "  The program built IR instead of executing."
  echo ""
  
  # Compile and run the IR
  let start3 = cpuTime()
  let v2 = compile(ir)
  let t3 = cpuTime() - start3
  echo "Compiled IR: ", v2, " in ", t3*1000, "ms"
  echo ""
  
  # With constant folding at staging time
  let folded = fold(ir)
  echo "Folded IR: ", folded
  let v3 = compile(folded)
  echo "Folded result: ", v3
  echo ""
  
  echo "Key LMS idea: `prog` is written once. The type R selects"
  echo "whether it executes (R=int) or builds optimizable IR (R=Rep)."
  echo "No separate hand-staged version needed."
