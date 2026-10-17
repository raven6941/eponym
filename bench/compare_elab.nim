## Comparison harness: direct elaborator vs relational elaborator
##
## Tests both elaborators on the same fragment and compares accept/reject.
## Fragment: Pi (non-dep), lam, app, Nat, Vec, vars.
##
## The direct elaborator (elab.nim) handles the full language; we restrict
## test cases to the fragment. The relational elaborator (rel_elab_dep.nim)
## handles only the fragment.

import minikanren
import rel_elab_dep
import elab  # direct elaborator

type
  TestCase = object
    name: string
    # Eponym surface syntax for direct elaborator
    src: string
    # RTerm encoding for relational elaborator
    # (tm, expected ty, should succeed?)
    tm: RTerm
    ty: RTerm
    shouldSucceed: bool

proc rnilCtx(): RTerm = rnil()

# --- Test corpus ------------------------------------------------------------

proc corpus*(): seq[TestCase] =
  result = @[]
  # 1. zero : Nat
  result.add(TestCase(
    name: "zero : Nat",
    src: "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\nproc t : Nat =\n  zero\n",
    tm: zeroTm(),
    ty: natTy(),
    shouldSucceed: true
  ))
  # 2. suc(zero) : Nat
  result.add(TestCase(
    name: "suc(zero) : Nat",
    src: "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\nproc t : Nat =\n  suc zero\n",
    tm: sucTm(zeroTm()),
    ty: natTy(),
    shouldSucceed: true
  ))
  # 3. lam(x.x) : Pi(Nat,Nat)
  result.add(TestCase(
    name: "lam(x.x) : Pi(Nat,Nat)",
    src: "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\nproc t : Nat -> Nat =\n  lam (x : Nat). x\n",
    tm: lamTm(varTm(0)),
    ty: piTy(natTy(), natTy()),
    shouldSucceed: true
  ))
  # 4. (lam x.x) zero : Nat
  result.add(TestCase(
    name: "(lam x.x) zero : Nat",
    src: "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\nproc t : Nat =\n  (lam (x : Nat). x) zero\n",
    tm: appTm(lamTm(varTm(0)), zeroTm()),
    ty: natTy(),
    shouldSucceed: true
  ))
  # 5. nil : Vec(Nat, zero)
  result.add(TestCase(
    name: "nil : Vec(Nat,zero)",
    src: "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\ndata Vec (A : Type 0) : Nat -> Type 0 where\n| nil : Vec A zero\n| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)\nproc t : Vec Nat zero =\n  nil Nat\n",
    tm: nilTm(),
    ty: vecTy(natTy(), zeroTm()),
    shouldSucceed: true
  ))
  # 6. cons(zero, nil) : Vec(Nat, suc(zero))
  result.add(TestCase(
    name: "cons(zero,nil) : Vec(Nat,suc(zero))",
    src: "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\ndata Vec (A : Type 0) : Nat -> Type 0 where\n| nil : Vec A zero\n| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)\nproc t : Vec Nat (suc zero) =\n  cons Nat zero zero (nil Nat)\n",
    tm: consTm(zeroTm(), nilTm()),
    ty: vecTy(natTy(), sucTm(zeroTm())),
    shouldSucceed: true
  ))
  # 7. REJECT: zero : Vec(Nat,zero)  (wrong type)
  result.add(TestCase(
    name: "REJECT zero : Vec(Nat,zero)",
    src: "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\ndata Vec (A : Type 0) : Nat -> Type 0 where\n| nil : Vec A zero\n| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)\nproc t : Vec Nat zero =\n  zero\n",
    tm: zeroTm(),
    ty: vecTy(natTy(), zeroTm()),
    shouldSucceed: false
  ))
  # 8. REJECT: nil : Vec(Nat, suc(zero))  (wrong index)
  result.add(TestCase(
    name: "REJECT nil : Vec(Nat,suc(zero))",
    src: "data Nat : Type 0 where\n| zero : Nat\n| suc (n : Nat) : Nat\ndata Vec (A : Type 0) : Nat -> Type 0 where\n| nil : Vec A zero\n| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)\nproc t : Vec Nat (suc zero) =\n  nil Nat\n",
    tm: nilTm(),
    ty: vecTy(natTy(), sucTm(zeroTm())),
    shouldSucceed: false
  ))

# --- Comparison -------------------------------------------------------------

proc testDirect(tc: TestCase): bool =
  ## Returns true if direct elaborator accepts.
  try:
    discard elabCheck(tc.src)
    return true
  except ElabError:
    return false

proc testRelational(tc: TestCase): bool =
  ## Returns true if relational elaborator accepts.
  ## Uses checko (tm against ty).
  let g = checko(tc.tm, tc.ty, rnilCtx())
  let res = run(freshVar(), g, 1)
  return res.len > 0

proc compareAll*() =
  var directOk = 0
  var relOk = 0
  var mismatches: seq[string] = @[]
  for tc in corpus():
    let d = testDirect(tc)
    let r = testRelational(tc)
    let dExp = tc.shouldSucceed
    # Check direct matches expectation
    if d != dExp:
      echo "DIRECT MISMATCH (vs expected): ", tc.name,
           " got ", d, " expected ", dExp
    # Check relational matches expectation
    if r != dExp:
      echo "RELATIONAL MISMATCH (vs expected): ", tc.name,
           " got ", r, " expected ", dExp
    # Check they agree with each other
    if d == r:
      inc directOk  # both agree
    else:
      mismatches.add(tc.name & ": direct=" & $d & " relational=" & $r)
    if d == dExp and r == dExp:
      inc relOk
  echo "=== Comparison ==="
  echo "Cases where both agree: ", directOk, "/", corpus().len
  echo "Cases where both match expected: ", relOk, "/", corpus().len
  if mismatches.len > 0:
    echo "Mismatches (direct vs relational):"
    for m in mismatches: echo "  ", m
  else:
    echo "No direct-vs-relational mismatches!"

when isMainModule:
  compareAll()
