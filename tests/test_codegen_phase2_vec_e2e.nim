## End-to-end wrapper test for the Phase 2 representation backend
## (Issue #330 v3: `Vec` as `seq[int]`).
##
## A separate file from `test_codegen_phase2_vec.nim`: both elaborate a
## `vecElim`, and each elaboration emits `eponymElim_vecElim`, so they cannot
## share a module. This file checks the typed wrapper path (`eponymBlock`):
## a `Vec`-typed wrapper must reroute through the repr proc
## (`eponymCompiledRepr_wVMapDouble`) via the identity boundary, and must
## preserve the entry length check.
##
## Call-form lambdas are used: the command-form `lam (v : Vec Int i). ...`
## does not survive blockToEponym's command-lambda converter (the established
## `lam(binder: type) => body` call form comes from test_embedded_macro_forms).
## `vecnil` is the eponymBlock spelling of the `nil` constructor (`nil` is a
## Nim keyword); explicit type/index args use square brackets.

import std/sequtils
import eponym_mac

eponymBlock:
  import "../lib/nat.ep"
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeVector(Vec)
  proc wVMapDouble(n: Nat, xs: Vec[Int, n]): Vec[Int, n] = vecElim[Int](lam(i: Nat) => lam(v: Vec[Int, i]) => Vec[Int, i], vecnil[Int](), lam(i: Nat) => lam(x: Int) => lam(xs2: Vec[Int, i]) => lam(ih: Vec[Int, i]) => cons[Int, i](addInt(x, x), ih), n, xs)

proc expect(ok: bool, message: string) =
  if not ok:
    quit("FAIL: " & message, 1)
  echo "ok: ", message

when isMainModule:
  for xs in [@[], @[5], @[1, 2, 3, 4]]:
    expect(wVMapDouble(xs.len, xs) == xs.mapIt(it * 2),
      "e2e wrapper wVMapDouble on " & $xs)
  var raised = false
  try:
    discard wVMapDouble(2, @[1, 2, 3])
  except ValueError:
    raised = true
  expect(raised, "e2e wrapper preserves the Vec entry check")
  echo "all Phase 2 Vec end-to-end wrapper checks passed"
