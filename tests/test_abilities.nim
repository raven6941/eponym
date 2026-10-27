## Issue #177: ambient abilities (Frank-style) threaded through
## bidirectional elaboration — prototype acceptance tests.
##
## - Pure programs elaborate with zero annotations (opt-in promise).
## - Commands elaborate under a matching peg; wrong pegs and unhandled
##   commands are rejected with precise errors.
## - Frank's `bad` example (unannotated peg, effectful body) is rejected.
## - Signatures freshen one ?aN each (implicit effect polymorphism):
##   a pure operator instantiates under any ambient.
## - Unknown interfaces in pegs / commands are rejected at declaration.

import strutils
import parse_surf  # ParseError
import elab

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

proc elaborates(src: string): bool =
  try:
    discard elabCheck(src)
    true
  except ElabError as e:
    echo "  unexpected ElabError: ", e.msg
    false
  except ParseError as e:
    echo "  unexpected ParseError: ", e.msg
    false

proc rejects(src: string, frag: string): bool =
  ## Must raise ElabError whose message contains `frag`.
  try:
    discard elabCheck(src)
    echo "  unexpectedly elaborated"
    false
  except ElabError as e:
    if frag in e.msg: true
    else:
      echo "  wrong error message: ", e.msg
      false

const prelude = """
interface Console
postulate(String, Univ)
postulate(msg, String)
command send : String -> unitTy in Console
"""

# --- pure programs: zero annotations ---------------------------------------
check(elaborates("""
proc id (A : Univ) (x : A) : A = x
proc twice (A : Univ) (f : A -> A) (x : A) : A = f (f x)
proc constFn (A : Univ) (B : Univ) (x : A) (y : B) : A = x
"""), "pure programs elaborate with no ability annotations")

# --- command under a matching peg -------------------------------------------
check(elaborates(prelude & """
proc puts : [Console] unitTy = send msg
"""), "command elaborates under a matching peg")

# --- Frank's `bad`: unannotated peg + effectful body -------------------------
check(rejects(prelude & """
proc bad : unitTy = send msg
""", "stuck on [?a"), "Frank's `bad` is rejected (stuck on the signature ?aN)")

# --- wrong peg at use ---------------------------------------------------------
check(rejects(prelude & """
proc puts : [Console] unitTy = send msg
proc pureUse : unitTy = puts
""", "ability mismatch"), "using a [Console] operator in a pure ambient is rejected")

# --- unhandled command ----------------------------------------------------------
check(rejects(prelude & """
proc noPeg : unitTy = send msg
""", "not yet known"), "command with no interface in the ambient is rejected")

# --- implicit effect polymorphism: pure operator under [Console] ---------------
check(elaborates(prelude & """
proc puts : [Console] unitTy = send msg
proc id (A : Univ) (x : A) : A = x
proc useBoth : [Console] unitTy = id unitTy puts
"""), "pure operator instantiates under [Console] (per-use freshening)")

# --- explicit [] : pure operator, usable in a [] ambient ----------------------
check(elaborates(prelude & """
proc pid : [] unitTy -> unitTy = lam(x: unitTy) => x
proc usePure : [] unitTy = pid unitv
"""), "explicit [] operator works in a [] ambient")

# --- explicit [] under an open ambient: Frank-strict rejection -------------------
check(rejects(prelude & """
proc pid : [] unitTy -> unitTy = lam(x: unitTy) => x
proc poly (A : Univ) (x : A) : A = pid x
""", "ability mismatch"), "[] operator under a polymorphic ambient is rejected (no subeffecting)")

# --- unknown interface in a peg ---------------------------------------------------
check(rejects("""
interface Console
proc p : [Consle] unitTy = unitv
""", "unknown interface"), "unknown interface in a peg is rejected")

# --- command of an undeclared interface -------------------------------------------
check(rejects("""
command send : unitTy -> unitTy in Console
""", "unknown interface"), "command of an undeclared interface is rejected")

# --- duplicate interface --------------------------------------------------------------
check(rejects("""
interface Console
interface Console
""", "duplicate declaration"), "duplicate interface is rejected")

# --- interface used as a term -----------------------------------------------------------
check(rejects("""
interface Console
proc p : unitTy = Console
""", "not a term"), "interface used as a term is rejected")

# --- shadowing order: rightmost interface wins membership -------------------------------
check(elaborates("""
interface A
interface B
postulate(msg, unitTy)
command ca : unitTy -> unitTy in A
command cb : unitTy -> unitTy in B
proc both : [A, B] unitTy = cb (ca unitv)
"""), "both interfaces in the peg satisfy membership")

check(rejects("""
interface A
interface B
postulate(msg, unitTy)
command ca : unitTy -> unitTy in A
command cb : unitTy -> unitTy in B
proc missing : [B] unitTy = cb (ca unitv)
""", "requires interface 'A'"), "missing interface in the peg is rejected")

# --- data constructors stay usable under any ambient --------------------------------------
check(elaborates(prelude & """
data(Nat, Univ) where
| zero : Nat
| suc (n : Nat) : Nat
proc puts : [Console] unitTy = send msg
proc two : [Console] Nat = suc (suc zero)
"""), "constructors elaborate under an effectful ambient")

if failures == 0:
  echo "--- all ability tests passed ---"
else:
  echo "--- ", failures, " ability test(s) FAILED ---"
  quit(1)
