# Singleton types for literals, embedded (Issue #74).
#
# Every Nat literal elaborates with a *singleton type*: `2 : 2`, and
# `2 <: Nat` by definitional subsumption (widening on demand). In type
# position a literal *is* its singleton type (Scala 3 literal-type
# style), so a parameter can demand exactly one value: `(d : 2)`.
#
# What this buys: precise argument types. `divBy2` below takes a divisor
# of type `2` — `divBy2 6 3` is a compile-time type error (see the
# `embedded_err_singleton_mismatch` fixture), while `divBy2 6 2`
# checks. Without singletons the divisor would be a plain Nat and the
# restriction inexpressible in the type.
#
# This is the elaborator's (and the kernel's) only subtyping, kept
# minimal and decidable: tNatSing(k) <: Nat, covariant through Pi
# codomains and Sigma components, definitional equality elsewhere.
#
# Scope note: the full MLstruct story also refines the *fall-through*
# branch of a literal match to `Nat ∩ ¬0`. Eponym has no negation
# types (and no `case` surface syntax yet), so that half is explicitly
# out of scope — see issue #74.

import eponym_mac
import eponym_embed

eponymBlock:
  # Prelude import (issue #131): Nat, zero, suc, add, mul from lib/nat.ep.
  import "../../lib/nat.ep"

  # The divisor must be exactly the literal 2.
  proc divBy2(n: Nat, d: 2): Nat = n

  # The literal 2 checks against the singleton domain ...
  proc six(): Nat = divBy2(6, 2)

  # ... and a singleton-typed variable widens to Nat on demand.
  proc useIt(d: 2): Nat = divBy2(4, d)

  # Singleton widening is covariant through Pi codomains (issue #223):
  # the inferred Pi(d:2).2 checks against the ascribed Pi(d:2).Nat.
  proc widenPi(d: 2): Nat = d

  # ... and through Sigma components: Sig(d:2).2 <: Sig(d:2).Nat.
  proc widenSig(p: Sig(d: 2, 2)): Sig(d: 2, Nat) = p

  # Ordinary Nat code is unaffected: literals still check against Nat.
  proc idNat(n: Nat): Nat = n
  proc seven(): Nat = idNat(7)

proc main() =
  echo "singleton_types: singleton types for Nat literals (Issue #74)."
  echo "  divBy2's divisor has type `2`: divBy2(6, 3) is a compile-time"
  echo "  error (tests/fixtures/embedded_err_singleton_mismatch.nim);"
  echo "  divBy2(6, 2) checks, and singleton variables widen to Nat."

when isMainModule:
  main()
