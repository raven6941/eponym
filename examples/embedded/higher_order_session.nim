# Higher-order constructor arguments, embedded (Issue #113 / #144).
#
# A session continuation can depend on a value received earlier:
#   recvDNat (k : Nat -> Session)
# is strictly positive in Session (Session occurs only in the codomain),
# so the datatype is accepted. The generated eliminator gives each
# higher-order argument an induction hypothesis *under binders*:
#   ih : Pi (n : Nat). C (k n)
# and the computation rule pushes the recursive call under the binders:
#   sessionElim C ms (recvDNat k) = m_recvDNat k (fun n => sessionElim C ms (k n))
#
# Two-layer shape: the proof layer (the eponymBlock below) is checked at
# compile time by the elaborator; the running layer is plain Nim.

import eponym_mac

eponymBlock:
  # Prelude import (issue #131): Nat (+ zero, suc) from lib/nat.ep.
  import "../../lib/nat.ep"

  # Protocol descriptions are normalized and checked during elaboration;
  # this demo does not expose a runtime Session value.
  compileTimeOnly(proto)
  compileTimeOnly(receives)
  compileTimeOnly(protoReceives)

  # Session protocol descriptions with dependent continuations.
  data(Session, [], Univ):
    proc sendD(A: Univ, k: A -> Session): Session
    proc recvDNat(k: Nat -> Session): Session
    proc endD(): Session

  # A protocol: receive a Nat, then send a Nat, then done. The continuation
  # after the receive is a function of the received value.
  proc proto(): Session =
    recvDNat(lam(n: Nat) => sendD(Nat, lam(m: Nat) => endD()))

  # Count the receives in a protocol. The recvDNat method applies its
  # induction hypothesis under the binder (ih zero); the sendD method
  # contributes zero receives.
  proc receives(s: Session): Nat =
    sessionElim(lam(u: Session) => Nat,
      lam(A: Univ) => lam(k: A -> Session) => lam(ih: Pi(x: A, Nat)) => zero(),
      lam(k: Nat -> Session) => lam(ih: Pi(n: Nat, Nat)) => suc(ih(zero())),
      zero(),
      s)

  proc protoReceives(): Nat = receives(proto())

# --- Normal Nim program ------------------------------------------------
# Plain Nim from here. `receives` computes through the generated
# eliminator; `protoReceives` must reduce to 1 (one receive in the
# protocol).

proc main() =
  echo "higher_order_session: higher-order ctor args elaborated at compile time."
  echo "receives : Session -> Nat -- checks out."

when isMainModule:
  main()
