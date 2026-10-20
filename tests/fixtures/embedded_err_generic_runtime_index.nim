import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Nat, Univ)
  proc indexedIdentity[n: Nat](value: Nat): Nat = value
  runtimeValue(indexedIdentity)

discard indexedIdentityRuntimeValue(1)
