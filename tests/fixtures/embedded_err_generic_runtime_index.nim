import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  proc indexedIdentity[n: Int](value: Int): Int = value
  runtimeValue(indexedIdentity)

discard indexedIdentityRuntimeValue(1)
