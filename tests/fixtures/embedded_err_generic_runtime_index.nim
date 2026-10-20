import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  postulate(Tag, Univ)
  proc indexedIdentity[n: Tag](value: Int): Int = value
  runtimeValue(indexedIdentity)

discard indexedIdentityRuntimeValue(1)
