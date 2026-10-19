import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  postulate(Tag, Univ)
  proc indexedIdentity[n: Tag](value: Int): Int = value
  runtimeValue(indexedIdentity)

let result = indexedIdentityRuntimeValueRuntimeValueRaw([vNatLit(3)],
  [intToValue(1)])
doAssert result.value.whnfKind == wInt
doAssert result.value.whnfIntVal == 1
