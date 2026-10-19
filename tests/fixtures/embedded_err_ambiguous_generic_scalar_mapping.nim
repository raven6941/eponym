import eponym_mac
import eponym_embed
import eponym_init
import elab

eponymBlock:
  import "runtime_imported_generic.ep"
  runtimeVector(Vec)
  runtimeType(RuntimeScalar, int)
  postulate(OtherScalar, Univ)
  runtimeType(OtherScalar, int)
  runtimeValue(importedGenericSingleton)

discard importedGenericSingleton(42)
