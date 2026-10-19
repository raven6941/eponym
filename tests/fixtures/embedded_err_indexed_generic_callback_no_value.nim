import eponym_mac
import eponym_embed
import eponym_init
import elab

eponymBlock:
  import "runtime_imported_generic_variant.ep"
  runtimeDataVariant(SizedTree)
  runtimeValue(importedGenericIndexedCallbackReturn)

discard importedGenericIndexedCallbackReturn(
  proc(value: RuntimeStructuredVariant): RuntimeStructuredVariant = value)
