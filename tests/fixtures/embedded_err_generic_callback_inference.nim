import ../../src/eponym/eponym_mac
import ../../src/eponym/eponym_embed
import ../../src/eponym/eponym_init
import ../../src/eponym/elab
import std/options

eponymBlock:
  import "runtime_imported_generic.ep"
  runtimeOption(Option)
  runtimeDataVariant(SizedTree)
  runtimeValue(importedGenericIndexedSigmaOptionCallbackApply)

proc badInferredCallback(): auto =
  let value = (7, some(RuntimeStructuredVariant(constructor: "sizedTree",
    arguments: @[
      RuntimeStructuredValue(kind: rsvNat, natValue: 1),
      RuntimeStructuredValue(kind: rsvVariant,
        variantValue: RuntimeStructuredVariant(constructor: "treeEmpty"))])))
  importedGenericIndexedSigmaOptionCallbackApply(
    proc(flag: bool): bool = not flag, value)
