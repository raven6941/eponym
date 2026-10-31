## Issue #409: `bindPostulateValue`-bound postulates applied at statically
## known types go through generated typed adapters instead of the
## `postulateValue` bindings-table lookup plus per-argument
## `vCompiledAppWithBindings` fold.
##
## Slice 2 (Value tier): each instantiation gets an emitted
## `eponymTypedAdapter_<post>_<types>_<n>` proc calling the user's
## `(args, globals)` proc directly with baked type witnesses. The key
## assertion calls the compiled definition proc directly with EMPTY
## runtime bindings — the old fold path resolves the postulate through
## the bindings table, so it cannot produce a real result without the
## binding; observing the correct value proves the reroute.
##
## Slice 3 (repr tier): each int-fragment instantiation additionally gets
## an `eponymReprAdapter_<post>_<types>_<n>` proc with the representation
## signature (`int -> int` here — no `RuntimeValue` anywhere in it) that
## encodes its arguments, calls the Value-tier adapter, and decodes the
## result. `echoInt` maps `Int` to Nim `int`, so its body compiles in the
## repr tier through the adapter; `echoBool` has no mapping and stays on
## the Value tier. The differential check asserts both tiers print the
## same representation and return the same value on the same inputs.

import eponym_mac
import eponym_embed

var adapterArgCounts: seq[int] = @[]
var adapterPrinted: seq[string] = @[]

proc recordingDebugEcho(args: seq[RuntimeValue],
                        globals: RuntimeGlobals): RuntimeValue =
  adapterArgCounts.add(args.len)
  adapterPrinted.add(runtimeValueDebugString(args[1], globals))
  args[1]

eponymRuntimeBridgeTestBlock:
  postulate(Int, Univ)
  runtimeType(Int, int)
  import "../lib/debug.ep"
  import "../lib/bool.ep"
  bindPostulateValue(debugEcho, recordingDebugEcho)
  proc echoInt(value: Int): Int = debugEcho[Int](value)
  proc echoBool(value: Bool): Bool = debugEcho[Bool](value)

when isMainModule:
  # 1. Value tier: direct call to the compiled proc with empty bindings —
  #    only the typed adapter can serve this, since the fold path needs
  #    the postulate's runtime binding.
  let direct = eponymCompiled_echoInt(@[intToValue(41)], initRuntimeBindings())
  doAssert valueToInt(direct) == 41,
    "issue #409: typed adapter should serve the call without runtime bindings"
  doAssert adapterArgCounts == @[2],
    "typed adapter should pass [typeWitness, value], got " & $adapterArgCounts
  doAssert adapterPrinted == @["41"],
    "value-tier call should print the representation, got " & $adapterPrinted

  # 2. Repr tier: echoInt's body compiled in the repr tier, which requires
  #    the #409 repr-adapter reroute — without it the postulate reference
  #    is outside the representation fragment and no repr proc is emitted.
  static:
    doAssert declared(eponymCompiledRepr_echoInt),
      "issue #409: echoInt should reach the repr tier via the repr adapter"
  doAssert eponymCompiledRepr_echoInt(42) == 42
  doAssert adapterPrinted == @["41", "42"],
    "repr-tier call should print the same representation, got " &
      $adapterPrinted

  # 3. The repr adapter itself is a fully typed Nim proc — no
  #    RuntimeValue in its signature. (`_1` is this file's single
  #    eponymBlock expansion sequence.)
  doAssert eponymReprAdapter_debugEcho_Int_1(43) == 43
  doAssert adapterPrinted == @["41", "42", "43"]

  # 4. End-to-end behavior through the wrappers is unchanged: the Int
  #    wrapper routes to the repr proc (identity boundary), Bool stays
  #    on the Value tier. Differential: both tiers print the same
  #    representation and return the value unchanged.
  doAssert echoInt(44) == 44
  doAssert echoBool(true) == true
  doAssert echoBool(false) == false
  doAssert adapterArgCounts == @[2, 2, 2, 2, 2, 2]
  doAssert adapterPrinted == @["41", "42", "43", "44", "true", "false"],
    "differential printed representations diverged: " & $adapterPrinted
  echo "test_postulate_typed_adapter: typed-adapter reroute passed"
