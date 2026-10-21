## Opaque Float/String/Char mappings preserve values through checked wrappers.

import falsify
import eponym_mac
import eponym_embed

proc hostFloatScale(value: float64): float64 = value * 2.5 + 0.75
proc hostStringSuffix(value: string): string = value & "!"
proc hostCharIdentity(value: char): char = value

eponymBlock:
  import "../lib/float.ep"
  import "../lib/text.ep"
  runtimeType(Float, float64)
  runtimeType(String, string)
  runtimeType(Char, char)
  postulate(scaleFloat, Float -> Float)
  bindPostulate(scaleFloat, hostFloatScale, Float, Float)
  postulate(addSuffix, String -> String)
  bindPostulate(addSuffix, hostStringSuffix, String, String)
  postulate(keepChar, Char -> Char)
  bindPostulate(keepChar, hostCharIdentity, Char, Char)
  proc checkedScaleFloat(value: Float): Float = scaleFloat(value)
  proc checkedAddSuffix(value: String): String = addSuffix(value)
  proc checkedKeepChar(value: Char): Char = keepChar(value)

static:
  doAssert not compiles(checkedScaleFloat("not a Float"))
  doAssert not compiles(checkedAddSuffix(12))
  doAssert not compiles(checkedKeepChar("not a Char"))

when isMainModule:
  var rng = initRng(20261021'u64)
  let floatCodecCases = forAll("opaque Float runtime mapping",
    rng, 200,
    proc(r: var Rng): float64 = r.genFloat(-1000.0, 1000.0),
    proc(value: float64): bool =
      checkedScaleFloat(value) == hostFloatScale(value),
    shrinkFloat)
  let stringCodecCases = forAll("opaque String runtime mapping",
    rng, 200,
    proc(r: var Rng): string = r.genString(30),
    proc(value: string): bool = checkedAddSuffix(value) == value & "!",
    shrinkString)
  let charCodecCases = forAll("opaque Char runtime mapping",
    rng, 200,
    proc(r: var Rng): char = r.genChar(),
    proc(value: char): bool = checkedKeepChar(value) == value,
    shrinkChar)
  if not floatCodecCases or not stringCodecCases or not charCodecCases:
    quit(1)
  echo "test_scalar_runtime_codecs: opaque scalar properties passed"
