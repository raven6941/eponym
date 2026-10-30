## First-class units and dimensions (issue #493).
##
## Watch: `Qty d` is nominal during Eponym checking but maps to float64 at
## runtime; Vec dimensions remain ordinary runtime values. Parsing and pure
## scalar/vector arithmetic cross explicit Nim bindings, whose behavior is
## trusted. `parseUnitChecked` returns the dimension beside a magnitude
## normalized to SI, so dynamic callers compare dimensions before `addQ`.

import std/math
import eponym_mac

proc hostAddQ(d: seq[int], a, b: float64): float64 = a + b
proc hostMulQ(d1, d2: seq[int], a, b: float64): float64 = a * b
proc hostDivQ(d1, d2: seq[int], a, b: float64): float64 = a / b
proc hostPowQ(n: int, d: seq[int], x: float64): float64 = pow(x, float64(n))

proc hostAddDim(a, b: seq[int]): seq[int] =
  if a.len != 3 or b.len != 3:
    raise newException(ValueError, "dimension vectors must have length 3")
  for i in 0 ..< 3: result.add(a[i] + b[i])

proc hostSubDim(a, b: seq[int]): seq[int] =
  if a.len != 3 or b.len != 3:
    raise newException(ValueError, "dimension vectors must have length 3")
  for i in 0 ..< 3: result.add(a[i] - b[i])

proc hostParseUnit(text: string): tuple[dimensions: seq[int], scale: float64] =
  case text
  of "lb*s": (@[1, 1, -1], 4.4482216152605) # lbf-second, normalized to N*s
  of "N*s": (@[1, 1, -1], 1.0)
  else: raise newException(ValueError, "unknown unit: " & text)

proc hostKilometers(value: float64): float64 = value * 1000.0

eponymBlock:
  import "../../lib/units.ep"
  runtimeType(Int, int)
  runtimeType(Nat, int)
  runtimeType(Float, float64)
  runtimeType(String, string)
  runtimeType(Qty, float64)
  runtimeVector(Vec)

  bindPostulatePair(parseUnit, hostParseUnit, String, Vec, Qty)
  bindPostulate(addDim, hostAddDim, Vec, Vec, Vec)
  bindPostulate(subDim, hostSubDim, Vec, Vec, Vec)
  bindPostulate(addQ, hostAddQ, Vec, Qty, Qty, Qty)
  bindPostulate(mulQ, hostMulQ, Vec, Vec, Qty, Qty, Qty)
  bindPostulate(divQ, hostDivQ, Vec, Vec, Qty, Qty, Qty)
  bindPostulate(powQ, hostPowQ, Int, Vec, Qty, Qty)
  bindPostulate(kilometers, hostKilometers, Float, Qty)

  # Concrete Nim signatures request typed wrappers for the imported library
  # definitions and keep their dependent Eponym contracts visible here.
  proc runParseUnit(text: String): Sig(dd: Vec[Int, 3], Qty[dd]) =
    parseUnitChecked(text)
  proc runAddQ(d {.unrestricted.}: Vec[Int, 3], x: Qty[d], y: Qty[d]): Qty[d] =
    addQ(d, x, y)
  proc runMulQ(d1 {.unrestricted.}: Vec[Int, 3], d2 {.unrestricted.}: Vec[Int, 3],
      x: Qty[d1], y: Qty[d2]): Qty[addDim(d1, d2)] = mulQ(d1, d2, x, y)
  proc runDivQ(d1 {.unrestricted.}: Vec[Int, 3], d2 {.unrestricted.}: Vec[Int, 3],
      x: Qty[d1], y: Qty[d2]): Qty[subDim(d1, d2)] = divQ(d1, d2, x, y)
  proc runPowQ(n {.unrestricted.}: Int, d {.unrestricted.}: Vec[Int, 3],
      x: Qty[d]): Qty[scaleDim(n, d)] = powQ(n, d, x)
  proc runKilometers(value: Float): Qty[lengthDim] = kilometersOf(value)
  proc runAddLengths(x: Qty[lengthDim], y: Qty[lengthDim]): Qty[lengthDim] =
    addLengths(x, y)
  proc runDimensionSum(d1: Vec[Int, 3], d2: Vec[Int, 3]): Vec[Int, 3] =
    dimensionSum(d1, d2)
  proc runDimensionDifference(d1: Vec[Int, 3], d2: Vec[Int, 3]): Vec[Int, 3] =
    dimensionDifference(d1, d2)

when isMainModule:
  let poundSeconds = runParseUnit("lb*s")
  let newtonSeconds = runParseUnit("N*s")
  doAssert poundSeconds[0] == newtonSeconds[0]
  let impulse = runAddQ(poundSeconds[0], poundSeconds[1], newtonSeconds[1])
  doAssert abs(impulse - 5.4482216152605) < 1e-12

  # Convert a real scaled unit and exercise both positive and negative powers.
  doAssert runKilometers(1.25) == 1250.0
  doAssert runAddLengths(2.0, 3.0) == 5.0
  doAssert runPowQ(-1, @[0, 0, 1], 2.0) == 0.5

  # Runtime values use the same checked algebra as their type indices.
  let speed = runDivQ(@[0, 1, 0], @[0, 0, 1], 100.0, 20.0)
  let area = runMulQ(@[0, 1, 0], @[0, 1, 0], 2.0, 3.0)
  doAssert speed == 5.0
  doAssert area == 6.0

  let lengthTimesLength = runDimensionSum(@[0, 1, 0], @[0, 1, 0])
  let lengthOverTime = runDimensionDifference(@[0, 1, 0], @[0, 0, 1])
  doAssert lengthTimesLength == [0, 2, 0]
  doAssert lengthOverTime == [0, 1, -1]

  var rejectedGarbage = false
  try:
    discard runParseUnit("not-a-unit")
  except ValueError:
    rejectedGarbage = true
  doAssert rejectedGarbage
