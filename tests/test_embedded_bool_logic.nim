## Nim Boolean `and`/`or` lower to checked, short-circuiting Eponym terms.

import falsify
import eponym_mac
import eponym_embed

var observedBoolCalls = 0

proc observeBool(value: bool): bool =
  inc observedBoolCalls
  value

proc negateBool(value: bool): bool = not value

eponymBlock:
  import "../lib/bool.ep"
  postulate(observe, Bool -> Bool)
  bindPostulate(observe, observeBool, Bool)
  proc checkedAnd(value: Bool): Bool = value and observe(true)
  proc checkedOr(value: Bool): Bool = value or observe(false)
  proc applyCallback(callback: proc(value: Bool): Bool {.closure.},
      value: Bool): Bool = callback(value)

var rng = initRng(0xB001)
let cases = forAll(
  "embedded Bool logic short-circuits and accepts named Nim callbacks", rng, 200,
  proc(r: var Rng): bool = r.genInt(0, 1) == 1,
  proc(value: bool): bool =
    observedBoolCalls = 0
    let andResult = checkedAnd(value)
    let andCalls = observedBoolCalls
    observedBoolCalls = 0
    let orResult = checkedOr(value)
    let orCalls = observedBoolCalls
    let callbackResult = applyCallback(negateBool, value)
    andResult == value and andCalls == (if value: 1 else: 0) and
      orResult == value and orCalls == (if value: 0 else: 1) and
      callbackResult == not value)
if not cases:
  quit(1)

echo "test_embedded_bool_logic: checked Boolean operators short-circuit"
