## The optimizer must evaluate the checked, certified Eponym objective.
import falsify
import ../examples/embedded/convex_opt as convex

when isMainModule:
  var rng = initRng(681203'u64)
  let objectiveCases = forAll(
    "runtime interpreter evaluates the certified CExpr",
    rng, 300,
    proc(r: var Rng): int = r.genInt(-100, 100),
    proc(x: int): bool =
      let delta = x - 3
      let objective = 2 * delta * delta + x
      convex.evalCertifiedObjective(x) == objective and
        convex.evalShiftedCertifiedObjective(x) == objective + 11,
    shrinkInt)
  if not objectiveCases:
    quit(1)
  doAssert convex.evalCertifiedObjective(3) == 3
  echo "test_convex_opt_runtime: checked objective drives runtime evaluation"
