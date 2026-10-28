import eponym_mac

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/eq.ep"

  proc refineTarget(x: Nat): Nat = shedHole(refineGoal)
  proc giveTarget(x: Nat): Nat = ![giveGoal]
  proc introTarget(): Pi(x: Nat, Nat) = ![introGoal]
  proc constructTarget(): Nat = ![constructGoal]
  proc applyTarget(x: Nat): Nat = ![applyGoal]
  proc caseTarget(n: Nat): Nat = ![caseGoal]
  proc rewriteTarget(x: Nat, y: Nat, e: Eq Nat x y): Eq Nat x x = ![rewriteGoal]
