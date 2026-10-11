## Online primitive operators for the staged ETT evaluator (GH #79).
##
## Tests + benchmark for the per-call unfold/residualize policy in
## ett_staged.nim (Danvy's online TDPE extension):
## - default policy: unfold iff all operands static, else residualize
## - user filters: `pow` unfolds only when the exponent is static and
##   below the size guard (Consel-style unfold control)
## - algebraic simplification during residualization (dynamic versions)
## - effect escape hatch: `traceAdd` is always residualized + let-inserted
## - benchmark vs the fixed offline policy (applyPrimFixed)

import std/[tables, times, strutils]
import eponym
import ett_staged

type ApplyFn = proc(name: string, args: seq[SVal]): SVal

proc apOnline(name: string, args: seq[SVal]): SVal =
  applyPrim(primTable[name], args)

proc apFixed(name: string, args: seq[SVal]): SVal =
  applyPrimFixed(primTable[name], args)

proc envOf(pairs: openArray[(string, int)]): Table[string, Value] =
  result = initTable[string, Value]()
  for (k, v) in pairs:
    result[k] = Value(kind: vkNat, natV: v)

proc checkAgree(name: string, staged: SVal, expected: int,
                env: Table[string, Value]) =
  let got = evalSVal(staged, env)
  assert got.kind == vkNat, name & ": residual did not evaluate to a nat"
  assert got.natV == expected,
    name & ": expected " & $expected & ", got " & $got.natV
  echo "ok: ", name, " == ", expected
  echo "    residual: ", $staged, "   nodes: ", countNodes(staged)

when isMainModule:
  let env = envOf([("x", 7), ("y", 11), ("z", 13), ("w", 4)])
  let x = dynamicVar("x")
  let y = dynamicVar("y")
  let z = dynamicVar("z")
  let w = dynamicVar("w")

  echo "=== A. default unfold/residualize policy ==="
  resetPrimStats()
  let a1 = apOnline("add", @[natLit(2), natLit(3)])
  assert isStaticNat(a1) and a1.val.natV == 5 and countNodes(a1) == 0
  echo "ok: add(2,3) unfolds to static 5 (unfolds=", primUnfolds, ")"
  let a2 = apOnline("add", @[natLit(2), x])
  assert not isStaticNat(a2) and countNodes(a2) == 2  # prim + var; static 2 leaves no trace
  echo "ok: add(2,x) residualizes: ", $a2, " (residuals=", primResiduals, ")"
  checkAgree("add(2,x) with x=7", a2, 9, env)

  echo "=== B. user filters: pow unfolds only on static small exponent ==="
  resetPrimStats()
  let b1 = apOnline("pow", @[natLit(2), natLit(10)])
  assert isStaticNat(b1) and b1.val.natV == 1024
  echo "ok: pow(2,10) unfolds to 1024 (filter passed)"
  let b2 = apOnline("pow", @[natLit(2), w])
  assert not isStaticNat(b2)
  echo "ok: pow(2,w) residualizes (exponent dynamic): ", $b2
  checkAgree("pow(2,w) with w=4", b2, 16, env)
  let b3 = apOnline("pow", @[natLit(2), natLit(100)])
  assert not isStaticNat(b3)
  echo "ok: pow(2,100) residualizes (size guard: exponent >= 32): ", $b3

  echo "=== C. algebraic simplification during residualization ==="
  resetPrimStats()
  let c1 = apOnline("add", @[x, natLit(0)])
  assert countNodes(c1) == 1
  echo "ok: x + 0 -> x (simps=", primSimps, ")"
  let c2 = apOnline("mul", @[natLit(0), y])
  assert isStaticNat(c2) and c2.val.natV == 0 and countNodes(c2) == 0
  echo "ok: 0 * y -> static 0 (pure op: residual computation discarded)"
  let c3 = apOnline("mul", @[z, natLit(1)])
  assert countNodes(c3) == 1
  echo "ok: z * 1 -> z"
  checkAgree("x+0 with x=7", c1, 7, env)
  checkAgree("0*y with y=11", c2, 0, env)
  checkAgree("z*1 with z=13", c3, 13, env)

  echo "=== D. effect escape hatch: always residualize + let-insert ==="
  resetPrimStats()
  let d1 = apOnline("traceAdd", @[natLit(1), natLit(2)])
  assert not isStaticNat(d1)
  assert d1.node.kind == enkLet and d1.node.rhs.node.kind == enkPrim
  echo "ok: traceAdd(1,2) residualized + let-inserted despite static args:"
  echo "    ", $d1, "   nodes: ", countNodes(d1),
       " (residuals=", primResiduals, ", unfolds=", primUnfolds, ")"
  checkAgree("traceAdd(1,2)", d1, 3, env)
  let d2 = apOnline("traceAdd", @[x, y])
  checkAgree("traceAdd(x,y) with x=7,y=11", d2, 18, env)

  echo "=== E. benchmark: arithmetic-heavy corpus, online vs fixed ==="
  proc corpus(apply: ApplyFn): SVal =
    let t1 = apply("add", @[natLit(2), natLit(3)])   # 5
    let t2 = apply("add", @[x, natLit(0)])            # x (online) | (add x 0)
    let t3 = apply("mul", @[t1, t2])                 # (mul 5 x)
    let t4 = apply("mul", @[natLit(0), y])           # 0 (online) | (mul 0 y)
    let t5 = apply("add", @[t3, t4])                 # (mul 5 x) (online)
    let t6 = apply("mul", @[z, natLit(1)])           # z (online) | (mul z 1)
    let t7 = apply("pow", @[natLit(2), natLit(10)])  # 1024
    let t8 = apply("add", @[t5, t6])
    apply("add", @[t8, t7])

  resetPrimStats()
  let online = corpus(apOnline)
  let onlineUnfolds = primUnfolds
  let onlineSimps = primSimps
  let fixed = corpus(apFixed)
  echo "online residual: ", $online
  echo "fixed  residual: ", $fixed
  echo "nodes: online=", countNodes(online), " fixed=", countNodes(fixed),
       " (unfolds=", onlineUnfolds, ", simps=", onlineSimps, ")"
  assert countNodes(online) < countNodes(fixed),
    "online policy should shrink the residual"

  # staged/unstaged agreement on the corpus: 5*7 + 0 + 13 + 1024 = 1072
  checkAgree("corpus online", online, 1072, env)
  checkAgree("corpus fixed", fixed, 1072, env)

  # wall-clock: evaluate both residuals repeatedly
  const iters = 50_000
  let t0 = cpuTime()
  var acc = 0
  for _ in 0 ..< iters:
    acc += evalSVal(online, env).natV
  let tOnline = cpuTime() - t0
  let t1 = cpuTime()
  for _ in 0 ..< iters:
    acc += evalSVal(fixed, env).natV
  let tFixed = cpuTime() - t1
  doAssert acc == 2 * iters * 1072
  echo "eval ", iters, "x: online=", tOnline.formatFloat(ffDecimal, 3), "s",
       " fixed=", tFixed.formatFloat(ffDecimal, 3), "s"
  echo "ALL PRIMOP TESTS PASSED"
