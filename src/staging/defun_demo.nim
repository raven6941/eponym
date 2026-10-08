## Issue #24 demo: defunctionalized continuations, and the staging comparison.
##
## Part 1 — Continuation sites in the engine (confirmed by reading
##   src/minikanren.nim before the change):
##   - `Goal = proc(s: State): Stream` — every goal a closure (USER BOUNDARY,
##     kept: user goals are the program, not engine control flow)
##   - `skBind.fn: proc(s: State): Stream` — bind continuation (DEFUNCTIONALIZED
##     to `Cont`: ckOne(single goal) | ckSeq(goal sequence))
##   - `skThunk.thunk: proc(): Stream` — laziness wrapper (DEFUNCTIONALIZED
##     to `skFresh{nvars, body, fstate}` data)
##   - `bindStream`/`take` used to compose flattening closures at
##     construction and execution time (DEFUNCTIONALIZED: concatCont appends
##     data; applyCont interprets)
##   - `freshN` bodies, `typeoRec` param: user goal constructors (boundary)
##   - Goal-level defunctionalization already exists as RelGoal
##     (src/staging/relgoal.nim, Phase 3 design) — the data form stageGoal
##     consumes. The closure typeo (rel_elab) and RelGoal typeo
##     (stage_typeo.typeoData) are maintained in parallel by hand; no
##     mechanical closure->RelGoal translator exists.
##
## Part 2 — Inspectability: control flow is now first-order data.
##   With closures, a stream's continuations were opaque: no analyzer or
##   specializer could see how many goals a bind composes, or which ones.
##   Now every node is traversable (only user Goal leaves stay closures).
##
## Part 3 — Agreement: the defunctionalized engine gives the same answers.
##
## Part 4 — Staging head-to-head:
##   - Higher-order (closure typeo): stageGoal takes RelGoal, not Goal.
##     There is no inspection path for a closure — the specializer cannot
##     see through it at all. (Stated, not run: it is a type-level fact.)
##   - Defunctionalized (RelGoal typeo): stageGoal prunes statically
##     impossible branches; the residual executes on the defunctionalized
##     engine via toGoal.

import minikanren
import rel_elab
import rel_interp
import staging/relgoal
import staging/stagegoal
import staging/stage_typeo  # typeoData
import tables
import sets
import strutils
import sequtils

echo "=== Issue #24: defunctionalized continuations ==="
echo ""

# --- Part 2: inspect a raw stream tree as data ---

proc countKinds(s: Stream, counts: var Table[StreamKind, int]) =
  counts.mgetOrPut(s.kind, 0) += 1
  case s.kind
  of skEmpty: discard
  of skCons: countKinds(s.tail, counts)
  of skMPlus:
    countKinds(s.left, counts)
    countKinds(s.right, counts)
  of skBind: countKinds(s.src, counts)
  of skFresh: discard  # body is user code (boundary); structure is data

let q0 = freshVar()
# conj(conj(conj(a,b),c),d): nested binds must flatten to ONE skBind
# whose Cont is ckSeq of 3 goals — data append, not closure composition.
let g0 = conj(conj(conj(`==`(q0, rint(1)), `==`(q0, rint(1))),
                   `==`(q0, rint(1))),
              `==`(q0, rint(1)))
let st0 = g0(emptyState())
assert st0.kind == skBind, "expected top-level skBind, got " & $st0.kind
assert st0.cont.kind == ckSeq, "expected flattened ckSeq cont"
assert st0.cont.goals.len == 3, "expected 3 flattened goals, got " & $st0.cont.goals.len
echo "Part 2a: nested conj flattens to one skBind with ckSeq of ",
  st0.cont.goals.len, " goals (was: nested closure composition)"

let qf = freshVar()
let gf = conj(fresh(proc(x: RTerm): Goal = `==`(x, rint(7))),
               `==`(qf, rint(7)))
let stf = gf(emptyState())
var counts = initTable[StreamKind, int]()
countKinds(stf, counts)
assert counts.getOrDefault(skFresh, 0) == 1, "expected one skFresh node"
echo "Part 2b: stream node census: ", counts
echo "  (fresh is an skFresh data node; every control node is traversable)"
echo ""

# --- Part 3: agreement ---

let q1 = freshVar()
let r1 = run(q1, typeo(zeroTm(), q1, rnil()), 1)
assert r1.len == 1 and $r1[0] == "nat"
echo "Part 3a: typeo(zero) = nat  ✓"

let q2 = freshVar()
let tm2 = addTm(sucTm(zeroTm()), sucTm(sucTm(zeroTm())))
let r2 = run(q2, evalo(tm2, q2), 1)
assert r2.len == 1 and $r2[0] == "(suc (suc (suc zero)))"
echo "Part 3b: evalo(1+2) = 3  ✓"

let q3 = freshVar()
let r3 = run(q3, typeo(lamTm(varTm(0)), q3, rnil()), 3)
assert r3.len == 3 and r3.allIt(($it).startsWith("(arr"))
echo "Part 3c: typeo(lam(var 0)) = (arr ?v ?v) ×3 (iterative deepening)  ✓"
echo "  (matches pre-defunctionalization behavior exactly)"
echo ""

# --- Part 4: staging head-to-head ---

echo "Part 4a: higher-order typeo (rel_elab, Goal = proc) is opaque to"
echo "  stageGoal: it takes RelGoal, and no closure->RelGoal inspection"
echo "  exists. The specializer cannot see through it at all."
echo ""

var staticEnv = initTable[string, RTerm]()
staticEnv["__var_ty"] = natTy()  # ty = nat, static
var dynamicVars = initHashSet[string]()
dynamicVars.incl("__var_tm")
dynamicVars.incl("__var_ctx")

let staged = stageGoal(typeoData(), staticEnv, dynamicVars)
assert staged.kind == sgResidual
assert "lam" notin $staged.goal, "lam branch should be pruned, got: " & $staged.goal
echo "Part 4b: defunctionalized (RelGoal) typeo stages with ty=nat static:"
echo "  lam branch pruned: ✓"
echo "  residual: ", staged.goal
echo ""

# Execute a pruned residual on the defunctionalized engine.
# (The typeo residual above still contains rgCall; the toGoal prototype
# does not substitute call args — a known staging-prototype gap, not
# something this issue takes on. Here we use a call-free residual.)
let pv = ratom("__var_v")
let pu = ratom("__var_u")
let pre1 = rgConj(
  rgEq(pv, pu),
  rgDisj(rgEq(zeroTm(), sucTm(zeroTm())),  # statically impossible: pruned
         rgEq(pv, zeroTm())))
var penv = initTable[string, RTerm]()
var pdyn = initHashSet[string]()
pdyn.incl("__var_v")
pdyn.incl("__var_u")
let pstaged = stageGoal(pre1, penv, pdyn)
assert pstaged.kind == sgResidual, "expected residual, got " & $pstaged.kind
assert "suc" notin $pstaged.goal,
  "impossible branch should be pruned, got: " & $pstaged.goal
echo "Part 4c: pruned residual: ", pstaged.goal
let pq = freshVar()
let pgoal = toGoal(substAtom(substAtom(pstaged.goal, pv, pq), pu, pq))
let pres = run(pq, pgoal, 2)
assert pres.len == 1 and $pres[0] == "zero", "expected [zero], got " & $pres
echo "  executes on the defunctionalized engine: v = zero  ✓"
echo ""
echo "=== done ==="
