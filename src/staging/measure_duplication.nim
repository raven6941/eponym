## Duplication measurement for #61 (let-insertion / genlet).
##
## Step 1 of issue #61: quantify residual code duplication in the staged
## typeo pipeline (stageGoal partial deduction, src/staging/stagegoal.nim),
## specialized for typeo(tm, nat, ctx) with tm/ctx dynamic — the same
## specialization the stagedTypeoProcs macro in relcompile.nim performs.
##
## Metric: for each specialized body's RelGoal AST (goals + embedded
## RTerms), count tree nodes (naive residual: every occurrence is a fresh
## copy, as applyEnv/substAtom build it) vs. DAG nodes (structurally
## identical subterms shared — the let-bound minimal form a genlet-style
## specializer would produce). Blowup factor = tree / DAG.
## Structural keys come from `$`, which is canonical on ground terms
## (cf. specKey in stagegoal.nim); for RelGoals it is the printed form.
##
## Usage: nim c -r --path:src src/staging/measure_duplication.nim

import staging/relgoal
import staging/stagegoal
import staging/modes
import staging/typeo_relgoal
import minikanren
import rel_elab
import tables
import sets
import strutils
import algorithm

# --- structural keys + tree/DAG walk ----------------------------------------

proc keyOf(t: RTerm): string = "t:" & $t

proc keyOf(rg: RelGoal): string =
  case rg.kind
  of rgFail, rgSucceed, rgEq, rgNeq, rgConj, rgDisj,
     rgFresh, rgCall, rgSetEq, rgBranch:
    "g:" & $rg

type Walk = object
  tree: int                 # node count, duplicates counted per occurrence
  dag: HashSet[string]      # structurally distinct nodes
  freq: CountTable[string]  # occurrence count per structural key
  names: Table[string, string]  # key -> short sample rendering

proc add(w: var Walk, key: string, render: string) =
  inc w.tree
  w.dag.incl(key)
  w.freq.inc(key)
  if key notin w.names: w.names[key] = render

proc walkTerm(w: var Walk, t: RTerm) =
  if t.isNil: return
  w.add(keyOf(t), $t)
  case t.kind
  of rkAtom, rkVar: discard
  of rkPair:
    walkTerm(w, t.head)
    walkTerm(w, t.tail)

proc walkGoal(w: var Walk, rg: RelGoal) =
  w.add(keyOf(rg), $rg)
  case rg.kind
  of rgFail, rgSucceed: discard
  of rgEq, rgNeq:
    walkTerm(w, rg.left); walkTerm(w, rg.right)
  of rgConj, rgDisj:
    walkGoal(w, rg.leftG); walkGoal(w, rg.rightG)
  of rgFresh:
    walkGoal(w, rg.body)
  of rgCall:
    for a in rg.args: walkTerm(w, a)
  of rgSetEq:
    for t in rg.cells: walkTerm(w, t)
    for t in rg.values: walkTerm(w, t)
  of rgBranch:
    for t in rg.vars: walkTerm(w, t)

proc report(title: string, staticTy: RTerm) =
  var relEnv = initTable[string, RelDef]()
  relEnv["typeo"] = RelDef(name: "typeo", params: @["tm", "ty", "ctx"],
                           modes: @[mIn, mIn, mIn], body: typeoData())
  var spCtx = newSpecCtx(relEnv, fuel = 8)
  var staticParams = initTable[string, RTerm]()
  staticParams["ty"] = staticTy
  var dynamicVars = initHashSet[string]()
  dynamicVars.incl("__var_tm")
  dynamicVars.incl("__var_ctx")
  let top = specializeRelation(spCtx, "typeo", staticParams, dynamicVars)
  echo "== ", title, " (top: ", top, ", specs: ", spCtx.specs.len, ") =="
  var w: Walk
  w.dag = initHashSet[string]()
  var names = newSeq[string]()
  for name in spCtx.specs.keys: names.add(name)
  names.sort()
  for name in names:
    let e = spCtx.specs[name]
    echo "--- ", name, "(", e.params.join(", "), ") ---"
    echo $e.body
    echo ""
    walkGoal(w, e.body)
  echo "-- duplication report --"
  echo "tree nodes (naive residual): ", w.tree
  echo "DAG nodes  (let-bound minimal): ", w.dag.len
  echo "blowup factor (tree/DAG): ", formatFloat(w.tree / max(1, w.dag.len), ffDecimal, 3)
  type Dup = tuple[key: string, n: int]
  var dups: seq[Dup] = @[]
  for key, n in w.freq:
    if n > 1 and key.len > 5 and not key.startsWith("g:(fail"):
      dups.add((key, n))
  dups.sort(proc(a, b: Dup): int = cmp(b.n, a.n))
  echo "top repeated subterms (genlet candidates):"
  for i in 0 ..< min(8, dups.len):
    let (key, n) = dups[i]
    let sample = w.names[key]
    let short = if sample.len > 90: sample[0 .. 87] & "..." else: sample
    echo "  x" & $n & "  " & short
  echo ""

report("typeo(tm, nat, ctx)  [relcompile.stagedTypeoProcs case]", natTy())
# Composite static type: the arrow appears whole in staged equations.
report("typeo(tm, arr(arr(nat,nat),nat), ctx)",
       arrTy(arrTy(natTy(), natTy()), natTy()))
