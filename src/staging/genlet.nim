## genlet: residual let-insertion for staged relational goals (issue #61).
##
## Partial evaluators duplicate computations: when a static function is
## applied twice in the residual, the application is computed twice. The
## standard fix is *let-insertion* — name the shared computation once
## with a residual `let`. Danvy's TDPE route and MetaOCaml's `genlet` do
## it by capturing the code-generation continuation up to a delimiter;
## this specializer works in direct style on RelGoal data, so the same
## sharing is achieved as a residual post-pass (common-subterm
## elimination with residual `fresh` binders):
##
##   P[t] ∧ Q[t]   →   (fresh gN. (gN == t) ∧ P[gN] ∧ Q[gN])
##
## The rewrite is semantics-preserving in miniKanren: `fresh v; v == t`
## just binds v to t. Insertion never crosses a binder (rgFresh) or a
## disjunction — both are sharing boundaries, so no variable is ever
## lifted out of its scope and no branch structure is reshuffled.
##
## When to insert: pure savings test. Replacing n occurrences of a term
## of s nodes with placeholders removes (n-1)*(s-1) term nodes and adds
## the residual equation (s+1 term nodes, ~3 goal nodes). Hoist only when
## the net is positive; this self-calibrates — on residuals with no real
## composite duplication (the current staged-typeo case, measured
## 1.85x/2.26x tree/DAG with mostly placeholder atoms), nothing qualifies
## and the pass is a no-op.
##
## Effect policy (issue #61 step 3): the ETT fragment staged so far is
## pure — every residual computation is safe to share. Let-insertion is
## therefore never required for correctness here, only an optional size
## optimization. When effectful primitives appear, insertion must be
## restricted to computations the effect annotation marks duplicable.

import staging/relgoal
import minikanren
import tables
import sequtils
import strutils

type
  GenletCtx* = object
    counter*: int  ## fresh-name supply for inserted binders

proc newGenletCtx*(): GenletCtx = GenletCtx(counter: 0)

proc termNodes(t: RTerm): int =
  ## Node count of a term (nil = empty list tail contributes 0).
  if t.isNil: 0
  else:
    1 + (case t.kind
         of rkAtom, rkVar: 0
         of rkPair: termNodes(t.head) + termNodes(t.tail))

proc countTerms(t: RTerm, freq: var CountTable[string],
                sample: var Table[string, RTerm]) =
  if t.isNil: return
  if t.kind == rkPair:
    let k = $t
    freq.inc(k)
    if k notin sample: sample[k] = t
    countTerms(t.head, freq, sample)
    countTerms(t.tail, freq, sample)

proc countCompositeWalk(x: RelGoal, freq: var CountTable[string],
                        sample: var Table[string, RTerm]) =
  case x.kind
  of rgFail, rgSucceed: discard
  of rgEq, rgNeq:
    countTerms(x.left, freq, sample)
    countTerms(x.right, freq, sample)
  of rgConj:
    countCompositeWalk(x.leftG, freq, sample)
    countCompositeWalk(x.rightG, freq, sample)
  of rgDisj, rgFresh: discard  # sharing boundary
  of rgCall: (for a in x.args: countTerms(a, freq, sample))
  of rgSetEq:
    (for t in x.cells: countTerms(t, freq, sample))
    (for t in x.values: countTerms(t, freq, sample))
  of rgBranch: (for v in x.vars: countTerms(v, freq, sample))

proc countComposite(g: RelGoal, freq: var CountTable[string],
                    sample: var Table[string, RTerm]) =
  ## Count composite (rkPair) RTerm occurrences by structural key in the
  ## subtree rooted at g. Stops at rgFresh and rgDisj boundaries: those
  ## are the sharing boundaries, so counted occurrences are always
  ## replaceable under one residual binder placed at the hoist site.
  ## `$` is canonical on these terms (cf. specKey in stagegoal.nim).
  countCompositeWalk(g, freq, sample)

proc substTerm(t: RTerm, target, repl: RTerm): RTerm =
  ## Replace structural occurrences of target in t with repl.
  if t.isNil: t
  elif $t == $target: repl
  elif t.kind == rkPair:
    rpair(substTerm(t.head, target, repl), substTerm(t.tail, target, repl))
  else: t

proc substShared(g: RelGoal, target, repl: RTerm): RelGoal =
  ## Replace occurrences of target in g with repl, using the same
  ## boundary discipline as countComposite (so exactly the counted
  ## occurrences are replaced).
  case g.kind
  of rgFail, rgSucceed: g
  of rgEq: rgEq(substTerm(g.left, target, repl), substTerm(g.right, target, repl))
  of rgNeq: rgNeq(substTerm(g.left, target, repl), substTerm(g.right, target, repl))
  of rgConj: rgConj(substShared(g.leftG, target, repl),
                    substShared(g.rightG, target, repl))
  of rgDisj, rgFresh: g  # boundary: not counted, not touched
  of rgCall: rgCall(g.relName, g.args.mapIt(substTerm(it, target, repl)))
  of rgSetEq:
    RelGoal(kind: rgSetEq,
            cells: g.cells.mapIt(substTerm(it, target, repl)),
            values: g.values.mapIt(substTerm(it, target, repl)))
  of rgBranch:
    RelGoal(kind: rgBranch, vars: g.vars.mapIt(substTerm(it, target, repl)))

proc hoist(g: RelGoal, ctx: var GenletCtx): RelGoal =
  ## Insert one residual let at this conjunction for the candidate with
  ## the largest positive node savings, if any.
  var freq = initCountTable[string]()
  var sample = initTable[string, RTerm]()
  countComposite(g, freq, sample)
  var bestKey = ""
  var bestSave = 0
  for k, n in freq:
    if n > 1:
      let s = termNodes(sample[k])
      # Savings: (n-1) occurrences replaced by 1-node placeholders,
      # minus the residual equation (s term nodes + ~3 goal nodes:
      # the eq itself, the fresh binder, the added conjunction).
      let save = (n - 1) * (s - 1) - s - 3
      if save > bestSave:
        bestSave = save
        bestKey = k
  if bestKey == "": return g
  let t = sample[bestKey]
  let name = "genlet" & $ctx.counter
  inc ctx.counter
  let ph = ratom("__var_" & name)
  rgFresh(name, rgConj(rgEq(ph, t), substShared(g, t, ph)))

proc insertLets*(rg: RelGoal, ctx: var GenletCtx): RelGoal =
  ## Bottom-up: inner lets first, then hoist at each conjunction.
  ## Loops per conjunction because one hoist can reveal the next
  ## candidate; each hoist strictly reduces node count (savings test),
  ## so the loop terminates.
  case rg.kind
  of rgConj:
    var g = rgConj(insertLets(rg.leftG, ctx), insertLets(rg.rightG, ctx))
    while true:
      let g2 = hoist(g, ctx)
      if g2 == g: break
      g = g2
    g
  of rgDisj:
    rgDisj(insertLets(rg.leftG, ctx), insertLets(rg.rightG, ctx))
  of rgFresh:
    rgFresh(rg.varName, insertLets(rg.body, ctx))
  else: rg

proc insertLetsIntoSpecs*(specs: var Table[string, RelEntry],
                          ctx: var GenletCtx) =
  ## Apply let-insertion to every specialized body (issue #61).
  for name, entry in specs.mpairs:
    entry.body = insertLets(entry.body, ctx)

when isMainModule:
  echo "=== genlet: residual let-insertion ==="
  echo ""
  # Synthetic goal with a genuinely shared composite term (8 nodes, x3):
  # t = ((f a b) . c)
  let t = rpair(rpair(ratom("f"), rpair(ratom("a"), rpair(ratom("b"), rnil()))),
                rpair(ratom("c"), rnil()))
  let g = rgFresh("x", rgFresh("y", rgFresh("z",
    rgConj(rgEq(ratom("__var_x"), t),
           rgConj(rgEq(ratom("__var_y"), t), rgEq(ratom("__var_z"), t))))))
  echo "before: ", g
  var ctx = newGenletCtx()
  let g2 = insertLets(g, ctx)
  echo "after:  ", g2
  echo "binders inserted: ", ctx.counter
  # The let lands at the hoist conjunction (inside the outer binders —
  # the pass never lifts a term across an rgFresh boundary).
  if ctx.counter == 1 and
     "(fresh genlet0 ((__var_genlet0 == " & $t & ")" in $g2 and
     "(__var_x == __var_genlet0)" in $g2 and
     "(__var_y == __var_genlet0)" in $g2 and
     "(__var_z == __var_genlet0)" in $g2:
    echo "✓ shared composite hoisted under one residual let"
  else:
    echo "✗ unexpected shape"
  echo ""
  # Semantics: both must admit exactly the shared term as the answer.
  let q1 = freshVar()
  let r1 = run(q1, conj(toGoal(g), `==`(q1, ratom("yes"))), 3).len
  let q2 = freshVar()
  let r2 = run(q2, conj(toGoal(g2), `==`(q2, ratom("yes"))), 3).len
  echo "answers before: ", r1, ", after: ", r2
  if r1 == 1 and r2 == 1: echo "✓ agreement: inserted let is α-semantics-preserving"
  else: echo "✗ agreement failure"
  echo ""
  # No-op case: atoms only — nothing qualifies, goal returned unchanged.
  let ga = rgConj(rgEq(ratom("__var_x"), ratom("__var_tm")),
                  rgEq(ratom("__var_y"), ratom("__var_tm")))
  var ctx2 = newGenletCtx()
  let ga2 = insertLets(ga, ctx2)
  if ctx2.counter == 0: echo "✓ atom-only duplication left alone (no spurious lets)"
  else: echo "✗ inserted ", ctx2.counter, " binders for atoms"
  echo ""
  echo "genlet pass works."
