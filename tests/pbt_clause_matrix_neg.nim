## tests/pbt_clause_matrix_neg.nim — Issue #163: negative property tests for the
## clause-matrix compiler's coverage/redundancy/overlap checkers (#78).
##
## The positive suite (tests/pbt_clause_matrix.nim) pins the *acceptance*
## behavior: generated exhaustive, redundancy-free matrices must elaborate
## and compute the reference semantics. This suite pins the *rejection*
## behavior, which was previously covered only by a handful of hand-written
## `.ep` examples in `src/eponym/elab.nim`'s self-tests:
##
## - P_neg1 (coverage soundness): take a generated exhaustive matrix and drop
##   one constructor-headed row. The matrix no longer covers the value space,
##   so elaboration must fail with an ElabError mentioning "missing case for
##   constructor". Generation is disjoint-by-construction (see expandPat),
##   so dropping any single row always leaves a genuine coverage gap — the
##   property cannot pass vacuously by dropping a row that was already dead.
## - P_neg2 (redundancy detection): take a generated exhaustive matrix and
##   append a wildcard catch-all. The catch-all is dead code (the matrix
##   already covers every value), so elaboration must fail with an ElabError
##   mentioning "redundant clause". Note the checker reports this from the
##   nested split node when the partition is nested (e.g. "(under 'suc')"),
##   so the property asserts only the stable fragment.
## - P_neg3 (overlap detection): take a generated exhaustive matrix and
##   duplicate an existing row. The duplicate is subsumed by the earlier
##   identical row, so elaboration must fail with an ElabError mentioning
##   "overlapping clauses".
## - P_neg4 (nested overlap): generate a constructor pattern and a distinct,
##   more specific pattern inside its Nat/ListN payload; elaboration must
##   report the overlap before later coverage checking.
##
## Each property asserts the *error fragment*, not the full message, so the
## suite survives message rewording as long as the defect category is named.
##
## Value category: (d) improved certainty about "proved"/certified conclusions
## — extensional evidence that the checkers reject what they must reject,
##   over nested patterns where the hand-written examples don't reach.
##
## Run: nim c -r --hints:off --path:src --path:src/eponym \
##        --path:src/experimental --path:src/experimental/relational --path:src/experimental/staging --path:tests \
##        tests/pbt_clause_matrix_neg.nim
## Fixed seed 424242 in CI (change Seed locally for fresh fuzzing).

import falsify
import pbt_clause_matrix  # reuse the exported generators (expandPat, renderPat, Prelude, ...)
import elab
import strutils
import sequtils

const Seed = 424242'u64
const CasesPerProp = 100

# --- negative-case generators -------------------------------------------------

type NegCase = object
  src: string
  frag: string  # expected ElabError message fragment
  shape: string

proc `$`(c: NegCase): string = c.src

proc genRows(r: var Rng, ty: string): seq[Row] =
  ## An exhaustive, redundancy-free, disjoint-by-construction single-column
  ## matrix over `ty` (never the degenerate single catch-all).
  var ns = 0
  r.expandPat(ty, 0, 2, ns)
    .mapIt(Row(pats: @[it], rhsTrue: r.genBool()))

proc renderRows(rows: seq[Row]): string =
  result = ""
  for row in rows:
    result &= "| " & renderPat(row.pats[0]) & " = " &
      (if row.rhsTrue: "true" else: "false") & "\n"

proc genDropCase(r: var Rng): NegCase =
  ## Drop one constructor-headed row from an exhaustive matrix: the remaining
  ## matrix must fail coverage.
  let ty = DataTypes[r.below(DataTypes.len)]
  let rows = r.genRows(ty)
  doAssert rows.len >= 2, "expandPat always partitions into >= 2 rows"
  let drop = r.below(rows.len)
  var src = Prelude
  src &= "def f : " & ty & " -> Bool\n"
  for ri, row in rows:
    if ri != drop:
      src &= "| " & renderPat(row.pats[0]) & " = " &
        (if row.rhsTrue: "true" else: "false") & "\n"
  NegCase(src: src, frag: "missing case for constructor")

proc genCatchAllCase(r: var Rng): NegCase =
  ## Append a wildcard catch-all after an exhaustive matrix: the catch-all is
  ## dead and must be flagged redundant.
  let ty = DataTypes[r.below(DataTypes.len)]
  let rows = r.genRows(ty)
  var src = Prelude
  src &= "def f : " & ty & " -> Bool\n"
  src &= renderRows(rows)
  src &= "| _ = true\n"
  NegCase(src: src, frag: "redundant clause")

proc genDupCase(r: var Rng): NegCase =
  ## Duplicate an existing row at the end: the duplicate is subsumed by the
  ## earlier identical row and must be flagged overlapping.
  let ty = DataTypes[r.below(DataTypes.len)]
  let rows = r.genRows(ty)
  let dup = rows[r.below(rows.len)]
  var src = Prelude
  src &= "def f : " & ty & " -> Bool\n"
  src &= renderRows(rows)
  src &= "| " & renderPat(dup.pats[0]) & " = " &
    (if not dup.rhsTrue: "true" else: "false") & "\n"
  NegCase(src: src, frag: "overlapping clauses")

proc genNestedOverlapCase(r: var Rng): NegCase =
  ## Generate two different patterns where the second is a strict subset of
  ## the first. Unlike a duplicated row or trailing catch-all, these cases
  ## exercise overlap inside a constructor argument.
  let shape = ["nat-suc", "list-head", "list-tail"][r.below(3)]
  var broad, specific, ty: string
  case shape
  of "nat-suc":
    ty = "Nat"
    broad = "(suc _)"
    specific = if r.genBool: "(suc zero)" else: "(suc (suc _))"
  of "list-head":
    ty = "ListN"
    broad = "(lcons _ _)"
    specific = if r.genBool: "(lcons zero _)" else: "(lcons (suc _) _)"
  else:
    ty = "ListN"
    broad = "(lcons _ _)"
    specific = if r.genBool: "(lcons _ lnil)" else: "(lcons _ (lcons _ _))"
  var src = Prelude
  src &= "def f : " & ty & " -> Bool\n"
  src &= "| " & broad & " = true\n"
  src &= "| " & specific & " = false\n"
  NegCase(src: src, frag: "overlapping clauses", shape: shape)

proc classifyOverlap(c: NegCase): seq[string] = @[c.shape]

# --- property -----------------------------------------------------------------

proc checkNeg(c: NegCase): bool =
  ## Elaboration must raise an ElabError whose message names the defect.
  try:
    discard elabCheck(c.src)
  except ElabError as e:
    if c.frag in e.msg:
      return true
    echo "FAIL: expected fragment '", c.frag, "' in error message: ", e.msg
    echo c.src
    return false
  echo "FAIL: expected ElabError containing '", c.frag,
    "', but elaboration succeeded"
  echo c.src
  false

# --- main ---------------------------------------------------------------------

var r = initRng(Seed)
let ok1 = forAll("clause-matrix negative: dropped row fails coverage", r,
                 CasesPerProp, genDropCase, checkNeg)
let ok2 = forAll("clause-matrix negative: catch-all is redundant", r,
                 CasesPerProp, genCatchAllCase, checkNeg)
let ok3 = forAll("clause-matrix negative: duplicated row overlaps", r,
                 CasesPerProp, genDupCase, checkNeg)
let ok4 = forAll("clause-matrix negative: nested patterns overlap", r,
                 CasesPerProp, genNestedOverlapCase, checkNeg,
                 classify = classifyOverlap,
                 cover = @[("nat-suc", 10.0), ("list-head", 10.0),
                           ("list-tail", 10.0)])
if not (ok1 and ok2 and ok3 and ok4):
  quit(1)
echo "all clause-matrix negative properties passed"
