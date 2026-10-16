## tests/pbt_clause_matrix.nim — Issue #163: differential property tests for the
## clause-matrix compiler (issue #78; the compiler is `compileMatrixNode` and
## friends in src/eponym/elab.nim).
##
## Property P1 (differential match semantics): for a randomly generated
## exhaustive, redundancy-free clause matrix over Nat / Bool / ListN —
## including nested constructor patterns, wildcard `_` and variable patterns,
## plus two-column Bool×Bool matches — the elaborated definition computes the
## same result as a naive first-match interpreter of the same matrix applied
## to random scrutinee values.
##
## Generation is exhaustive-by-construction: `expandPat` recursively partitions
## a datatype's value space (a constructor argument is either left as a
## variable/wildcard or itself partitioned), so the compiler's coverage and
## redundancy checkers must accept every generated matrix — a generator bug
## would surface as an elaboration failure, which `forAll` reports as FAIL.
## The naive matcher is structural first-match-wins over the same pattern
## trees that are rendered to surface syntax, so any disagreement is a real
## miscompilation (or a semantic question worth a decisions.org entry).
##
## Value category: (d) improved certainty about "proved"/certified conclusions
## — extensional evidence that the matrix compiler agrees with the obvious
## reference semantics on nested patterns, catch-alls, and multi-column splits.
##
## Run: nim c -r --hints:off --path:src --path:src/eponym \
##        --path:src/experimental --path:src/experimental/relational --path:src/experimental/staging tests/pbt_clause_matrix.nim
## Fixed seed 424242 in CI (change Seed locally for fresh fuzzing).

import falsify
import elab
import eponym_init
import sequtils
import strutils

const Seed = 424242'u64
const CasesSingle = 120
const CasesMulti = 60

# --- datatype descriptors ---------------------------------------------------

type CtorSig = object
  name: string
  argTys: seq[string]

const
  NatCtors = @[CtorSig(name: "zero", argTys: @[]),
               CtorSig(name: "suc", argTys: @["Nat"])]
  BoolCtors = @[CtorSig(name: "true", argTys: @[]),
                CtorSig(name: "false", argTys: @[])]
  ListNCtors = @[CtorSig(name: "lnil", argTys: @[]),
                 CtorSig(name: "lcons", argTys: @["Nat", "ListN"])]

proc ctorsOf(ty: string): seq[CtorSig] =
  case ty
  of "Nat": NatCtors
  of "Bool": BoolCtors
  of "ListN": ListNCtors
  else:
    assert false, "unknown type " & ty
    @[]

const DataTypes* = ["Nat", "Bool", "ListN"]

# --- patterns and values ----------------------------------------------------

type
  PatKind* = enum pkWild, pkVar, pkCtor
  Pat* = object
    case kind*: PatKind
    of pkWild: discard
    of pkVar: vname*: string
    of pkCtor:
      ctor*: string
      args*: seq[Pat]

type
  ValKind = enum vkNat, vkBool, vkList
  Val = object
    case kind: ValKind
    of vkNat: n: int
    of vkBool: b: bool
    of vkList: elems: seq[int]

type
  Row* = object
    pats*: seq[Pat]   # one pattern per column
    rhsTrue*: bool    # RHS is the `true` or `false` constructor

type Case = object
  src: string
  probes: seq[string]
  expected: seq[bool]  # naive first-match RHS per probe
  maxPatDepth: int    # max constructor-nesting depth over all row patterns
  numRows: int        # 1 ⟺ degenerate catch-all matrix

proc patDepth(p: Pat): int =
  ## Constructor-nesting depth of a pattern (0 = flat/wildcard).
  if p.kind != pkCtor or p.args.len == 0: 0
  else: 1 + max(p.args.mapIt(patDepth(it)))

proc `$`(c: Case): string = c.src

# --- rendering ----------------------------------------------------------------

proc renderPat*(p: Pat): string =
  case p.kind
  of pkWild: "_"
  of pkVar: p.vname
  of pkCtor:
    if p.args.len == 0: p.ctor
    else: "(" & p.ctor & " " & p.args.mapIt(renderPat(it)).join(" ") & ")"

proc renderVal(v: Val): string =
  case v.kind
  of vkNat:
    result = "zero"
    for _ in 1 .. v.n: result = "(suc " & result & ")"
  of vkBool:
    result = if v.b: "true" else: "false"
  of vkList:
    result = "lnil"
    for i in countdown(v.elems.high, 0):
      result = "(lcons " & renderVal(Val(kind: vkNat, n: v.elems[i])) &
        " " & result & ")"

const Prelude* = """data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Bool : ? where
| true : Bool
| false : Bool
data ListN : ? where
| lnil : ListN
| lcons (x : Nat) (xs : ListN) : ListN
"""

# --- naive reference matcher --------------------------------------------------

proc matches(p: Pat, v: Val): bool =
  ## Structural first-match test of one pattern against one value.
  case p.kind
  of pkWild, pkVar: true
  of pkCtor:
    case v.kind
    of vkNat:
      if p.ctor == "zero": p.args.len == 0 and v.n == 0
      elif p.ctor == "suc":
        p.args.len == 1 and v.n > 0 and
          matches(p.args[0], Val(kind: vkNat, n: v.n - 1))
      else: false
    of vkBool:
      p.args.len == 0 and
        ((p.ctor == "true" and v.b) or (p.ctor == "false" and not v.b))
    of vkList:
      if p.ctor == "lnil": p.args.len == 0 and v.elems.len == 0
      elif p.ctor == "lcons":
        p.args.len == 2 and v.elems.len > 0 and
          matches(p.args[0], Val(kind: vkNat, n: v.elems[0])) and
          matches(p.args[1], Val(kind: vkList, elems: v.elems[1 .. ^1]))
      else: false

proc firstMatch(rows: seq[Row], vals: seq[Val]): int =
  ## Index of the first row whose patterns all match; -1 if none.
  for ri, row in rows:
    var ok = true
    for ci in 0 ..< vals.len:
      if not matches(row.pats[ci], vals[ci]): ok = false; break
    if ok: return ri
  -1

# --- generators ---------------------------------------------------------------

proc shuffledIdx(r: var Rng, n: int): seq[int] =
  result = toSeq(0 ..< n)
  for i in countdown(n - 1, 1):
    let j = r.below(i + 1)
    swap(result[i], result[j])

proc freshVar(r: var Rng, ns: var int): Pat =
  inc ns
  Pat(kind: pkVar, vname: "v" & $ns)

proc wildOrVar*(r: var Rng, ns: var int): Pat =
  if r.below(4) == 0: Pat(kind: pkWild) else: r.freshVar(ns)

proc expandPat*(r: var Rng, ty: string, depth, maxDepth: int,
               ns: var int): seq[Pat] =
  ## Patterns that partition the whole value space of `ty`: exhaustive and
  ## pairwise disjoint by construction. A constructor's argument is either
  ## left as a wildcard/variable or itself recursively partitioned.
  result = @[]
  for ci in r.shuffledIdx(ctorsOf(ty).len):
    let c = ctorsOf(ty)[ci]
    if depth < maxDepth and c.argTys.len > 0 and r.below(2) == 0:
      let splittable = toSeq(0 ..< c.argTys.len)
        .filterIt(c.argTys[it] in DataTypes)
      if splittable.len > 0:
        let j = splittable[r.below(splittable.len)]
        for sub in r.expandPat(c.argTys[j], depth + 1, maxDepth, ns):
          var args = newSeq[Pat](c.argTys.len)
          for k in 0 ..< c.argTys.len:
            args[k] = if k == j: sub else: r.wildOrVar(ns)
          result.add(Pat(kind: pkCtor, ctor: c.name, args: args))
        continue
    var args = newSeq[Pat](c.argTys.len)
    for k in 0 ..< c.argTys.len:
      args[k] = r.wildOrVar(ns)
    result.add(Pat(kind: pkCtor, ctor: c.name, args: args))

proc genVal(r: var Rng, ty: string): Val =
  case ty
  of "Nat": Val(kind: vkNat, n: r.below(5))
  of "Bool": Val(kind: vkBool, b: r.genBool())
  of "ListN":
    let n = r.below(4)
    var e = newSeq[int](n)
    for i in 0 ..< n: e[i] = r.below(3)
    Val(kind: vkList, elems: e)
  else:
    assert false, "unknown type " & ty
    Val(kind: vkNat, n: 0)

proc genSingleCase(r: var Rng): Case =
  ## One-column function `f : T -> Bool` with a generated matrix.
  let ty = DataTypes[r.below(DataTypes.len)]
  var ns = 0
  var rows: seq[Row]
  if r.below(6) == 0:
    # degenerate catch-all matrix: a single wildcard/variable row
    rows = @[Row(pats: @[r.wildOrVar(ns)], rhsTrue: r.genBool())]
  else:
    rows = r.expandPat(ty, 0, 2, ns)
      .mapIt(Row(pats: @[it], rhsTrue: r.genBool()))
  let nProbes = 3 + r.below(4)
  var src = Prelude
  src &= "def f : " & ty & " -> Bool\n"
  for row in rows:
    src &= "| " & renderPat(row.pats[0]) & " = " &
      (if row.rhsTrue: "true" else: "false") & "\n"
  result = Case(src: "", probes: @[], expected: @[])
  for i in 0 ..< nProbes:
    let pv = r.genVal(ty)
    let pn = "probe" & $i
    src &= "proc " & pn & " : Bool = f " & renderVal(pv) & "\n"
    let idx = firstMatch(rows, @[pv])
    assert idx >= 0, "generated matrix not exhaustive"
    result.probes.add(pn)
    result.expected.add(rows[idx].rhsTrue)
  src &= "proc expTrue : Bool = true\nproc expFalse : Bool = false\n"
  result.src = src
  result.numRows = rows.len
  result.maxPatDepth = max(rows.mapIt(patDepth(it.pats[0])))

proc genTwoColCase(r: var Rng): Case =
  ## Two-column function `g : Bool -> Bool -> Bool`: exercises the
  ## multi-column split (first column with a constructor pattern splits).
  var ns = 0
  var rows: seq[Row] = @[]
  for b1 in r.shuffledIdx(2):
    let c1 = if b1 == 0: "true" else: "false"
    if r.below(3) == 0:
      rows.add(Row(pats: @[Pat(kind: pkCtor, ctor: c1, args: @[]),
                            r.wildOrVar(ns)],
                   rhsTrue: r.genBool()))
    else:
      for b2 in r.shuffledIdx(2):
        let c2 = if b2 == 0: "true" else: "false"
        rows.add(Row(pats: @[Pat(kind: pkCtor, ctor: c1, args: @[]),
                              Pat(kind: pkCtor, ctor: c2, args: @[])],
                     rhsTrue: r.genBool()))
  var src = Prelude
  src &= "def g : Bool -> Bool -> Bool\n"
  for row in rows:
    src &= "| " & renderPat(row.pats[0]) & " " & renderPat(row.pats[1]) &
      " = " & (if row.rhsTrue: "true" else: "false") & "\n"
  result = Case(src: "", probes: @[], expected: @[])
  for i in 0 ..< 4:
    let pvs = @[r.genVal("Bool"), r.genVal("Bool")]
    let pn = "probe" & $i
    src &= "proc " & pn & " : Bool = g " & renderVal(pvs[0]) & " " &
      renderVal(pvs[1]) & "\n"
    let idx = firstMatch(rows, pvs)
    assert idx >= 0, "generated matrix not exhaustive"
    result.probes.add(pn)
    result.expected.add(rows[idx].rhsTrue)
  src &= "proc expTrue : Bool = true\nproc expFalse : Bool = false\n"
  result.src = src
  result.numRows = rows.len
  result.maxPatDepth = max(rows.mapIt(max(it.pats.mapIt(patDepth(it)))))

# --- property -----------------------------------------------------------------

proc classifyMatrix(c: Case): seq[string] =
  ## Coverage tags for the matrix generators: nesting depth and
  ## catch-all vs partitioned. Pinned via `cover` so generator drift
  ## can't silently stop exercising nested patterns.
  ## Note: expandPat partitions by construction, so overlapping /
  ## redundant rows are not generatable (a deliberate design limit,
  ## not a coverage gap).
  result = @[]
  case c.maxPatDepth
  of 0: result.add("flat")
  of 1: result.add("nested-1")
  else: result.add("nested-2+")
  result.add(if c.numRows == 1: "catch-all" else: "partitioned")

proc checkCase(c: Case): bool =
  let defs = elabCheck(c.src)
  proc findDef(nm: string): ElabDef =
    for d in defs:
      if d.name == nm: return d
    assert false, "missing def " & nm
  let truId = eval(findDef("expTrue").tmTm, @[]).whnfRefId
  let flsId = eval(findDef("expFalse").tmTm, @[]).whnfRefId
  for i in 0 ..< c.probes.len:
    let v = eval(findDef(c.probes[i]).tmTm, @[])
    if v.whnfKind != wRef or v.whnfSpineLen != 0:
      echo "FAIL probe ", c.probes[i], ": not a nullary constructor value"
      echo c.src
      return false
    let want = if c.expected[i]: truId else: flsId
    if v.whnfRefId != want:
      echo "FAIL probe ", c.probes[i], ": compiled chose ",
        (if v.whnfRefId == truId: "true" else: "false"),
        ", naive first-match chose ",
        (if c.expected[i]: "true" else: "false")
      echo c.src
      return false
  true

# --- main ---------------------------------------------------------------------

when isMainModule:
  var r = initRng(Seed)
  let ok1 = forAll("clause-matrix single-column", r, CasesSingle,
                   genSingleCase, checkCase,
                   classify = classifyMatrix,
                   cover = @[("nested-1", 10.0), ("nested-2+", 15.0),
                             ("catch-all", 7.0)])
  let ok2 = forAll("clause-matrix two-column", r, CasesMulti,
                   genTwoColCase, checkCase,
                   classify = classifyMatrix,
                   cover = @[("partitioned", 50.0)])
  if not (ok1 and ok2):
    quit(1)
  echo "all clause-matrix differential properties passed"
