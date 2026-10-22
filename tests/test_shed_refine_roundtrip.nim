## The refine contract across the real Nim macro boundary.
##
## A partial refinement must survive the entire editor loop:
## compile shedsBlock -> refine the generated Eponym hole -> splice the
## returned Nim term -> compile shedsBlock again -> address the residual
## goal by its shed name -> finish the proof -> compile strictly.
##
## Run: nim c -r --hints:off --path:src --path:src/eponym \
##   tests/test_shed_refine_roundtrip.nim
import os
import osproc
import sequtils
import strutils
import elab
import lsp
import sheds
import shed_layout

const RepoRoot = parentDir(parentDir(currentSourcePath()))

proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    echo "FAIL: ", label
    quit(1)

proc compileFixture(path, scratch: string): tuple[ok: bool, output: string] =
  let nim = findExe("nim")
  if nim.len == 0: return (false, "nim not on PATH")
  let cmd = quoteShell(nim) & " c --hints:off" &
    " --nimcache:" & quoteShell(scratch / "nimcache") &
    " --path:" & quoteShell(RepoRoot / "src") &
    " --path:" & quoteShell(RepoRoot / "src" / "eponym") &
    " -o:" & quoteShell(scratch / "fixture") & " " & quoteShell(path)
  let (output, code) = execCmdEx(cmd)
  (code == 0, output & "\n[nim exit code: " & $code & "]")

proc spliceShed(src: string, line1, col1: int, term: string): string =
  let lines = src.splitLines()
  let line = lines[line1 - 1]
  let start = col1 - 1
  var endCol = -1
  if start + 1 < line.len and line[start] == '!' and line[start + 1] == '[':
    var depth = 0
    for i in start ..< line.len:
      if line[i] == '[': inc depth
      elif line[i] == ']':
        dec depth
        if depth == 0:
          endCol = i + 1
          break
  elif line[start ..< min(start + 9, line.len)] == "shedHole(":
    let close = line.find(')', start)
    if close >= 0: endCol = close + 1
  doAssert endCol >= 0, "unclosed shed marker"
  var updated = lines
  updated[line1 - 1] = line[0 ..< col1 - 1] & term & line[endCol .. ^1]
  updated.join("\n")

let scratch = getTempDir() / "eponym_shed_refine_roundtrip"
removeDir(scratch)
createDir(scratch)
let nimFile = scratch / "const_endo.nim"
let nimV0 = """import sheds_mac

shedsBlock:
  proc constEndo(A: Univ): Pi(f: A, g: A, A) = ![constEndoBody]
"""
writeFile(nimFile, nimV0)

var compiled = compileFixture(nimFile, scratch)
check(compiled.ok, "initial Nim fixture compiles and writes a sidecar")
if not compiled.ok: echo compiled.output

var sidecar = readShedSidecar(sidecarPath(nimFile))
check(sidecar.len == 1 and sidecar[0].name == "constEndoBody" and
      sidecar[0].status == ssYellow and sidecar[0].goalPi.len == 3,
  "macro sidecar records the named Pi goal")
check(nimV0.splitLines()[sidecar[0].nimLine - 1].find("![constEndoBody]") + 1 ==
      sidecar[0].nimCol,
  "macro sidecar records the exact 1-based marker column")
let beforeRejectedRefine = sidecar[0].genSrc
let rejected = refineShed(nimFile, "constEndoBody", "A")
check(not rejected.ok and "refine rejected:" in rejected.why,
  "a term with the wrong type is rejected")
sidecar = readShedSidecar(sidecarPath(nimFile))
check(sidecar[0].status == ssYellow and sidecar[0].genSrc == beforeRejectedRefine,
  "rejected refinement leaves the sidecar unchanged")
let rejectedGive = refineShed(
  nimFile, "constEndoBody", "lam f. lam g. ?", requireComplete = true)
check(not rejectedGive.ok and "give rejected" in rejectedGive.why,
  "Give rejects a candidate that leaves a residual hole")
sidecar = readShedSidecar(sidecarPath(nimFile))
check(sidecar[0].status == ssYellow and sidecar[0].genSrc == beforeRejectedRefine,
  "rejected Give leaves the sidecar unchanged")

let partial = refineShed(nimFile, "constEndoBody", "lam f. lam g. ?")
check(partial.ok and partial.status == "yellow" and partial.yellowCount == 1,
  "a well-typed partial lambda is accepted with one open goal")
check(partial.term == "lam f. lam g. shedHole(constEndoBody)",
  "the returned Nim splice names the residual hole")
if partial.ok:
  let nimV1 = spliceShed(nimV0, partial.nimLine, partial.nimCol, partial.term)
  writeFile(nimFile, nimV1)
  compiled = compileFixture(nimFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok, "the partial refinement survives Nim source recompilation")

  sidecar = readShedSidecar(sidecarPath(nimFile))
  check(sidecar.len == 1 and sidecar[0].name == "constEndoBody" and
        sidecar[0].status == ssYellow and sidecar[0].goal == "A" and
        "f : A" in sidecar[0].ctx and "g : A" in sidecar[0].ctx,
    "recompiled source preserves the inner goal and both binders")

  let completed = refineShed(
    nimFile, "constEndoBody", "f", requireComplete = true)
  check(completed.ok and completed.status == "white" and
        completed.yellowCount == 0,
    "a complete, well-typed lambda closes the shed: " &
      (if completed.ok: completed.status & ", " & $completed.yellowCount & " yellow"
       else: completed.why))
  if completed.ok:
    let nimV2 = spliceShed(nimV1, completed.nimLine, completed.nimCol,
                           completed.term)
    writeFile(nimFile, nimV2)
    compiled = compileFixture(nimFile, scratch)
    check(compiled.ok, "the completed refinement compiles as Nim")
    if not compiled.ok: echo compiled.output
    sidecar = readShedSidecar(sidecarPath(nimFile))
    check(sidecar.len == 0,
      "a fully refined source no longer emits an open shed")
    try:
      discard elabCheck("proc constEndo (A : Type 0) : " &
        "Pi (f : A). Pi (g : A). A = lam f. lam g. f\n")
      check(true, "completed generated Eponym source passes strict checking")
    except CatchableError as e:
      check(false, "completed generated Eponym source checks: " & e.msg)

# Two holes on one generated-source line must get distinct names and exact
# positions. Filling either child must not accidentally fill its sibling.
let natFile = scratch / "two_holes.nim"
let natImport = (RepoRoot / "lib" / "nat.ep").replace("\\", "/")
let natV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & natImport & "\"\n" &
  "  proc addPair(n: Nat): Nat = ![sumBody]\n"
writeFile(natFile, natV0)
compiled = compileFixture(natFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "multiple-hole fixture compiles")

let split = refineShed(natFile, "sumBody", "add ? ?")
check(split.ok and split.status == "yellow" and split.yellowCount == 2,
  "refinement records both residual application goals")
check(split.term == "add shedHole(sumBody) shedHole(sumBody_1)",
  "multiple residual holes get distinct source markers")
if split.ok:
  let natV1 = spliceShed(natV0, split.nimLine, split.nimCol, split.term)
  writeFile(natFile, natV1)
  compiled = compileFixture(natFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok, "both named residual holes survive source recompilation")
  var natSheds = readShedSidecar(sidecarPath(natFile))
  check(natSheds.len == 2 and natSheds[0].name == "sumBody" and
        natSheds[1].name == "sumBody_1" and
        natSheds[0].holeCol != natSheds[1].holeCol and
        natSheds[0].goal == "Nat" and natSheds[1].goal == "Nat",
    "same-line residual goals have distinct positions and correct Nat goals")

  let second = refineShed(natFile, "sumBody_1", "n")
  check(second.ok and second.status == "white" and second.yellowCount == 1,
    "the second same-line residual goal can be refined independently: " &
      (if second.ok: second.status & ", " & $second.yellowCount & " yellow"
       else: second.why))
  if second.ok:
    let natV2 = spliceShed(natV1, second.nimLine, second.nimCol, second.term)
    writeFile(natFile, natV2)
    compiled = compileFixture(natFile, scratch)
    if not compiled.ok: echo compiled.output
    check(compiled.ok, "one filled child and its sibling survive recompilation")
    natSheds = readShedSidecar(sidecarPath(natFile))
    check(natSheds.len == 1 and natSheds[0].name == "sumBody" and
          natSheds[0].status == ssYellow,
      "recompilation retains only the unfilled sibling")
    let first = refineShed(natFile, "sumBody", "n")
    check(first.ok and first.status == "white" and first.yellowCount == 0,
      "the remaining same-line goal closes independently")

# A case-split introduces sub-sheds. Verify the extension's required next
# step: source splice + macro recompilation must give every child a usable
# goal/context/layout, then each child can be completed through refineShed.
let caseFile = scratch / "case_split.nim"
let boolImport = (RepoRoot / "lib" / "bool.ep").replace("\\", "/")
let caseV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & natImport & "\"\n" &
  "  import \"" & boolImport & "\"\n" &
  "  proc isZero(n: Nat): Bool = ![isZeroBody]\n"
writeFile(caseFile, caseV0)
compiled = compileFixture(caseFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "case-split fixture compiles with an initial shed")

let cases = caseSplitShed(caseFile, "isZeroBody", "n")
check(cases.ok and cases.subSheds.len == 2,
  "case-split returns one named shed per Nat constructor: " &
    (if cases.ok: cases.term else: cases.why))
if cases.ok:
  let caseV1 = spliceShed(caseV0, cases.nimLine, cases.nimCol, cases.term)
  writeFile(caseFile, caseV1)
  compiled = compileFixture(caseFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok, "case-split source splice recompiles")
  var caseSheds = readShedSidecar(sidecarPath(caseFile))
  check(caseSheds.len == 2 and
        caseSheds[0].name == cases.subSheds[0] and
        caseSheds[1].name == cases.subSheds[1] and
        caseSheds.allIt(it.status == ssYellow and it.holeIdx >= 0 and
                        it.goal.len > 0 and it.genSrc.len > 0),
    "recompiled case children have named, open goals and generated source")
  check(caseSheds[1].goalPi.anyIt(it.startsWith("ih0 : ")),
    "successor case goal shows its typed induction hypothesis: " &
      $caseSheds[1].goalPi)
  for child in caseSheds:
    let box = layoutShed(child)
    check(allHoleIds(box).len > 0,
      "case child " & child.name & " has a renderable hole layout")

  let zero = refineShed(caseFile, cases.subSheds[0], "false", true)
  check(zero.ok and zero.status == "white" and zero.yellowCount == 1,
    "zero case can be independently completed with Give")
  if zero.ok:
    let caseV2 = spliceShed(caseV1, zero.nimLine, zero.nimCol, zero.term)
    writeFile(caseFile, caseV2)
    compiled = compileFixture(caseFile, scratch)
    if not compiled.ok: echo compiled.output
    check(compiled.ok, "completed zero case recompiles")
    caseSheds = readShedSidecar(sidecarPath(caseFile))
    check(caseSheds.len == 1 and caseSheds[0].name == cases.subSheds[1],
      "sidecar retains only the unfilled successor case")
    let suc = refineShed(
      caseFile, cases.subSheds[1], "lam p. lam ih. false", true)
    check(suc.ok and suc.status == "white" and suc.yellowCount == 0,
      "successor case can be independently completed with its IH in scope")

# Parameterized, non-indexed datatypes can replay their type parameters in
# the eliminator and motive. This exercises the real Nim splice and macro
# recompilation, not only the LSP's generated text.
let listFile = scratch / "list_case_split.nim"
let listImport = (RepoRoot / "lib" / "list.ep").replace("\\", "/")
let listV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & listImport & "\"\n" &
  "  proc listLength(xs: List[Nat]): Nat = ![listLengthBody]\n"
writeFile(listFile, listV0)
compiled = compileFixture(listFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "parameterized List fixture compiles with an initial shed")

let listCases = caseSplitShed(listFile, "listLengthBody", "xs")
check(listCases.ok and listCases.subSheds.len == 2,
  "case-split accepts a parameterized, non-indexed List")
check(listCases.term ==
      "listElim[Nat](lam(u, List[Nat], Nat), " &
      "![listLengthBody_nil], ![listLengthBody_cons], xs)",
  "case-split replays List's parameter in both eliminator and motive")
if listCases.ok:
  let listV1 = spliceShed(listV0, listCases.nimLine, listCases.nimCol,
                          listCases.term)
  writeFile(listFile, listV1)
  compiled = compileFixture(listFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok, "parameterized case-split splice recompiles")
  let listSheds = readShedSidecar(sidecarPath(listFile))
  check(listSheds.len == 2 and
        listSheds.allIt(it.status == ssYellow) and
        listSheds.anyIt(it.name == listCases.subSheds[0] and it.goal == "Nat"),
    "parameterized cases retain their typed goals")
  check(listSheds.anyIt(it.name == listCases.subSheds[1] and
                        it.goalPi.anyIt(it.startsWith("x : Nat"))) and
        listSheds.anyIt(it.name == listCases.subSheds[1] and
                        it.goalPi.anyIt(it.startsWith("ih0 : (L"))),
    "cons case exposes the element and typed induction hypothesis")

# A parameter supplied by a generic Eponym binder must retain its local name
# when the generated type argument is spliced back into Nim syntax.
let genericListFile = scratch / "generic_list_case_split.nim"
let genericListV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & listImport & "\"\n" &
  "  proc inspectList[A: Univ](xs: List[A]): Nat = ![inspectListBody]\n"
writeFile(genericListFile, genericListV0)
compiled = compileFixture(genericListFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "generic List fixture compiles with an initial shed")
let genericListCases = caseSplitShed(
  genericListFile, "inspectListBody", "xs")
check(genericListCases.ok and genericListCases.term.startsWith(
        "listElim[A](lam(u, List[A], Nat),"),
  "case-split retains a generic local datatype parameter")
if genericListCases.ok:
  let genericListV1 = spliceShed(
    genericListV0, genericListCases.nimLine, genericListCases.nimCol,
    genericListCases.term)
  writeFile(genericListFile, genericListV1)
  compiled = compileFixture(genericListFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok, "generic parameterized case-split splice recompiles")

# Indexed families need an index-generalized motive. Verify both a constant
# target and a target which depends directly on the index variable.
let vecFile = scratch / "indexed_case_split.nim"
let vecImport = (RepoRoot / "lib" / "vec.ep").replace("\\", "/")
let vecV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & vecImport & "\"\n" &
  "  proc vectorLength(n: Nat, xs: Vec[Nat, n]): Nat = ![vecBody]\n"
writeFile(vecFile, vecV0)
compiled = compileFixture(vecFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "indexed Vec fixture compiles with an initial shed")
let vecCases = caseSplitShed(vecFile, "vecBody", "xs")
check(vecCases.ok and vecCases.term.startsWith(
        "vecElim[Nat](lam(i0, Nat, lam(u, Vec[Nat, i0], Nat)),"),
  "indexed case-split generalizes the Vec index in its motive: " &
    (if vecCases.ok: vecCases.term else: vecCases.why))
if vecCases.ok:
  let vecV1 = spliceShed(vecV0, vecCases.nimLine, vecCases.nimCol,
                         vecCases.term)
  writeFile(vecFile, vecV1)
  compiled = compileFixture(vecFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok, "indexed case-split splice recompiles with typed branches")
  let vecSheds = readShedSidecar(sidecarPath(vecFile))
  check(vecSheds.len == 2 and
        vecSheds.allIt(it.status == ssYellow and it.goal.len > 0),
    "indexed case children retain open goals after recompilation")

let dependentVecFile = scratch / "dependent_index_case_split.nim"
let dependentVecV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & vecImport & "\"\n" &
  "  proc identityVector(n: Nat, xs: Vec[Nat, n]): Vec[Nat, n] = " &
  "![identityVectorBody]\n"
writeFile(dependentVecFile, dependentVecV0)
compiled = compileFixture(dependentVecFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "dependent indexed Vec fixture compiles with a shed")
let dependentVecCases = caseSplitShed(
  dependentVecFile, "identityVectorBody", "xs")
check(dependentVecCases.ok and "Vec[Nat, i0]" in dependentVecCases.term,
  "case-split substitutes the generalized index into a dependent target: " &
    (if dependentVecCases.ok: dependentVecCases.term else: dependentVecCases.why))
if dependentVecCases.ok:
  let dependentVecV1 = spliceShed(dependentVecV0,
    dependentVecCases.nimLine, dependentVecCases.nimCol,
    dependentVecCases.term)
  writeFile(dependentVecFile, dependentVecV1)
  compiled = compileFixture(dependentVecFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok,
    "dependent indexed case-split source recompiles with generalized goals")

# The index domain may depend on a datatype parameter. Recovering the domain
# from the registered telescope must substitute the actual local type binder.
let taggedEp = scratch / "tagged.ep"
let natEpImport = (RepoRoot / "lib" / "nat.ep").replace("\\", "/")
writeFile(taggedEp, "import \"" & natEpImport & "\"\n" & """data Tagged (A : Type 0) : Nat -> A -> Type 0 where
| tag (n : Nat) (x : A) : Tagged A n x
""")
let taggedFile = scratch / "parameter_index_case_split.nim"
let taggedEpImport = taggedEp.replace("\\", "/")
let taggedV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & taggedEpImport & "\"\n" &
  "  proc inspectTagged[A: Univ](n: Nat, a: A, " &
  "value: Tagged[A, n, a]): A = " &
  "![taggedBody]\n"
writeFile(taggedFile, taggedV0)
compiled = compileFixture(taggedFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "parameter-dependent index fixture compiles with a shed")
let taggedCases = caseSplitShed(taggedFile, "taggedBody", "value")
check(taggedCases.ok and "lam(i0, Nat, lam(i1, A," in taggedCases.term and
      "Tagged[A, i0, i1]" in taggedCases.term and
      ", n, a, value)" in taggedCases.term,
  "case-split handles multiple indices and a parameter-dependent index domain: " &
    (if taggedCases.ok: taggedCases.term else: taggedCases.why))
if taggedCases.ok:
  let taggedV1 = spliceShed(taggedV0, taggedCases.nimLine,
                            taggedCases.nimCol, taggedCases.term)
  writeFile(taggedFile, taggedV1)
  compiled = compileFixture(taggedFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok,
    "parameter-dependent indexed case-split splice recompiles")

# Exact compound index occurrences can be abstracted safely; the resulting
# motive is still validated by re-elaboration before a splice is returned.
let compoundVecFile = scratch / "compound_index_case_split.nim"
let compoundVecV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & vecImport & "\"\n" &
  "  proc identitySuccessor(n: Nat, xs: Vec[Nat, suc(n)]): " &
  "Vec[Nat, suc(n)] = ![compoundIndexBody]\n"
writeFile(compoundVecFile, compoundVecV0)
compiled = compileFixture(compoundVecFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "compound indexed Vec fixture compiles with a shed")
let compoundVecCases = caseSplitShed(
  compoundVecFile, "compoundIndexBody", "xs")
check(compoundVecCases.ok and
      "Vec[Nat, i0]" in compoundVecCases.term and
      compoundVecCases.term.endsWith(", suc(n), xs)"),
  "case-split abstracts an exact compound index occurrence: " &
    (if compoundVecCases.ok: compoundVecCases.term else: compoundVecCases.why))
if compoundVecCases.ok:
  let compoundVecV1 = spliceShed(compoundVecV0, compoundVecCases.nimLine,
                                 compoundVecCases.nimCol, compoundVecCases.term)
  writeFile(compoundVecFile, compoundVecV1)
  compiled = compileFixture(compoundVecFile, scratch)
  if not compiled.ok: echo compiled.output
  check(compiled.ok, "compound indexed case-split source recompiles")

# If the target depends on `n` independently of the actual index `suc(n)`, it
# remains tied to the outer context instead of being accidentally rewritten.
let unrelatedIndexFile = scratch / "unrelated_compound_index_case_split.nim"
let unrelatedIndexV0 = "import sheds_mac\n\nshedsBlock:\n" &
  "  import \"" & vecImport & "\"\n" &
  "  proc preserveContext(n: Nat, xs: Vec[Nat, suc(n)]): " &
  "Vec[Nat, n] = ![unrelatedIndexBody]\n"
writeFile(unrelatedIndexFile, unrelatedIndexV0)
compiled = compileFixture(unrelatedIndexFile, scratch)
if not compiled.ok: echo compiled.output
check(compiled.ok, "independent compound-index target fixture compiles")
let unrelatedIndexCases = caseSplitShed(
  unrelatedIndexFile, "unrelatedIndexBody", "xs")
check(unrelatedIndexCases.ok and "Vec[Nat, n]" in unrelatedIndexCases.term and
      "Vec[Nat, i0]" in unrelatedIndexCases.term,
  "case-split preserves unrelated context dependencies in the motive: " &
    (if unrelatedIndexCases.ok: unrelatedIndexCases.term
     else: unrelatedIndexCases.why))

removeDir(scratch)
echo "--- shed refine round-trip contract passed ---"
