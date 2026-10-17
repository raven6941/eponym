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
  nimFile, "constEndoBody", "lam f. lam g. _", requireComplete = true)
check(not rejectedGive.ok and "give rejected" in rejectedGive.why,
  "Give rejects a candidate that leaves a residual hole")
sidecar = readShedSidecar(sidecarPath(nimFile))
check(sidecar[0].status == ssYellow and sidecar[0].genSrc == beforeRejectedRefine,
  "rejected Give leaves the sidecar unchanged")

let partial = refineShed(nimFile, "constEndoBody", "lam f. lam g. _")
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
      discard elabCheck("proc constEndo (A : ?) : " &
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

let split = refineShed(natFile, "sumBody", "add _ _")
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
  "case-split returns one named shed per Nat constructor")
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

removeDir(scratch)
echo "--- shed refine round-trip contract passed ---"
