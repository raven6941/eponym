## Issue #523: the boundary preview is tested as a report, not by compiling
## generated fixture code.  This keeps the diagnostic deterministic and makes
## fallback reasons visible in the blessed UX.
import std/[os, tables, macros, strutils, sets]
import eponym_embed
import elab
import codegen

type Case = tuple[file: string, defName: string]
const cases: seq[Case] = @[
  ("tests/boundary_preview_snapshots/cases/vec.ep", "f"),
  ("tests/boundary_preview_snapshots/cases/sig.ep", "pack"),
  ("tests/boundary_preview_snapshots/cases/opaque.ep", "keep"),
  ("tests/boundary_preview_snapshots/cases/bound_postulate.ep", "use"),
  ("tests/boundary_preview_snapshots/cases/higher_order.ep", "apply"),
  ("tests/boundary_preview_snapshots/cases/fallback.ep", "fallback")]
const snapDir = "tests/boundary_preview_snapshots/snapshots"

proc mappings(g: Globals): seq[HostRuntimeType] =
  for name in ["Int", "Nat"]:
    if name in g:
      result.add(HostRuntimeType(eponymName: name, nimType: ident"int"))
  if "Vec" in g:
    result.add(HostRuntimeType(eponymName: "Vec", nimType: ident"VecHost",
      isRuntimeVector: true))
  if "Box" in g:
    result.add(HostRuntimeType(eponymName: "Box", nimType: ident"BoxHost"))

proc snapPath(file: string): string = snapDir / file.splitFile().name & ".txt"

macro reportFor(file: static[string], defName: static[string]): untyped =
  let src = readFile(file)
  let checked = elabCheckDirStateAll(src, "")
  var d: ElabDef
  for candidate in checked.defs:
    if candidate.name == defName: d = candidate
  var lines = initTable[string, int]()
  for item in checked.defs: lines[item.name] = 1
  let reps = mappings(checked.globals)
  var bound: seq[PostulateReprBinding] = @[]
  if defName == "use":
    bound.add(PostulateReprBinding(postulateName: "step",
      implementation: ident"hostStep", argCount: 1,
      forwarderName: "eponymCompiledRepr_step"))
  let cg = compileBlockProcs(checked.defs, checked.globals, "", src, file,
    lines, reps, bound, allDefs = checked.allDefs)
  let entry = cg.report.getOrDefault(defName,
    CodegenReportEntry(tier: cgtInterpreter,
      reason: "definition was outside the generated runtime closure",
      slowPaths: @[]))
  var declared = initHashSet[string]()
  var postulateTrust = initTable[string, string]()
  if defName == "use":
    declared.incl("step")
    postulateTrust["step"] = "bindPostulate(step, hostStep): the Nim adapter behavior is trusted; " &
      "its signature is checked"
  let trustLines = definitionTrustLines(d, checked.globals, checked.allDefs,
    declared, postulateTrust, reps, initHashSet[string](), initHashSet[string]())
  newLit(boundaryPreviewReport(d, checked.globals, "", src, reps, entry.tier,
    entry.reason, checked.allDefs, trustLines))

const reportVec = reportFor("tests/boundary_preview_snapshots/cases/vec.ep", "f")
const reportSig = reportFor("tests/boundary_preview_snapshots/cases/sig.ep", "pack")
const reportOpaque = reportFor("tests/boundary_preview_snapshots/cases/opaque.ep", "keep")
const reportBound = reportFor("tests/boundary_preview_snapshots/cases/bound_postulate.ep", "use")
const reportHigher = reportFor("tests/boundary_preview_snapshots/cases/higher_order.ep", "apply")
const reportFallback = reportFor("tests/boundary_preview_snapshots/cases/fallback.ep", "fallback")

proc checkCase(c: Case, bless: bool): bool =
  let actual = (case c.defName
    of "f": reportVec
    of "pack": reportSig
    of "keep": reportOpaque
    of "use": reportBound
    of "apply": reportHigher
    else: reportFallback).strip()
  let sp = snapPath(c.file)
  if bless:
    writeFile(sp, actual & "\n")
    echo "blessed: ", c.file
    return true
  if not fileExists(sp):
    echo "FAIL: ", c.file, " — no snapshot; run with --bless"
    return false
  let expected = readFile(sp).strip()
  if actual != expected:
    echo "FAIL: ", c.file, " — boundary report changed (run --bless deliberately)"
    return false
  echo "ok: ", c.file
  true

let bless = "--bless" in commandLineParams()
var failed = 0
for c in cases:
  if not checkCase(c, bless): inc failed
echo "--- ", cases.len - failed, "/", cases.len, " boundary previews ok ---"
if failed > 0 and not bless: quit(1)
