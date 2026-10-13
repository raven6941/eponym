## Issue #62: differential audit harness for the independent kernel checker.
##
## For every .ep example accepted by the direct elaborator, each elaborated
## definition is re-checked by the independent audit kernel
## (src/eponym/kernel_check.nim), LCF-style: the elaborator is the untrusted
## producer, the kernel the auditor.
##
## Verdicts per definition:
##   PASS     -- kernel accepted an elaborator-accepted definition.
##   SKIP     -- kernel raised "out of kernel fragment" (tMeta/tInt/tNatLit/
##               tPrim, or a fully-applied eliminator needing iota): the
##               definition is not auditable by the v1 kernel, honestly
##               reported rather than counted as a pass.
##   DISAGREE -- elaborator accepted but kernel rejected: a soundness bug in
##               one of the two, which must be triaged explicitly. Any
##               disagreement fails this test (exit 1).
##
## Mirrors tests/run_examples.nim: the same .ep files are elaborated
## (fresh ModuleDriver per file, so `import` works), and *-neg.ep files
## must still be rejected by the elaborator.
import os
import strutils
import tables
import sequtils
import algorithm
import elab
import eponym_init  # TermKind (tR) for reading global reference nodes
import kernel_check

type
  Verdict = enum vPass, vSkip, vDisagree

proc buildKernelGlobals(globals: Globals,
                        defsByName: Table[string, ElabDef]): KernelGlobals =
  ## The kernel's table: every elaborator global becomes an entry; the
  ## cached Value fields in tR nodes are never consulted (kernel_check
  ## does not read them). Definitions get their elaborated bodies for
  ## delta-unfolding; postulates / constructors / eliminators keep
  ## def=nil and are treated as neutrals.
  for name, e in globals:
    if e.tm.kind == tR:
      result[e.tm.refId] = KGEntry(ty: e.ty, def: nil,
                                   isElim: e.isElim, elimNargs: e.elimNargs)
  for name, d in defsByName:
    if globals.hasKey(name) and globals[name].tm.kind == tR:
      result[globals[name].tm.refId].def = d.tmTm

proc auditFile(path: string,
               totals: var tuple[pass, skip, disagree, negOk: int]) =
  ## Elaborate one file and audit every definition it declares.
  let neg = path.endsWith("-neg.ep")
  var drv = initModuleDriver()
  var defs: seq[ElabDef]
  try:
    defs = drv.elabFile(path)
  except ElabError as e:
    if neg:
      inc totals.negOk
      return
    echo "ELAB-FAIL: ", path, " — ", e.msg.splitLines()[0]
    inc totals.disagree  # elaborator failure is a harness failure, not a skip
    return
  if neg:
    echo "NEG-FAIL: ", path, " — expected ElabError, elaborated cleanly"
    inc totals.disagree
    return
  var defsByName = initTable[string, ElabDef]()
  for d in defs:
    defsByName[d.name] = d
  # The kernel's table needs *every* global's body (including imports',
  # which elabFile omits from its return): drv.allDefs (issue #62) logs
  # them all. Only the file's own defs are audited here; imported defs
  # are audited when their own file is walked.
  let g = buildKernelGlobals(drv.globals, drv.allDefs)
  for name in sorted(toSeq(defsByName.keys)):
    let d = defsByName[name]
    if d.tmTm.isNil or d.tyTm.isNil:
      inc totals.skip
      echo "SKIP ", path, " :: ", name, ": no elaborated body/type"
      continue
    try:
      if kernelCheckDef(name, d.tmTm, d.tyTm, g):
        inc totals.pass
      else:
        inc totals.disagree
        echo "DISAGREE ", path, " :: ", name,
          ": kernel rejected an elaborator-accepted definition"
    except KernelError as e:
      inc totals.skip
      echo "SKIP ", path, " :: ", name, ": ", e.msg

var totals = (pass: 0, skip: 0, disagree: 0, negOk: 0)
var files = 0
for dir in ["lib", "examples", "examples/ep"]:
  for kind, path in walkDir(dir):
    if kind == pcFile and path.endsWith(".ep"):
      inc files
      auditFile(path, totals)

echo "--- kernel audit: ", files, " files, ",
  totals.pass, " passed, ",
  totals.skip, " skipped (out of kernel fragment), ",
  totals.disagree, " disagreements, ",
  totals.negOk, " negative tests rejected as expected ---"
if totals.disagree > 0:
  echo "AUDIT FAILED: disagreements need triage (issue #62)"
  quit(1)
echo "--- audit clean: no disagreements ---"
