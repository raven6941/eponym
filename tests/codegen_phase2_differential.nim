## Shared differential-test driver for the Phase-2 representation backend
## (issue #330 v3: Vec/List/Option as `seq[int]`/`Option[int]`).
##
## A `differentialBlockRepr` macro elaborates a surface program at compile
## time with the runtime mappings described by `specs` and emits both the
## Phase-1 Value procs and the Phase-2 repr procs
## (`eponymCompiledRepr_<name>`). Test bodies check each repr proc against
## the interpreter (`callValueFuncDir`) and against its Phase-1 compiled
## twin, then benchmark per #19's framing (Phase 2 vs Phase 1's compiled
## output). The macro also emits `reprCompiledNames()` (which defs got a
## repr proc) and `testPostulateBindings()` (neutral bindings for the
## differential harness, as in the Phase-1 suite).
##
## `specs` is comma-separated `Name:kind` with kind in
## {int, vector, list, option}, e.g. "Int:int,Nat:int,Vec:vector".

import std/[tables, macros, strutils]
import eponym_init
import eponym_embed
import eponym_mac
import elab
import codegen

export tables, macros, strutils
export eponym_init, eponym_embed, eponym_mac, elab, codegen

macro differentialBlockRepr*(src: static string, srcFile: static string,
                             specs: static string): untyped =
  let checked = elabCheckDirStateAll(src, "")
  var userLines = initTable[string, int]()
  for d in checked.defs:
    userLines[d.name] = 1
  var mappings: seq[HostRuntimeType] = @[]
  for spec in specs.split(','):
    let parts = spec.split(':')
    doAssert parts.len == 2, "bad phase-2 mapping spec: '" & spec &
      "' (want Name:kind)"
    let eponymName = parts[0]
    let kind = parts[1]
    doAssert kind in ["int", "vector", "list", "option"],
      "bad phase-2 mapping kind: '" & kind & "'"
    let nimType = case kind
      of "int": ident"int"
      of "vector", "list": ident"seq"
      else: ident"Option"
    mappings.add(HostRuntimeType(eponymName: eponymName, nimType: nimType,
      isRuntimeVector: kind == "vector", isRuntimeList: kind == "list",
      isRuntimeOption: kind == "option",
      isRuntimeVariant: false, isRuntimeCodec: false,
      isGenericTypeWitnessable: true, encoder: nil, decoder: nil))
  let cgBlock = compileBlockProcs(checked.defs, checked.globals, "", src,
    srcFile, userLines, mappings)
  result = newStmtList()
  for p in cgBlock.procs:
    result.add(p)
    # Repr procs carry user source positions, like the Phase-1 procs.
    if p.kind == nnkProcDef and p[0].kind == nnkPostfix and
        ($p[0][1]).startsWith("eponymCompiledRepr_"):
      let li = lineInfoObj(p)
      if not li.filename.endsWith(".nim"):
        error("repr proc " & $p[0][1] &
          " missing user source position (got " & li.filename & ")")
  var names = newNimNode(nnkBracket)
  for name in cgBlock.compiledRepr.keys:
    names.add(newLit(name))
  result.add quote do:
    proc reprCompiledNames*(): seq[string] = @`names`
  var bindStmts = newStmtList()
  let bndSym = genSym(nskVar, "testBnd")
  bindStmts.add(newVarStmt(bndSym, newCall(bindSym"initRuntimeBindings")))
  for name, e in checked.globals.pairs:
    if e.tm != nil and e.tm.kind == tR and not e.tm.refIsDefn and
        not e.isElim and not e.isDataConstructor:
      let refIdLit = newLit(e.tm.refId)
      bindStmts.add(newTree(nnkAsgn,
        newTree(nnkBracketExpr, bndSym, refIdLit),
        newCall(bindSym"postulateValue", refIdLit,
          newCall(bindSym"initRuntimeBindings"))))
    elif e.isDataConstructor:
      let refIdLit = newLit(e.tm.refId)
      bindStmts.add(newTree(nnkAsgn,
        newTree(nnkBracketExpr, bndSym, refIdLit),
        newCall(bindSym"postulateValue", refIdLit,
          newCall(bindSym"initRuntimeBindings"))))
  bindStmts.add(bndSym)
  result.add quote do:
    proc testPostulateBindings*(): RuntimeBindings =
      `bindStmts`

proc expect*(ok: bool, message: string) =
  if not ok:
    quit("FAIL: " & message, 1)
  echo "ok: ", message
