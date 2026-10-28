Warning: truncated output (original token count: 62614)
Total output lines: 5516

## Experiment 2: the `ett` macro -- compile-time elaboration and checking.
##
## Deliberately thin (see decisions.org on Nimony/Nim 3): the parser and
## elaborator are plain Nim code in parse_surf and elab; the macro only feeds
## them a string literal and turns failures into compiler errors. No NimNode
## inspection, no hygiene tricks -- nothing that ties us to Nim 2's macro API.

import macros
import std/tables
import elab
import eponym_embed  # runtime wrapper helpers and adapter-shape validation
import eponym_init # opaque Value conversion helpers
import codegen     # issue #329: naive Value-level backend
import preterm
import parse_surf
import derive_repr  # issue #402: runtimeDerive block form
import sheds       # issue #478: shed rewriting, sidecar, semantic state
import usage_check # issue #478: hasUnresolvedMetas, checkUsage
import unify       # issue #478: zonk, unify for macro-time draft filling
import os  # issue #131: parentDir of the eponymBlock call site
import strutils
import sequtils
import sets
import std/algorithm
import std/options

template rawValue* {.pragma.}

type LegacyCallInfo = object
  explicitCount: int
  termCount: int
  applicationParamTypes: seq[string]
  termParamNames: seq[string]
  termParamDefaults: seq[NimNode]
  firstExplicitNat: bool
  requiresBrackets: bool

var legacyCallInfo {.compileTime.} = initTable[string, LegacyCallInfo]()
var legacyTypeFamilies {.compileTime.} = initHashSet[string]()
var legacyTypeNames {.compileTime.} = initHashSet[string]()
var scopedLegacyTypeNames {.compileTime.} = initHashSet[string]()
var legacyNatConstructors {.compileTime.} = initHashSet[string]()
var legacyNatFunctions {.compileTime.} = initHashSet[string]()
var scopedNatNames {.compileTime.} = initHashSet[string]()

# Issue #408: cross-block export registry. Maps `loc.source & "\x00" & name`
# to the procs an earlier eponymBlock in this compilation emitted for an
# import-origin definition, so later blocks reuse them via direct calls
# instead of re-emitting (which would be a redefinition error, since
# emitted proc names are deterministic in the definition name). Compile-time
# state, like the legacy* tables above: it lives for one Nim module's
# compilation, and macro expansions run in source order.
var crossBlockExports {.compileTime.} = initTable[string, CrossBlockExport]()

proc isLegacyTypeName(n: NimNode): bool =
  n.kind in {nnkIdent, nnkSym} and
    ($n in legacyTypeNames or $n in scopedLegacyTypeNames)

proc isLegacyNatExpr(n: NimNode): bool

proc isLegacyNatBranch(n: NimNode): bool =
  if n.kind == nnkStmtList:
    n.len == 1 and isLegacyNatExpr(n[0])
  else:
    isLegacyNatExpr(n)

proc isLegacyNatExpr(n: NimNode): bool =
  case n.kind
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    result = n.intVal >= 0
  of nnkIdent, nnkSym:
    result = $n in scopedNatNames
  of nnkPar:
    result = n.len == 1 and isLegacyNatExpr(n[0])
  of nnkIfExpr, nnkIfStmt:
    var hasCondition = false
    var hasElse = false
    result = true
    for branch in n:
      case branch.kind
      of nnkElifExpr, nnkElifBranch:
        hasCondition = true
        if branch.len != 2 or not isLegacyNatBranch(branch[1]):
          result = false
      of nnkElseExpr, nnkElse:
        hasElse = true
        if branch.len != 1 or not isLegacyNatBranch(branch[0]):
          result = false
      else:
        result = false
    result = result and hasCondition and hasElse
  of nnkCall, nnkCommand:
    result = n.len > 0 and n[0].kind in {nnkIdent, nnkSym} and
      ($n[0] in legacyNatConstructors or $n[0] in legacyNatFunctions)
  else:
    result = false

# --- eponymBlock: Nim-block syntax (no """) ---------------------------------
# Converts a block of (valid Nim) AST to Eponym source, elaborates it,
# and generates wrapper procs. Uses call syntax:
#   proc add42(n: Int): Int = addInt(n, 42)
#   postulate(Int, Univ)
#   data(Nat, Univ):
#     proc zero(): Nat
#     proc suc(n: Nat): Nat

proc callerDir(body: NimNode): string =
  ## Directory of the Nim file containing the macro call (Issue #131).
  ## instantiationInfo() is unreliable inside macros, so parse it out of
  ## lineInfo, which has the form /abs/path/file.nim(line, col).
  let li = lineInfo(body)
  let p = li.rfind('(')
  if p < 0:
    error("eponymBlock: cannot determine calling file", body)
  parentDir(li[0 ..< p])

proc binderName(n: NimNode): string =
  ## Param/binder name, unwrapping a quantity pragma: `ch {.linear.}` -> "ch".
  if n.kind == nnkPragmaExpr: $n[0]
  else: $n

proc warnCallStyleExplicitArgs(n: NimNode) =
  ## Reject legacy eponymBlock calls that put explicit type/index parameters
  ## in the same parentheses as value arguments.
  if n.kind != nnkCall or n.len < 2 or n[0].kind notin {nnkIdent, nnkSym}:
    return
  let head = $n[0]
  if head notin legacyCallInfo: return
  let info = legacyCallInfo[head]
  let supplied = n.len - 1
  if info.explicitCount == 0: return
  let beginsWithTypeName = isLegacyTypeName(n[1])
  let beginsWithNatIndex = info.firstExplicitNat and isLegacyNatExpr(n[1])
  if not info.requiresBrackets and supplied <= info.termCount and
      not beginsWithTypeName and not beginsWithNatIndex: return
  error("eponymBlock: call-style explicit parameters have been removed; " &
    "use square brackets for Eponym type/index arguments", n)

proc warnCallStyleTypeArgs(n: NimNode) =
  if n.kind == nnkCall and n.len > 1 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] in legacyTypeFamilies:
    error("eponymBlock: call-style explicit type/index arguments have been " &
      "removed; use square brackets", n)

proc nimFormalArgCount(formal: NimNode): int =
  if formal.kind != nnkFormalParams: return 0
  for i in 1 ..< formal.len:
    let param = formal[i]
    if param.kind == nnkIdentDefs:
      result += param.len - 2

proc nimFormalArgNames(formal: NimNode): seq[string] =
  if formal.kind != nnkFormalParams: return
  for i in 1 ..< formal.len:
    let param = formal[i]
    if param.kind != nnkIdentDefs: continue
    for j in 0 ..< param.len - 2:
      let name = if param[j].kind == nnkPragmaExpr: param[j][0] else: param[j]
      result.add(binderName(name))

proc nimFormalArgDefaults(formal: NimNode): seq[NimNode] =
  if formal.kind != nnkFormalParams: return
  for i in 1 ..< formal.len:
    let param = formal[i]
    if param.kind != nnkIdentDefs: continue
    for _ in 0 ..< param.len - 2:
      result.add(if param[^1].kind == nnkEmpty: nil
                 else: copyNimTree(param[^1]))

proc namedArgumentName(arg: NimNode): string =
  if arg.kind == nnkExprEqExpr and arg.len == 2 and
      arg[0].kind in {nnkIdent, nnkSym}:
    result = $arg[0]

proc orderCallArguments(args: seq[NimNode], names: seq[string],
    defaults: seq[NimNode], call: NimNode): seq[NimNode] =
  let hasNamed = args.anyIt(namedArgumentName(it).len > 0)
  if names.len == 0:
    if hasNamed:
      error("eponymBlock: named arguments need a known callable signature", call)
    return args
  if not hasNamed:
    result = args
    while result.len < names.len:
      let i = result.len
      if i >= defaults.len or defaults[i].isNil:
        error("eponymBlock: missing required argument for '" & names[i] & "'",
          call)
      result.add(copyNimTree(defaults[i]))
    return
  var ordered = newSeq[NimNode](names.len)
  var nextPositional = 0
  for arg in args:
    let name = namedArgumentName(arg)
    var index = -1
    if name.len > 0:
      for i, paramName in names:
        if paramName == name:
          index = i
          break
      if index < 0:
        error("eponymBlock: unknown named argument '" & name & "'", arg)
    else:
      while nextPositional < ordered.len and not ordered[nextPositional].isNil:
        inc nextPositional
      if nextPositional >= ordered.len:
        error("eponymBlock: too many arguments", call)
      index = nextPositional
      inc nextPositional
    if not ordered[index].isNil:
      error("eponymBlock: duplicate argument for '" & names[index] & "'", arg)
    ordered[index] = if name.len > 0: arg[1] else: arg
  for i, value in ordered:
    if value.isNil:
      if i < defaults.len and not defaults[i].isNil:
        result.add(copyNimTree(defaults[i]))
      else:
        error("eponymBlock: missing required argument for '" & names[i] & "'",
          call)
    else:
      result.add(value)

proc nimGenericParamCount(params: NimNode): int =
  if params.kind == nnkGenericParams:
    for param in params:
      if param.kind == nnkIdentDefs:
        result += param.len - 2

proc nimIndexArity(kind: NimNode): int =
  var current = kind
  while current.kind == nnkInfix and current.len == 3 and
      $current[0] == "->":
    inc result
    current = current[2]

proc registerLegacyInfo(name: string, explicitCount, termCount: int,
                        firstExplicitNat = false,
                        requiresBrackets = false,
                        applicationParamTypes: seq[string] = @[]) =
  legacyCallInfo[name] = LegacyCallInfo(explicitCount: explicitCount,
    termCount: termCount, firstExplicitNat: firstExplicitNat,
    requiresBrackets: requiresBrackets,
    applicationParamTypes: applicationParamTypes)

proc surfaceApplicationParamTypes(
    tele: seq[tuple[name: string, ty: PreTerm, impl: bool,
                    erased: bool, qty: Qty]]): seq[string] =
  ## Record the complete Eponym application telescope. Bracket application
  ## supplies a prefix of it, so literal disambiguation needs the domain type
  ## at each prefix position, including explicit data-index binders.
  for binder in tele:
    result.add($binder.ty)

proc firstSurfaceExplicitIsNat(tele: seq[tuple[name: string, ty: PreTerm,
    impl: bool, erased: bool, qty: Qty]]): bool =
  for binder in tele:
    if binder.impl or binder.ty.kind in {pkUniv, pkUnivN}:
      return binder.ty.kind == pkVar and binder.ty.name == "Nat"
    return false

proc surfaceExplicitCount(tele: seq[tuple[name: string, ty: PreTerm,
    impl: bool, erased: bool, qty: Qty]]): int =
  for binder in tele:
    if binder.impl or binder.ty.kind in {pkUniv, pkUnivN}:
      inc result

proc surfaceRequiresBrackets(tele: seq[tuple[name: string, ty: PreTerm,
    impl: bool, erased: bool, qty: Qty]]): bool =
  for binder in tele:
    if binder.impl: continue
    if binder.ty.kind in {pkUniv, pkUnivN}: return true

proc surfaceIndexArity(ty: PreTerm): int =
  var current = ty
  while not current.isNil and current.kind == pkPi:
    inc result
    current = current.c2

proc registerSurfaceLegacyInfo(source: string, path: string,
    seen: var HashSet[string]) =
  let normalized = normalizedPath(path)
  if normalized in seen or not fileExists(normalized): return
  seen.incl(normalized)
  let declarations = parseProgram(source)
  for declaration in declarations:
    case declaration.kind
    of dkDef:
      let explicitCount = surfaceExplicitCount(declaration.def.tele)
      registerLegacyInfo(declaration.def.name, explicitCount,
        declaration.def.tele.len - explicitCount,
        firstSurfaceExplicitIsNat(declaration.def.tele),
        surfaceRequiresBrackets(declaration.def.tele),
        surfaceApplicationParamTypes(declaration.def.tele))
      for binder in declaration.def.tele:
        if not binder.impl and binder.ty.kind notin {pkUniv, pkUnivN}:
          legacyCallInfo[declaration.def.name].termParamNames.add(binder.name)
          legacyCallInfo[declaration.def.name].termParamDefaults.add(nil)
      if declaration.def.retTy.kind == pkVar and
          declaration.def.retTy.name == "Nat":
        legacyNatFunctions.incl(declaration.def.name)
    of dkData:
      let familyParams = declaration.params.len
      legacyTypeNames.incl(declaration.dname)
      if declaration.dname == "Nat":
        for constructor in declaration.ctors:
          legacyNatConstructors.incl(constructor.name)
      if familyParams + surfaceIndexArity(declaration.indexTy) > 0:
        legacyTypeFamilies.incl(declaration.dname)
      for constructor in declaration.ctors:
        let extraImplicit = surfaceExplicitCount(constructor.tele)
        var applicationParamTypes: seq[string] = @[]
        for parameter in declaration.params:
          applicationParamTypes.add($parameter.ty)
        for binder in constructor.tele:
          applicationParamTypes.add($binder.ty)
        registerLegacyInfo(constructor.name, familyParams + extraImplicit,
          constructor.tele.len - extraImplicit,
          firstSurfaceExplicitIsNat(constructor.tele),
          familyParams > 0 or surfaceRequiresBrackets(constructor.tele),
          applicationParamTypes)
        for binder in constructor.tele:
          if not binder.impl and binder.ty.kind notin {pkUniv, pkUnivN}:
            legacyCallInfo[constructor.name].termParamNames.add(binder.name)
            legacyCallInfo[constructor.name].termParamDefaults.add(nil)
        if constructor.name == "nil":
          registerLegacyInfo("vecnil", familyParams + extraImplicit,
            constructor.tele.len - extraImplicit,
            applicationParamTypes = applicationParamTypes)
    of dkImport:
      let importedPath = resolveImportTarget(declaration.ipath,
        normalized.parentDir)
      if importedPath.len > 0:
        registerSurfaceLegacyInfo(readFile(importedPath), importedPath, seen)
    else:
      discard

proc registerNimLegacyInfo(body: NimNode, sourceDir: string) =
  legacyCallInfo.clear()
  legacyTypeFamilies.clear()
  legacyTypeNames.clear()
  scopedLegacyTypeNames.clear()
  legacyNatConstructors.clear()
  legacyNatFunctions.clear()
  scopedNatNames.clear()
  var seen = initHashSet[string]()
  for statement in body:
    case statement.kind
    of nnkProcDef:
      let genericCount = nimGenericParamCount(statement[2])
      let firstGenericIsNat = statement[2].kind == nnkGenericParams and
        statement[2].len > 0 and statement[2][0].kind == nnkIdentDefs and
        statement[2][0][^2].kind in {nnkIdent, nnkSym} and
        $statement[2][0][^2] == "Nat"
      var applicationParamTypes: seq[string] = @[]
      if statement[2].kind == nnkGenericParams:
        for genericParam in statement[2]:
          if genericParam.kind == nnkIdentDefs:
            for _ in 0 ..< genericParam.len - 2:
              applicationParamTypes.add(genericParam[^2].repr)
      if statement[3].kind == nnkFormalParams:
        for i in 1 ..< statement[3].len:
          let param = statement[3][i]
          if param.kind == nnkIdentDefs:
            for _ in 0 ..< param.len - 2:
              applicationParamTypes.add(param[^2].repr)
      registerLegacyInfo($statement[0], genericCount,
        nimFormalArgCount(statement[3]), firstGenericIsNat,
        genericCount > 0, applicationParamTypes)
      if $statement[0] in legacyCallInfo:
        legacyCallInfo[$statement[0]].termParamNames =
          nimFormalArgNames(statement[3])
        legacyCallInfo[$statement[0]].termParamDefaults =
          nimFormalArgDefaults(statement[3])
      if statement[3].kind == nnkFormalParams and statement[3].len > 0 and
          statement[3][0].kind in {nnkIdent, nnkSym} and
          $statement[3][0] == "Nat":
        legacyNatFunctions.incl($statement[0])
    of nnkCall:
      if statement.len > 0 and statement[0].kind == nnkIdent and
          $statement[0] == "data" and statement.len >= 4:
        var params: NimNode = nil
        var kind: NimNode
        var constructors: NimNode
        if statement[2].kind == nnkBracket:
          params = statement[2]
          kind = statement[3]
          if statement.len > 4: constructors = statement[4]
        else:
          kind = statement[2]
          if statement.len > 3: constructors = statement[3]
        let paramCount = if params.isNil: 0 else: params.len
        var familyParamTypes: seq[string] = @[]
        if not params.isNil:
          for param in params:
            if param.kind == nnkExprColonExpr and param.len == 2:
              familyParamTypes.add(param[1].repr)
            elif param.kind == nnkIdentDefs and param.len >= 3:
              for _ in 0 ..< param.len - 2:
                familyParamTypes.add(param[^2].repr)
        legacyTypeNames.incl($statement[1])
        if paramCount + nimIndexArity(kind) > 0:
          legacyTypeFamilies.incl($statement[1])
        if not constructors.isNil and constructors.kind == nnkStmtList:
          for constructor in constructors:
            if constructor.kind == nnkProcDef:
              let termCount = nimFormalArgCount(constructor[3])
              var applicationParamTypes = familyParamTypes
              if constructor[2].kind == nnkGenericParams:
                for genericParam in constructor[2]:
                  if genericParam.kind == nnkIdentDefs:
                    for _ in 0 ..< genericParam.len - 2:
                      applicationParamTypes.add(genericParam[^2].repr)
              if constructor[3].kind == nnkFormalParams:
                for i in 1 ..< constructor[3].len:
                  let param = constructor[3][i]
                  if param.kind == nnkIdentDefs:
                    for _ in 0 ..< param.len - 2:
                      applicationParamTypes.add(param[^2].repr)
              registerLegacyInfo($constructor[0], paramCount, termCount,
                requiresBrackets = paramCount > 0,
                applicationParamTypes = applicationParamTypes)
              if $constructor[0] in legacyCallInfo:
                legacyCallInfo[$constructor[0]].termParamNames =
                  nimFormalArgNames(constructor[3])
                legacyCallInfo[$constructor[0]].termParamDefaults =
                  nimFormalArgDefaults(constructor[3])
              if $statement[1] == "Nat":
                legacyNatConstructors.incl($constructor[0])
    of nnkImportStmt:
      for imported in statement:
        if imported.kind != nnkStrLit: continue
        let importedPath = resolveImportTarget(imported.strVal, sourceDir)
        if importedPath.len > 0:
          registerSurfaceLegacyInfo(readFile(importedPath), importedPath, seen)
    else:
      discard

proc qtyPrefix(n: NimNode): string =
  ## Eponym quantity prefix from a Nim param pragma:
  ## `ch {.linear.}` -> "1 ", `ch {.erased.}` -> "0 ",
  ## `ch {.qvar(q).}` -> "q " (quantity *variable* binder, issue #151/#66).
  if n.kind == nnkPragmaExpr and n.len == 2 and n[1].kind == nnkPragma:
    for pr in n[1]:
      case pr.kind
      of nnkIdent:
        case $pr
        of "linear": return "1 "
        of "erased": return "0 "
        else: error("eponymBlock: unknown quantity pragma: " & $pr &
                    " (want linear/erased or qvar(q))", pr)
      of nnkCall:
        if pr[0].kind == nnkIdent and $pr[0] == "qvar" and pr.len == 2 and
           pr[1].kind == nnkIdent:
          return $pr[1] & " "
        error("eponymBlock: unsupported param pragma (want linear/erased or qvar(q))", pr)
      else:
        error("eponymBlock: unsupported param pragma", pr)
    return ""
  return ""

proc nimExprToEponym(n: NimNode, strict = true): string
proc nimTypeToEponym(n: NimNode): string
proc isNilLiteralExpr(n: NimNode): bool
proc nilConstructorForType(typeNode: NimNode): string

proc lambdaBinderToEponym(n: NimNode): string =
  ## Convert one lambda binder from the Nim AST into the common surface form.
  var binder = n
  while binder.kind in {nnkPar, nnkTupleConstr} and binder.len == 1:
    binder = binder[0]
  if binder.kind == nnkExprColonExpr and binder.len == 2:
    let name = binder[0]
    return qtyPrefix(name) & binderName(name) & ": " &
           nimTypeToEponym(binder[1])
  if binder.kind in {nnkIdent, nnkSym, nnkPragmaExpr}:
    return qtyPrefix(binder) & binderName(binder)
  error("eponymBlock: lambda binders must be names, optionally annotated " &
        "with a type", binder)

proc isLambdaArrow(n: NimNode): bool =
  var node = n
  while node.kind in {nnkPar, nnkStmtListExpr} and node.len == 1:
    node = node[0]
  node.kind == nnkInfix and node.len == 3…52614 tokens truncated…:
      echo "[eponym codegen]   " & inst.postulateName & "[" &
        inst.typeArgNames.join(", ") & "] -> " & inst.procName
  var adapterSpecs: seq[RawValueAdapterSpec] = @[]
  for inst in rawValueInstantiations:
    adapterSpecs.add(RawValueAdapterSpec(postulateName: inst.postulateName,
      typeArgNames: inst.typeArgNames, key: inst.key,
      implementation: inst.implementation, procName: inst.procName,
      reprProcName: inst.reprProcName))
  var cgBlock = compileBlockProcs(codegenDefs, checkedGlobals, baseDir, src,
    cgLocFile, cgUserLines, runtimeTypes, postulateReprs, allDefs,
    adapterSpecs, crossBlockExports)

  # Issue #408: publish this block's compiled import-origin definitions
  # into the cross-block registry for later blocks in this compilation.
  # The repr tier is exported only when the definition's transitive
  # runtime closure references no postulate bound in this block — otherwise
  # a reusing block would silently inherit this block's host
  # implementation. The value tier is unconditional: its convention is
  # uniform and postulate refs resolve through the *caller's* bindings,
  # exactly like the slow path it replaces.
  var boundPostulateNames = initHashSet[string]()
  for b in bindings: boundPostulateNames.incl(b.postulateName)
  for d in codegenDefs:
    if d.loc.source.len == 0 or d.loc.source.startsWith("<eponymBlock>"):
      continue
    let info = cgBlock.exportInfo.getOrDefault(d.name)
    if info.valueProc == "" and info.reprProc == "": continue
    var valueProc = info.valueProc
    var reprProc = info.reprProc
    var sigSummary = info.sigSummary
    # Under requireCompiled the macro filters non-repr procs out of the
    # emitted output (interpreter-freedom), so a compiled-but-unemitted
    # value proc must not be advertised to later blocks.
    if requireCompiled: valueProc = ""
    if reprProc != "":
      var hitsBound = false
      for p in info.postulatesUsed:
        if p in boundPostulateNames: hitsBound = true; break
      if hitsBound:
        reprProc = ""
        sigSummary = ""
        var entry = cgBlock.report.getOrDefault(d.name)
        entry.reason &= "; repr tier not exported cross-block: transitive " &
          "closure references a postulate bound in this block"
        cgBlock.report[d.name] = entry
        when defined(eponymCodegenReport):
          echo "[eponym codegen] " & d.name &
            ": repr tier not exported cross-block — transitive closure " &
            "references a postulate bound in this block"
    if valueProc == "" and reprProc == "": continue
    crossBlockExports[info.origin & "\x00" & d.name] =
      CrossBlockExport(valueProc: valueProc, reprProc: reprProc,
                       sigSummary: sigSummary)

  if requireCompiled:
    for d in codegenDefs:
      let codegen = cgBlock.report.getOrDefault(d.name)
      if d.name notin cgBlock.compiledRepr:
        error("eponymBlock requireCompiled: definition '" & d.name &
          "' has no representation-compiled body: " & codegen.reason, body)
      if codegen.slowPaths.len > 0:
        error("eponymBlock requireCompiled: definition '" & d.name &
          "' calls definitions outside the compiled block: " &
          codegen.slowPaths.join(", "), body)

  when defined(eponymCodegenReport):
    for d in defs:
      if d.name in compileTimeOnlyDefs:
        # Issue #401: type-level definitions never reach a backend; say
        # why they were excluded instead of reporting a fallback tier.
        echo "[eponym codegen] " & d.name &
          ": compile-time-only — " & compileTimeOnlyDefs[d.name] &
          "; excluded from the requireCompiled runtime closure"
        continue
      let entry = cgBlock.report.getOrDefault(d.name)
      let tierName = case entry.tier
        of cgtInterpreter: "interpreter fallback"
        of cgtValue: "Phase 1 Value backend"
        of cgtRepr: "Phase 2 representation backend"
      echo "[eponym codegen] " & d.name & ": " & tierName &
        " — " & entry.reason
      if entry.slowPaths.len > 0:
        echo "[eponym codegen]   runtime slow paths: " &
          entry.slowPaths.join(", ")
    # Issue #408: surface cross-block reuse of imported definitions —
    # they are not in `defs`, so the loop above never shows them.
    for d in codegenDefs:
      if d.loc.source.len == 0 or d.loc.source.startsWith("<eponymBlock>"):
        continue
      let entry = cgBlock.report.getOrDefault(d.name)
      if entry.crossBlockFrom == "": continue
      let tierName = case entry.tier
        of cgtInterpreter: "interpreter fallback"
        of cgtValue: "Phase 1 Value backend"
        of cgtRepr: "Phase 2 representation backend"
      echo "[eponym codegen] " & d.name & ": " & tierName &
        " — " & entry.reason
    for binding in postulateReprs:
      let entry = cgBlock.report.getOrDefault(binding.postulateName)
      if entry.tier == cgtRepr:
        echo "[eponym codegen] " & binding.postulateName &
          ": Phase 2 representation backend — " & entry.reason

  result = newStmtList()
  let dirLit = newLit(baseDir)
  # Issue #402: macro-generated boundary codecs for `runtimeDerive`
  # mappings, ahead of the codegen procs and typed wrappers that
  # reference them.
  for emittedProc in emittedDerivedCodecs:
    result.add(emittedProc)
  for p in cgBlock.procs:
    if not requireCompiled or
        (p.kind == nnkProcDef and p[0].kind == nnkPostfix and
         ($p[0][1]).startsWith("eponymCompiledRepr_")):
      result.add(p)
  # Issue #478: wrappers re-elaborate at runtime from their source
  # literal, so they get the filled source (holey src when nothing
  # was filled). Codegen above keeps the holey src.
  let wrapperSrc = if filledSrc.len > 0: filledSrc else: src
  for d in defs:
    if d.name in compileTimeOnlyDefs:
      # Issue #401: type-level definitions have no runtime denotation —
      # no Nim proc takes or returns their unrepresentable types — so no
      # wrapper is emitted. Referencing one from Nim is a compile error,
      # which is honest: there is nothing to call.
      continue
    let srcLit = newLit(wrapperSrc)
    let nameLit = newLit(d.name)
    var procDecl: NimNode = nil
    for st in body:
      if st.kind == nnkProcDef and $st[0] == d.name:
        procDecl = st
        break
    if procDecl.isNil:
      # Clause-style definitions have no Nim proc declaration to supply the
      # runtime ABI. Reconstruct a simple fixed-arity signature from the
      # checked Pi type and feed it through the same codec generator.
      procDecl = importedRuntimeProcDecl(d, checkedGlobals)
    if requireCompiled and procDecl.isNil:
      error("eponymBlock requireCompiled: cannot generate a typed Nim wrapper " &
        "for '" & d.name & "'", body)
    # Issue #478: a gated def gets exactly one surface — a use-gated
    # wrapper carrying its declared signature — and no other wrapper
    # (typed, dynamic, or runtimeValue), so no callable path bypasses
    # the gate.
    if d.name in gatedNames:
      let reason = gatedReasons.getOrDefault(d.name, "incomplete")
      if procDecl.isNil:
        result.add(unreconstructableRuntimeWrapper(d.name, reason))
      else:
        let tw = typedRuntimeWrapper(procDecl, baseDir, wrapperSrc, d.name,
          bindings, runtimeTypes, checkedGlobals, records,
          d.name in trustedRuntimePairs,
          cgBlock.compiled, cgBlock.compiledRepr, cgBlock.reprTypes, false)
        if not tw.isNil:
          result.add(gateWrapperProc(tw, reason))
        else:
          result.add(unsupportedRuntimeWrapper(procDecl, d.name, runtimeTypes,
            records, d.name in trustedRuntimePairs, reason))
      continue
    if not procDecl.isNil:
      if d.name in runtimeValueNames:
        let params = procDecl[3]
        let generic = genericRuntimeInfo(procDecl, runtimeTypes, records,
          allowDependentSigma = d.name in trustedRuntimePairs)
        var valueArity = 0
        for i in 1 ..< params.len:
          valueArity += params[i].len - 2
        let runtimeName = ident(d.name & "RuntimeValue")
        if procDecl[2].kind != nnkEmpty:
          let genericArgsSym = genSym(nskParam, "runtimeGenericArguments")
          let valueArgsSym = genSym(nskParam, "runtimeValueArguments")
          let globalsSym = genSym(nskLet, "runtimeGlobals")
          let defsSym = genSym(nskLet, "runtimeDefs")
          let bindingsSym = genSym(nskVar, "runtimeBindings")
          let nameLit = newLit(d.name)
          let dirLit = newLit(baseDir)
          let srcLit = newLit(wrapperSrc)
          let genericArity = newLit(block:
            var arity = 0
            for param in procDecl[2]:
              arity += param.len - 2
            arity)
          let valueArity = newLit(block:
            var arity = 0
            for i in 1 ..< params.len:
              arity += params[i].len - 2
            arity)
          var rawBody = newStmtList()
          rawBody.add quote do:
            if `genericArgsSym`.len != `genericArity`:
              raise newException(ValueError,
                "runtimeValue generic argument count mismatch for " & `nameLit`)
            if `valueArgsSym`.len != `valueArity`:
              raise newException(ValueError,
                "runtimeValue argument count mismatch for " & `nameLit`)
          rawBody.add(newLetStmt(globalsSym,
            newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
          rawBody.add(newLetStmt(defsSym,
            newCall(bindSym"getDefsDir", dirLit, srcLit)))
          rawBody.add(newVarStmt(bindingsSym,
            newCall(bindSym"initRuntimeBindings")))
          for binding in bindings:
            rawBody.add(bindingCall(binding, bindingsSym, globalsSym,
                                    runtimeTypes, records, checkedGlobals))
          let allArgsSeq = genSym(nskLet, "allRuntimeArguments")
          rawBody.add(newLetStmt(allArgsSeq, newCall(bindSym"concat",
            newCall(bindSym"toSeq", genericArgsSym),
            newCall(bindSym"toSeq", valueArgsSym))))
          rawBody.add(newTree(nnkTupleConstr,
            newCall(bindSym"callDefValueWithBindings",
              newCall(bindSym"findDef", defsSym, nameLit), allArgsSeq,
              bindingsSym, globalsSym), globalsSym))
          var rawProc = newNimNode(nnkProcDef)
          rawProc.add(newTree(nnkPostfix, ident"*",
                              ident(d.name & "RuntimeValueRaw")))
          rawProc.add(newEmptyNode())
          rawProc.add(newEmptyNode())
          var rawFormal = newNimNode(nnkFormalParams)
          rawFormal.add(bindSym"RuntimeValueResult")
          rawFormal.add(newIdentDefs(genericArgsSym,
            newTree(nnkBracketExpr, ident"openArray", bindSym"RuntimeValue"),
            newEmptyNode()))
          rawFormal.add(newIdentDefs(valueArgsSym,
            newTree(nnkBracketExpr, ident"openArray", bindSym"RuntimeValue"),
            newEmptyNode()))
          rawProc.add(rawFormal)
          rawProc.add(newEmptyNode())
          rawProc.add(newEmptyNode())
          rawProc.add(rawBody)
          result.add(rawProc)
        let globalsSym = genSym(nskLet, "runtimeGlobals")
        let defsSym = genSym(nskLet, "runtimeDefs")
        let bindingsSym = genSym(nskVar, "runtimeBindings")
        let argsSym = genSym(nskParam, "runtimeArguments")
        var genericValues = newNimNode(nnkBracket)
        if generic.error.len == 0:
          for genericArg in genericRuntimeValueArgs(generic, globalsSym,
              runtimeTypes, records):
            genericValues.add(copyNimTree(genericArg))
        let runtimeArgsSym = newCall(bindSym"prependRuntimeArgs",
          newTree(nnkPrefix, ident"@", genericValues), argsSym)
        let expectedArity = newLit(valueArity)
        var bindingStatements = newStmtList()
        for binding in bindings:
          bindingStatements.add(bindingCall(binding, bindingsSym, globalsSym,
                                            runtimeTypes, records,
                                            checkedGlobals))
        var rawBody = newStmtList()
        rawBody.add quote do:
          if `argsSym`.len != `expectedArity`:
            raise newException(ValueError,
              "runtimeValue argument count mismatch for " & `nameLit`)
        rawBody.add quote do:
            let `globalsSym` = getGlobalsDir(`dirLit`, `srcLit`)
            let `defsSym` = getDefsDir(`dirLit`, `srcLit`)
            var `bindingsSym` = initRuntimeBindings()
        rawBody.add(bindingStatements)
        rawBody.add quote do:
            (callDefValueWithBindings(findDef(`defsSym`, `nameLit`), `runtimeArgsSym`,
                                      `bindingsSym`), `globalsSym`)
        if generic.error.len == 0:
          var rawProc = newNimNode(nnkProcDef)
          rawProc.add(newTree(nnkPostfix, ident("*"), runtimeName))
          rawProc.add(newEmptyNode())
          rawProc.add(copyNimTree(generic.genericParams))
          var rawFormal = newNimNode(nnkFormalParams)
          rawFormal.add(bindSym"RuntimeValueResult")
          rawFormal.add(newIdentDefs(argsSym,
            newTree(nnkBracketExpr, ident"openArray", bindSym"RuntimeValue"),
            newEmptyNode()))
          rawProc.add(rawFormal)
          rawProc.add(newEmptyNode())
          rawProc.add(newEmptyNode())
          rawProc.add(rawBody)
          result.add(rawProc)
        if valueArity == 0 and generic.error.len == 0:
          var forwarderBody = newStmtList()
          var rawCallee: NimNode = copyNimTree(runtimeName)
          if generic.genericNames.len > 0:
            var genericCallArgs = newNimNode(nnkBracket)
            for genericName in generic.genericNames:
              genericCallArgs.add(copyNimTree(genericName))
            rawCallee = newTree(nnkBracketExpr, rawCallee, genericCallArgs)
          forwarderBody.add(newCall(rawCallee, newNimNode(nnkBracket)))
          var forwarder = newNimNode(nnkProcDef)
          forwarder.add(newTree(nnkPostfix, ident("*"),
                                ident(d.name & "RuntimeValue")))
          forwarder.add(newEmptyNode())
          forwarder.add(copyNimTree(generic.genericParams))
          var forwarderFormal = newNimNode(nnkFormalParams)
          forwarderFormal.add(bindSym"RuntimeValueResult")
          forwarder.add(forwarderFormal)
          forwarder.add(newEmptyNode())
          forwarder.add(newEmptyNode())
          forwarder.add(forwarderBody)
          result.add(forwarder)
        else:
          let allowDependentSigma = d.name in trustedRuntimePairs
          let typedValueWrapper = typedRuntimeValueWrapper(procDecl,
            baseDir, wrapperSrc, d.name, bindings, runtimeTypes, checkedGlobals,
            records, allowDependentSigma, cgBlock.compiled)
          if not typedValueWrapper.isNil:
            result.add(typedValueWrapper)
      let allowDependentSigma = d.name in trustedRuntimePairs
      let typedWrapper = typedRuntimeWrapper(procDecl, baseDir, wrapperSrc, d.name,
        bindings, runtimeTypes, checkedGlobals, records, allowDependentSigma,
        cgBlock.compiled, cgBlock.compiledRepr, cgBlock.reprTypes,
        requireCompiled)
      if not typedWrapper.isNil:
        result.add(typedWrapper)
      else:
        if requireCompiled:
          error("eponymBlock requireCompiled: no typed runtime wrapper for '" &
            d.name & "'", procDecl)
        result.add(unsupportedRuntimeWrapper(procDecl, d.name, runtimeTypes,
          records, allowDependentSigma))
      let dynamicWrapper = dynamicGenericRuntimeWrapper(procDecl, baseDir,
        src, d.name, bindings, runtimeTypes, checkedGlobals, records,
        allowDependentSigma)
      if not dynamicWrapper.isNil and not requireCompiled:
        result.add(dynamicWrapper)
      let addTypedDynamicGenericValueOverloads =
        not requireCompiled and not allowDependentSigma and
        hasCodecBackedDynamicValueBinder(procDecl, runtimeTypes, records)
      if addTypedDynamicGenericValueOverloads:
        let typedDynamicGenericValueWrapper = dynamicGenericRuntimeWrapper(
          procDecl, baseDir, wrapperSrc, d.name, bindings, runtimeTypes,
          checkedGlobals, records, allowDependentSigma = true,
          allowGenericFunctionValues = true)
        if not typedDynamicGenericValueWrapper.isNil:
          result.add(typedDynamicGenericValueWrapper)
      if d.name in runtimeValueNames:
        let dynamicRuntimeValueWrapper = dynamicGenericRuntimeWrapper(procDecl,
          baseDir, wrapperSrc, d.name, bindings, runtimeTypes, checkedGlobals,
          records, allowDependentSigma, returnRuntimeValue = true)
        if not dynamicRuntimeValueWrapper.isNil:
          result.add(dynamicRuntimeValueWrapper)
        else:
          let generic = genericRuntimeInfo(procDecl, runtimeTypes, records,
            allowDependentSigma = d.name in trustedRuntimePairs)
          if generic.error.len > 0:
            error("eponymBlock runtimeValue wrapper '" & d.name & "': " &
              generic.error, procDecl)
        if addTypedDynamicGenericValueOverloads:
          let typedDynamicGenericValueRuntimeValueWrapper =
            dynamicGenericRuntimeWrapper(procDecl, baseDir, wrapperSrc, d.name,
              bindings, runtimeTypes, checkedGlobals, records,
              allowDependentSigma = true, returnRuntimeValue = true,
              allowGenericFunctionValues = true)
          if not typedDynamicGenericValueRuntimeValueWrapper.isNil:
            result.add(typedDynamicGenericValueRuntimeValueWrapper)
      continue
    if d.name in runtimeValueNames:
      result.add(rawRuntimeValueWrapper(baseDir, wrapperSrc, d.name,
        checkedLambdaArity(d), bindings,
        runtimeTypes, records, checkedGlobals))
    result.add(unreconstructableRuntimeWrapper(d.name))
  for requested in runtimeValueNames:
    var localDef = false
    for d in defs:
      if d.name == requested:
        localDef = true
        break
    if not localDef:
      var importedDef: ElabDef
      for d in allDefs:
        if d.name == requested:
          importedDef = d
          break
      if importedDef.name.len > 0:
        let importedDecl = importedRuntimeProcDecl(importedDef,
          checkedGlobals)
        if not importedDecl.isNil:
          let typedImportedWrapper = typedRuntimeWrapper(importedDecl,
            baseDir, wrapperSrc, requested, bindings, runtimeTypes, checkedGlobals,
            records, false, initTable[string, string]())
          if not typedImportedWrapper.isNil:
            result.add(typedImportedWrapper)
          let typedImportedValueWrapper = typedRuntimeValueWrapper(
            importedDecl, baseDir, wrapperSrc, requested, bindings, runtimeTypes,
            checkedGlobals, records, false, initTable[string, string]())
          if not typedImportedValueWrapper.isNil:
            result.add(typedImportedValueWrapper)
        result.add(rawRuntimeValueWrapper(baseDir, wrapperSrc, requested,
          checkedLambdaArity(importedDef), bindings, runtimeTypes, records,
          checkedGlobals,
          if not importedDecl.isNil and
              importedDecl[2].kind != nnkEmpty: "RuntimeValueRaw"
          else: "RuntimeValue"))

macro eponym*(src: string): untyped =
  ## Elaborate and typecheck a surface program at compile time.
  ## On success expands to nothing; on failure compilation stops with an
  ## error pointing at the eponym"..." literal.
  let s = src.strVal  # src is a string literal (enforced by the signature)
  try:
    discard elabCheck(s)
  except ElabError as e:
    error("eponym elaboration error: " & e.msg, src)
  except ParseError as e:
    error("eponym parse error: " & e.msg, src)
  result = newStmtList()

when isMainModule:
  eponym"""
proc twice (A : Univ) (f : A -> A) (x : A) : A =
  f (f x)
proc pairSwap (A : Univ) (B : Univ) (p : Sig(u: A, B)) : Sig(v: B, A) =
  (snd p, fst p)
"""
  echo "ok: eponym macro accepts well-typed programs at compile time"
