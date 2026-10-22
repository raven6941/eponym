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

proc nimExprToEponym(n: NimNode): string
proc nimTypeToEponym(n: NimNode): string
proc isNilLiteralExpr(n: NimNode): bool
proc nilConstructorForType(typeNode: NimNode): string

proc ifExprToEponym(n: NimNode): string =
  var branches: seq[(NimNode, NimNode)] = @[]
  var elseBranch: NimNode = nil
  for branch in n:
    case branch.kind
    of nnkElifExpr, nnkElifBranch:
      if branch.len != 2:
        error("eponymBlock: if branch must have one condition and body", branch)
      branches.add((branch[0], branch[1]))
    of nnkElseExpr, nnkElse:
      if branch.len != 1:
        error("eponymBlock: else branch must have one body", branch)
      elseBranch = branch[0]
    else:
      error("eponymBlock: unsupported if branch " & $branch.kind, branch)
  if branches.len == 0 or elseBranch.isNil:
    error("eponymBlock: pure if expression requires a condition and an else branch", n)
  proc branchExpr(branch: NimNode): NimNode =
    if branch.kind == nnkStmtList:
      if branch.len != 1:
        error("eponymBlock: if branch must be one expression", branch)
      return branch[0]
    branch
  if elseBranch.kind == nnkStmtList:
    if elseBranch.len != 1:
      error("eponymBlock: else branch must be one expression", elseBranch)
    elseBranch = elseBranch[0]
  # Eponym applications are strict, while Nim conditionals evaluate only the
  # selected branch. Pass each branch as a unit thunk so a postulate (or any
  # other runtime-bound operation) in the unselected branch is not evaluated.
  var fallback = "(lam (_ : 1). " & nimExprToEponym(elseBranch) & ")"
  for i in countdown(branches.high, 0):
    let (condition, body) = branches[i]
    let yesBranch = "(lam (_ : 1). " & nimExprToEponym(branchExpr(body)) & ")"
    fallback = "ifThenElse (" & nimExprToEponym(condition) & ") " &
      yesBranch & " (" & fallback & ")"
  "(" & fallback & ") <>"

proc nimCommandLamToEponym(n: NimNode): string =
  ## Convert Nim's command-form untyped lambda (`lam x. body`) to Eponym
  ## syntax. Nim represents a nested chain such as `lam x. lam y. body`
  ## as `Command(lam, Command(DotExpr(x, lam), DotExpr(y, body)))`.
  if n.kind != nnkCommand or n.len != 2 or
     n[0].kind != nnkIdent or $n[0] != "lam":
    error("eponymBlock: unsupported command-form lambda", n)
  let arg = n[1]
  if arg.kind == nnkDotExpr and arg.len == 2:
    return "lam " & nimExprToEponym(arg[0]) & ". " &
           nimExprToEponym(arg[1])
  if arg.kind == nnkCommand and arg.len == 2 and
     arg[0].kind == nnkDotExpr and arg[0].len == 2 and
     arg[0][1].kind == nnkIdent and $arg[0][1] == "lam":
    var nested = newNimNode(nnkCommand)
    nested.add(ident("lam"))
    nested.add(arg[1])
    # A command-form typed binder such as `(n : Nat)` is represented as a
    # tuple/colon AST, not an identifier. Reuse the expression converter so
    # typed binders survive in nested command lambdas.
    return "lam " & nimExprToEponym(arg[0][0]) & ". " &
           nimCommandLamToEponym(nested)
  error("eponymBlock: unsupported command-form lambda", n)

proc nimCommandToEponym(n: NimNode): string =
  ## Nim's command-call syntax (`suc n`) is also nnkCommand. Treat ordinary
  ## commands as applications and reserve the special parser for `lam`.
  ## Nim nests whitespace-separated command arguments in child Command
  ## nodes; flatten those arguments instead of grouping them as one term.
  if n.len == 0: error("eponymBlock: empty command expression", n)
  if n[0].kind == nnkIdent and $n[0] == "lam":
    return nimCommandLamToEponym(n)
  var args: seq[string] = @[]
  proc appendArg(a: NimNode) =
    if a.kind == nnkCommand and a.len > 0 and
       not (a[0].kind == nnkIdent and $a[0] == "lam"):
      appendArg(a[0])
      for j in 1 ..< a.len:
        appendArg(a[j])
    elif a.kind == nnkCommand:
      args.add("(" & nimCommandLamToEponym(a) & ")")
    elif a.kind in {nnkCall, nnkObjConstr}:
      args.add("(" & nimExprToEponym(a) & ")")
    else:
      args.add(nimExprToEponym(a))
  for i in 1 ..< n.len:
    appendArg(n[i])
  nimExprToEponym(n[0]) & " " & args.join(" ")

proc legacyCallInfoFromNimType(ty: NimNode): LegacyCallInfo

proc nimExprToEponym(n: NimNode): string =
  ## Convert a Nim expression AST to Eponym source string.
  case n.kind
  of nnkIdent:
    var s = $n
    # Map Nim-safe names to Eponym names
    if s == "vecnil": s = "nil"
    if s == "unitv": s = "<>"   # issue #151: `<>` is not valid Nim syntax
    if s == "unitTy": s = "1"   # issue #151: the unit *type* (QTT)
    if s == "emptyTy": s = "O"  # issue #151: the empty type
    if s == "Univ": "Type 0"
    elif s == "_": "?"
    else: s
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    # In eponymBlock, integer literals are passed through verbatim and
    # overloaded by the elaborator (checkTm pkInt: Nat when the expected
    # type is Nat, primitive Int when it is Int) -- the same semantics
    # as string syntax. This also resolves Issue #8: nested literals in
    # eponymBlock bodies (e.g. cons(Int, 2, a, ...), eConst 3) now elaborate
    # per their expected type instead of always becoming Nat suc-chains.
    # Exception: 1 lexes as the *unit type* in surface syntax (QTT), so use
    # the parser's unambiguous integer spelling `01`. Expected-type
    # overloading then selects Nat or Int, just as it does for other literals.
    let v = n.intVal
    if v < 0: error("negative integer literal", n)
    if v == 1: "01" else: $v
  of nnkStmtList:
    # Proc body: convert let-statements to nested let...in, final expr is body
    if n.len == 0: error("eponymBlock: empty proc body", n)
    # Collect lets and final expression
    var lets: seq[(string, string, string)] = @[]  # (name, type-or-"", value)
    var finalExpr = newEmptyNode()
    for stmt in n:
      if stmt.kind == nnkLetSection:
        for def in stmt:
          # nnkIdentDefs: [name, type, value]; the type may be Empty
          # (issue #151: typed lets keep their annotation)
          let name = $def[0]
          var tyAnn = ""
          var isNatBinding = false
          if def[1].kind != nnkEmpty:
            let declaredType = nimTypeToEponym(def[1])
            tyAnn = " : " & declaredType
            isNatBinding = declaredType == "Nat"
          let val = if isNilLiteralExpr(def[2]):
            if def[1].kind == nnkEmpty:
              error("eponymBlock: `nil` in a let binding needs an explicit " &
                "List[...] or Vec[...] type", def[2])
            nilConstructorForType(def[1])
            else: nimExprToEponym(def[2])
          let callInfoSource = if def[2].kind in {nnkIdent, nnkSym}:
            $def[2] else: ""
          if callInfoSource in legacyCallInfo and
              legacyCallInfo[callInfoSource].termCount > 0:
            legacyCallInfo[name] = legacyCallInfo[callInfoSource]
          elif def[1].kind == nnkProcTy:
            let callInfo = legacyCallInfoFromNimType(def[1])
            if callInfo.termCount > 0:
              legacyCallInfo[name] = callInfo
          if isNatBinding or isLegacyNatExpr(def[2]):
            scopedNatNames.incl(name)
          lets.add((name, tyAnn, val))
      else:
        # Final expression (or single expression)
        if finalExpr.kind != nnkEmpty:
          error("eponymBlock: proc body must be lets followed by single expr", n)
        finalExpr = stmt
    if finalExpr.kind == nnkEmpty:
      error("eponymBlock: proc body must end with expression", n)
    var res = nimExprToEponym(finalExpr)
    # Wrap in let...in (innermost first, so reverse)
    for i in countdown(lets.len - 1, 0):
      let (nm, ty, vl) = lets[i]
      res = "let " & nm & ty & " = " & vl & " in " & res
    res
  of nnkObjConstr:
    # Pi(...)/Sig(...) type expressions in body position: Nim parses
    # them as object constructors, not calls. They are types, so route
    # through the type converter.
    nimTypeToEponym(n)
  of nnkCall:
    # byTac(refl) -> by refl (surface tactic term; smoke test 14, issue #151)
    if n[0].kind == nnkIdent and $n[0] == "byTac":
      if n.len != 2:
        error("byTac expects (tacticName)", n)
      let t = n[1]
      if t.kind == nnkIdent: return "by " & $t
      elif t.kind == nnkStrLit: return "by " & t.strVal
      else: error("byTac expects a tactic name (ident or string)", n)
    # Pi/Sig in expression position, positional form Sig(name, Dom, Body):
    # Nim parses it as a call, not an obj-constr. Route to the type converter.
    if n[0].kind == nnkIdent and $n[0] in ["Pi", "Sig"]:
      return nimTypeToEponym(n)
    # lam(x, T, body) -> lam (x : T). body (surface lambdas in eponymBlock bodies)
    if n[0].kind == nnkIdent and $n[0] == "lam":
      if n.len != 4 or n[1].kind notin {nnkIdent, nnkPragmaExpr}:
        error("lam expects (binder, type, body)", n)
      return "lam (" & qtyPrefix(n[1]) & binderName(n[1]) & " : " &
             nimTypeToEponym(n[2]) & "). " & nimExprToEponym(n[3])
    warnCallStyleExplicitArgs(n)
    # f(a, b) -> f a b (with parens for nested calls to preserve grouping)
    var callArgs: seq[NimNode] = @[]
    for i in 1 ..< n.len: callArgs.add(n[i])
    let headName = if n[0].kind in {nnkIdent, nnkSym}: $n[0] else: ""
    if callArgs.anyIt(namedArgumentName(it).len > 0):
      if headName.len == 0 or headName notin legacyCallInfo:
        error("eponymBlock: named arguments need a known callable signature", n)
      callArgs = orderCallArguments(callArgs,
        legacyCallInfo[headName].termParamNames,
        legacyCallInfo[headName].termParamDefaults, n)
    elif headName.len > 0 and headName in legacyCallInfo:
      callArgs = orderCallArguments(callArgs,
        legacyCallInfo[headName].termParamNames,
        legacyCallInfo[headName].termParamDefaults, n)
    let head = nimExprToEponym(n[0])
    var args: seq[string] = @[]
    for a in callArgs:
      # Parenthesize if arg is a call or obj-constr (Pi/Sig type args
      # parse as nnkObjConstr in expression position and need grouping too)
      if a.kind in {nnkCall, nnkObjConstr, nnkCommand}:
        args.add("(" & nimExprToEponym(a) & ")")
      else:
        args.add(nimExprToEponym(a))
    if args.len == 0: head
    else: head & " " & args.join(" ")
  of nnkPar:
    # (x) -> x (parenthesized)
    if n.len == 1: nimExprToEponym(n[0])
    else: "(" & n.mapIt(nimExprToEponym(it)).join(", ") & ")"
  of nnkCommand:
    nimCommandToEponym(n)
  of nnkBracketExpr:
    if n.len < 2:
      error("eponymBlock: bracket application needs explicit arguments", n)
    var parts = @[nimExprToEponym(n[0])]
    for i in 1 ..< n.len:
      let arg = n[i]
      var value: string
      let headName = if n[0].kind in {nnkIdent, nnkSym}: $n[0] else: ""
      if headName in legacyCallInfo and
          i - 1 < legacyCallInfo[headName].applicationParamTypes.len and
          legacyCallInfo[headName].applicationParamTypes[i - 1] == "Nat" and
          arg.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                       nnkInt64Lit} and arg.intVal == 1:
        # Eponym surface `1` is the unit type. At a bracket position whose
        # declared binder is Nat, spell the literal one as its constructor
        # form; ordinary expression positions keep `01` for expected-type
        # overloading between Int and Nat.
        value = "(suc zero)"
      else:
        value = nimExprToEponym(arg)
      if arg.kind in {nnkCall, nnkCommand, nnkObjConstr, nnkBracketExpr,
                      nnkInfix, nnkPrefix}:
        parts.add("(" & value & ")")
      else:
        parts.add(value)
    parts.join(" ")
  of nnkInfix:
    let prim = case $n[0]
      of "+": "addInt"
      of "-": "subInt"
      of "*": "mulInt"
      of "and", "or": $n[0]
      else: error("eponymBlock: unsupported pure operator '" & $n[0] & "'",
                  n[0])
    prim & " (" & nimExprToEponym(n[1]) & ") (" &
      nimExprToEponym(n[2]) & ")"
  of nnkPrefix:
    if $n[0] == "-":
      "subInt 0 (" & nimExprToEponym(n[1]) & ")"
    elif $n[0] == "not":
      "not (" & nimExprToEponym(n[1]) & ")"
    else:
      error("eponymBlock: unsupported pure prefix operator '" & $n[0] & "'",
            n[0])
  of nnkIfExpr, nnkIfStmt:
    ifExprToEponym(n)
  of nnkStmtListExpr:
    if n.len == 1: nimExprToEponym(n[0])
    else: error("eponymBlock: expected one expression in type index", n)
  of nnkDotExpr:
    # p.x -> (p).x (record projection, issue #37; the surface parser
    # resolves it against the record table at elaboration time).
    # The LHS is parenthesized: in `mkPt(x, y).x` the dot must not
    # rebind to `y`.
    "(" & nimExprToEponym(n[0]) & ")." & nimExprToEponym(n[1])
  of nnkTupleConstr:
    # (t : T) ascription (Nim parses it as a 1-tuple of ExprColonExpr);
    # (a, b) -> (a, b) [Eponym pair syntax]
    if n.len == 1 and n[0].kind == nnkExprColonExpr and n[0].len == 2:
      "(" & nimExprToEponym(n[0][0]) & " : " & nimTypeToEponym(n[0][1]) & ")"
    else:
      "(" & n.mapIt(nimExprToEponym(it)).join(", ") & ")"
  else:
    error("eponymBlock: unsupported Nim expression shape '" & $n.kind &
      "'; express the operation in supported Eponym syntax, or move the Nim " &
      "expression outside the block and expose it through a bound postulate",
      n)

proc piSigToEponym(n: NimNode): string
  ## Convert Pi(...)/Sig(...) (nnkCall or nnkObjConstr) to Eponym.
  ## Pi(x: A, y {.linear.}: B, C) -> Pi (x : A). Pi (1 y : B). C
  ## Sig(x: A, B) -> Sig (x : A). B ; Sig(A, B) -> Sig (_ : A). B
  ## Note: Nim parses `Pi(x: A, ...)` with named binders as nnkObjConstr,
  ## not nnkCall, so both shapes must be handled.

proc nimTypeToEponym(n: NimNode): string =
  ## Convert a Nim type AST to Eponym type string.
  case n.kind
  of nnkIdent:
    var s = $n
    # Map Nim-safe names to Eponym names (issue #144: same mapping as
    # expressions -- `nil` is a Nim keyword, so constructor references in
    # types must go through `vecnil` too)
    if s == "vecnil": s = "nil"
    if s == "unitv": s = "<>"   # issue #151: `<>` is not valid Nim syntax
    if s == "unitTy": s = "1"   # issue #151: the unit *type* (QTT)
    if s == "emptyTy": s = "O"  # issue #151: the empty type
    if s == "Univ": "Type 0" else: s
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    # Integer literal in type position: passed through verbatim; the
    # elaborator overloads it against the expected type (Nat or Int),
    # exactly as in string syntax (Issues #8, #115).
    # Exception: 1 lexes as the *unit type* in surface syntax (QTT), so
    # the Nat literal one is spelled `suc zero` (as in string syntax).
    let v = n.intVal
    if v < 0: error("negative integer literal in type", n)
    if v == 1: "(suc zero)" else: $v
  of nnkBracketExpr:
    if n.len < 2:
      error("eponymBlock: bracket type application needs explicit arguments", n)
    let head = nimTypeToEponym(n[0])
    var args: seq[string] = @[]
    for i in 1 ..< n.len:
      let a = n[i]
      if (a.kind == nnkCall and
          (a.len > 1 or a[0].kind == nnkBracketExpr)) or a.kind in
          {nnkObjConstr, nnkBracketExpr, nnkIfExpr, nnkIfStmt,
           nnkStmtListExpr} or
          a.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                     nnkInt64Lit}:
        args.add("(" & nimTypeToEponym(a) & ")")
      else:
        args.add(nimTypeToEponym(a))
    head & " " & args.join(" ")
  of nnkProcTy:
    if n.len != 2 or n[0].kind != nnkFormalParams or n[0].len < 2:
      error("runtime proc types require at least one named argument", n)
    var resultType = nimTypeToEponym(n[0][0])
    var params: seq[(string, NimNode)] = @[]
    for i in 1 ..< n[0].len:
      let p = n[0][i]
      if p.kind != nnkIdentDefs or p.len < 3:
        error("runtime proc types require ordinary named arguments", p)
      for j in 0 ..< p.len - 2:
        let name = if p[j].kind == nnkEmpty: "callbackArg" & $params.len
                   else: $p[j]
        params.add((name, p[^2]))
    for i in countdown(params.high, 0):
      resultType = "Pi (" & params[i][0] & " : " &
        nimTypeToEponym(params[i][1]) & "). " & resultType
    resultType
  of nnkCall:
    # Tactic term in type position (issue #151): byTac(refl) -> by refl.
    if n[0].kind == nnkIdent and $n[0] == "byTac":
      return nimExprToEponym(n)
    # Vec(Int, three) -> Vec Int three (paren nested calls)
    # For zero-arg calls like zero(), just return head (no parens needed)
    if n[0].kind == nnkIdent and $n[0] in ["Pi", "Sig"]:
      return piSigToEponym(n)
    if n[0].kind == nnkIdent and $n[0] == "lam":
      # lam(x, T, body) -> lam (x : T). body (continuations in types)
      if n.len != 4 or n[1].kind notin {nnkIdent, nnkPragmaExpr}:
        error("lam expects (binder, type, body)", n)
      return "lam (" & qtyPrefix(n[1]) & binderName(n[1]) & " : " &
             nimTypeToEponym(n[2]) & "). " & nimTypeToEponym(n[3])
    warnCallStyleTypeArgs(n)
    let head = nimTypeToEponym(n[0])
    if n.len == 1:
      head
    else:
      var args: seq[string] = @[]
      for i in 1 ..< n.len:
        let a = n[i]
        # Paren if arg is a call with args, an obj-constr (Pi/Sig type args
        # parse as nnkObjConstr and need grouping too), or an int literal
        # (suc chain needs grouping)
        if (a.kind == nnkCall and
            (a.len > 1 or a[0].kind == nnkBracketExpr)) or
            a.kind == nnkObjConstr or a.kind in
            {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit}:
          args.add("(" & nimTypeToEponym(a) & ")")
        else:
          args.add(nimTypeToEponym(a))
      head & " " & args.join(" ")
  of nnkObjConstr:
    # Nim parses `Pi(x: A, y {.linear.}: B, C)` (named binders) as an object
    # constructor, not a call. Only Pi/Sig are meaningful here.
    if n[0].kind == nnkIdent and $n[0] in ["Pi", "Sig"]:
      return piSigToEponym(n)
    error("eponymBlock: unsupported object construction in type: " & $n[0], n)
  of nnkInfix:
    # A -> B -> A -> B (right associative, as in Eponym)
    if $n[0] == "->" and n.len == 3:
      nimTypeToEponym(n[1]) & " -> " & nimTypeToEponym(n[2])
    else:
      error("eponymBlock: unsupported infix in type: " & $n[0], n)
  of nnkPar:
    # Preserve explicit grouping: (A -> B) -> C must not flatten to
    # A -> B -> C, and (Pi (n : Nat). ...) -> ... must not let the Pi body
    # swallow the rest of the arrow chain (issue #151: the natElim motive
    # method needs those parens).
    if n.len == 1: "(" & nimTypeToEponym(n[0]) & ")"
    else: error("eponymBlock: unexpected parenthesized form in type", n)
  else:
    nimExprToEponym(n)

proc piSigToEponym(n: NimNode): string =
  let isPi = $n[0] == "Pi"
  if n.len < 3: error($n[0] & " expects binders and a body", n)
  # Sig in Call form (positional args, no colons): Sig(name, Dom, Body).
  if not isPi and n.kind == nnkCall:
    if n.len == 4 and n[1].kind == nnkIdent:
      return "Sig (" & $n[1] & " : " & nimTypeToEponym(n[2]) & "). " & nimTypeToEponym(n[3])
    elif n.len == 3:
      return "Sig (_ : " & nimTypeToEponym(n[1]) & "). " & nimTypeToEponym(n[2])
    else:
      error("Sig expects (binder, dom, body) or (dom, body)", n)
  var parts: seq[string] = @[]
  for i in 1 ..< n.len - 1:
    let b = n[i]
    var q, nm, dom: string
    if b.kind == nnkTableConstr:
      # {A : T, ...} -> implicit binders (Pi only). Each pair: name : type.
      if not isPi: error("implicit binders only meaningful in Pi", b)
      for pair in b:
        if pair.kind != nnkExprColonExpr or pair.len != 2 or pair[0].kind != nnkIdent:
          error("implicit binder must have form {name : type}", b)
        parts.add("Pi {" & $pair[0] & " : " & nimTypeToEponym(pair[1]) & "}. ")
      continue
    if b.kind == nnkExprColonExpr and b.len == 2:
      q = qtyPrefix(b[0])
      nm = binderName(b[0])
      dom = nimTypeToEponym(b[1])
    elif not isPi:
      # Sig(A, B): anonymous binder -> Sig (_ : A). B
      q = ""; nm = "_"; dom = nimTypeToEponym(b)
    else:
      error("Pi binder must have form name: type", b)
    if isPi:
      parts.add("Pi (" & q & nm & " : " & dom & "). ")
    else:
      parts.add("Sig (" & q & nm & " : " & dom & "). ")
  parts.join("") & nimTypeToEponym(n[^1])

proc patToEponym(n: NimNode): string =
  ## Clause patterns are surface *atoms*; constructor applications need
  ## parens in surface syntax (`(suc m)`), so wrap calls (issue #151).
  case n.kind
  of nnkIdent:
    if $n == "_": "_" else: nimExprToEponym(n)
  of nnkCall:
    let s = nimExprToEponym(n)
    if n.len > 1: "(" & s & ")" else: s
  of nnkPar:
    if n.len == 1 and n[0].kind == nnkCall: "(" & nimExprToEponym(n[0]) & ")"
    else: nimExprToEponym(n)
  else:
    nimExprToEponym(n)

proc legacyCallInfoFromNimType(ty: NimNode): LegacyCallInfo =
  if ty.kind == nnkProcTy and ty.len == 2 and
      ty[0].kind == nnkFormalParams:
    result.termParamNames = nimFormalArgNames(ty[0])
    result.termParamDefaults = nimFormalArgDefaults(ty[0])
  let declarations = parseProgram("postulate __legacyCallable : " &
    nimTypeToEponym(ty))
  for declaration in declarations:
    if declaration.kind != dkPostulate: continue
    var current = declaration.ty
    while not current.isNil and current.kind == pkPi:
      result.applicationParamTypes.add($current.c1)
      let isType = current.c1.kind in {pkUniv, pkUnivN}
      if current.impl or isType:
        inc result.explicitCount
        if result.explicitCount == 1:
          result.firstExplicitNat = current.c1.kind == pkVar and
            current.c1.name == "Nat"
          result.requiresBrackets = not current.impl and isType
      else:
        inc result.termCount
      current = current.c2
    break

proc isNilLiteralExpr(n: NimNode): bool =
  if n.kind == nnkNilLit: return true
  if n.kind in {nnkPar, nnkStmtList} and n.len == 1:
    return isNilLiteralExpr(n[0])
  false

proc nilConstructorForType(typeNode: NimNode): string =
  # The Eponym List/Vec constructors are polymorphic functions, so Nim's
  # expected type must supply their element type argument.
  if typeNode.kind != nnkBracketExpr or typeNode.len < 2 or
      $typeNode[0] notin ["List", "Vec"]:
    error("eponymBlock: `nil` expression needs a List[...] or Vec[...] " &
      "type", typeNode)
  let elementType = nimTypeToEponym(typeNode[1])
  "nil (" & elementType & ")"

proc procDefToEponym(n: NimNode): string =
  ## Convert nnkProcDef to "proc name (generic binders) (params) : ret = body".
  # n[0] = name, n[1] = empty (pragma?), n[2] = generic params,
  # n[3] = formal params, n[4] = empty, n[5] = empty, n[6] = body
  let name = $n[0]
  let params = n[3]  # nnkFormalParams: [returnType, param1, param2, ...]
  let priorScopedTypeNames = toSeq(scopedLegacyTypeNames)
  let priorNatNames = toSeq(scopedNatNames)
  scopedLegacyTypeNames.clear()
  scopedNatNames.clear()
  var genericBinders: seq[string] = @[]
  if n[2].kind != nnkEmpty:
    for genericParam in n[2]:
      if genericParam.kind != nnkIdentDefs or
          genericParam[^2].kind == nnkEmpty:
        error("eponymBlock: explicit generic parameters need Eponym type annotations", genericParam)
      let ty = nimTypeToEponym(genericParam[^2])
      for i in 0 ..< genericParam.len - 2:
        genericBinders.add("(" & binderName(genericParam[i]) & " : " & ty & ")")
        if ty == "Type 0": scopedLegacyTypeNames.incl(binderName(genericParam[i]))
        if ty == "Nat": scopedNatNames.incl(binderName(genericParam[i]))
  var paramStrs: seq[string] = @[]
  var retTy = "Type 0"
  if params.len > 0 and params[0].kind != nnkEmpty:
    retTy = nimTypeToEponym(params[0])
  for i in 1 ..< params.len:
    let p = params[i]  # nnkIdentDefs: [name1, name2, ..., type, default]
    let ty = nimTypeToEponym(p[^2])
    for j in 0 ..< p.len - 2:
      let q = qtyPrefix(p[j])
      paramStrs.add("(" & q & binderName(p[j]) & " : " & ty & ")")
      if ty == "Type 0": scopedLegacyTypeNames.incl(binderName(p[j]))
      if ty == "Nat": scopedNatNames.incl(binderName(p[j]))
  let priorCallableInfos = toSeq(legacyCallInfo.pairs)
  for i in 1 ..< params.len:
    let formal = params[i]
    if formal.kind != nnkIdentDefs: continue
    let callableInfo = legacyCallInfoFromNimType(formal[^2])
    if callableInfo.explicitCount == 0 and callableInfo.termCount == 0: continue
    for j in 0 ..< formal.len - 2:
      let nameNode = if formal[j].kind == nnkPragmaExpr:
        formal[j][0] else: formal[j]
      let name = $nameNode
      legacyCallInfo[name] = callableInfo
  var body: string
  if isNilLiteralExpr(n[6]):
    body = nilConstructorForType(params[0])
  else:
    body = nimExprToEponym(n[6])
  legacyCallInfo.clear()
  for (callName, callInfo) in priorCallableInfos:
    legacyCallInfo[callName] = callInfo
  scopedLegacyTypeNames.clear()
  for typeName in priorScopedTypeNames: scopedLegacyTypeNames.incl(typeName)
  scopedNatNames.clear()
  for natName in priorNatNames: scopedNatNames.incl(natName)
  let genericStr = if genericBinders.len == 0: ""
                   else: " " & genericBinders.join(" ")
  "proc " & name & genericStr & " " & paramStrs.join(" ") & " : " & retTy &
    " = " & body & "\n"

proc defCallToEponym(st: NimNode): string =
  ## def(isZero, Nat -> Bool):
  ##   clause([zero], true)
  ##   clause([suc(n)], false)
  ## -> def isZero : Nat -> Bool / | zero = true / | (suc n) = false
  ## (issue #151: clause-style definitions embedded; issue #42: reused
  ## for defs inside a mutual block).
  if st.len < 4 or st[1].kind != nnkIdent:
    error("def expects (name, type) with a block of clause([pats], rhs)", st)
  result = "def " & $st[1] & " : " & nimTypeToEponym(st[2]) & "\n"
  let blk = st[st.len - 1]
  if blk.kind != nnkStmtList:
    error("def expects a block of clause([pats], rhs) statements", st)
  for c in blk:
    if c.kind != nnkCall or c[0].kind != nnkIdent or $c[0] != "clause":
      error("def block expects clause([pattern, ...], rhs) statements", c)
    if c.len != 3 or c[1].kind != nnkBracket:
      error("clause expects ([pattern, ...], rhs)", c)
    var pats: seq[string] = @[]
    for p in c[1]: pats.add(patToEponym(p))
    result.add("| " & pats.join(" ") & " = " & nimExprToEponym(c[2]) & "\n")

type DiagnosticSourceLoc = tuple[filename: string, line, column: int]

proc diagnosticSourceLoc(n: NimNode): DiagnosticSourceLoc =
  ## The string form puts each checked definition on one line. Prefer the
  ## source location of its final body expression so elaboration errors point
  ## to the user expression rather than the generated string line.
  if n.kind == nnkProcDef and n.len > 6:
    var body = n[6]
    while body.kind == nnkStmtList and body.len > 0:
      body = body[^1]
    if not body.isNil:
      let info = body.lineInfoObj
      return (info.filename, info.line, info.column)
  let info = n.lineInfoObj
  (info.filename, info.line, info.column)

proc blockToEponymInternal(body: NimNode, sourceDir: string,
    sourceLineMap: var seq[DiagnosticSourceLoc], captureSourceMap: bool): string =
  ## Convert a block of Nim AST to Eponym source program.
  let baseDir = if sourceDir.len > 0: sourceDir else: callerDir(body)
  registerNimLegacyInfo(body, baseDir)
  result = ""
  for st in body:
    let statementStart = result.len
    case st.kind
    of nnkProcDef:
      result.add(procDefToEponym(st))
    of nnkImportStmt:
      # Issue #131: import "../../lib/nat.ep" -> import "../../lib/nat.ep"
      # (Eponym source line). Paths resolve relative to the Nim file
      # containing the eponymBlock call (see the eponymBlock macro below).
      for p in st:
        if p.kind != nnkStrLit:
          error("eponymBlock: import expects a string path, e.g. import \"lib/nat.ep\"", p)
        result.add("import \"" & p.strVal & "\"\n")
    of nnkCall:
      let head = $st[0]
      if head == "postulate":
        # postulate(Int, Univ) -> postulate Int : Type 0
        if st.len != 3: error("postulate expects (name, type)", st)
        result.add("postulate " & $st[1] & " : " & nimTypeToEponym(st[2]) & "\n")
      elif head == "elim":
        # elim(boolElim, Pi(C: Bool -> Univ, ...)) -> elim boolElim : Pi ...
        # (issue #151: smoke tests 07/08 embedded)
        if st.len != 3 or st[1].kind != nnkIdent:
          error("elim expects (name, type)", st)
        result.add("elim " & $st[1] & " : " & nimTypeToEponym(st[2]) & "\n")
      elif head == "red":
        # red(boolElim(C, t, f, true), t) -> red boolElim C t f true = t
        # (issue #151: smoke tests 07/08 embedded)
        if st.len != 3:
          error("red expects (lhs, rhs)", st)
        result.add("red " & nimExprToEponym(st[1]) & " = " &
                   nimExprToEponym(st[2]) & "\n")
      elif head == "def":
        result.add(defCallToEponym(st))
      elif head == "mutual":
        # mutual:
        #   def(even, Nat -> Bool): clause([zero], true) ...
        #   def(odd, Nat -> Bool): ...
        # -> mutual / def even : ... / | ... / def odd : ... / | ...
        # (issue #42: mutual blocks embedded)
        if st.len != 2:
          error("mutual expects a block of def(name, type) groups", st)
        let mblk = st[1]
        if mblk.kind != nnkStmtList:
          error("mutual expects a block of def(name, type) groups", st)
        result.add("mutual\n")
        var ndefs = 0
        for d in mblk:
          if d.kind != nnkCall or d[0].kind != nnkIdent or $d[0] != "def":
            error("mutual block expects def(name, type) groups", d)
          result.add(defCallToEponym(d))
          inc ndefs
        if ndefs == 0:
          error("mutual needs at least one def group", st)
      elif head == "data":
        # data(Nat, Univ): block -> data Nat : Type 0 where | ...
        # data(Vec, [A: Univ], Nat -> Univ): block -> data Vec (A : Type 0) : Nat -> Type 0 where | ...
        if st.len < 3: error("data expects (name, type) with block", st)
        let name = $st[1]
        # Check if we have params: data(Vec, [A: Univ], kind)
        var paramStr = ""
        var tyNode: NimNode
        var blkIdx: int
        if st[2].kind == nnkBracket:
          # Parameterized: data(Name, [params], kind)
          if st.len < 5: error("data with params expects (name, [params], kind) with block", st)
          let params = st[2]
          var pStrs: seq[string] = @[]
          for p in params:
            # p is ExprColonExpr(A, Univ) or IdentDefs?
            if p.kind == nnkExprColonExpr:
              pStrs.add("(" & $p[0] & " : " & nimTypeToEponym(p[1]) & ")")
            else:
              error("data params must be [name: type]", p)
          paramStr = " " & pStrs.join(" ")
          tyNode = st[3]
          blkIdx = 4
        else:
          # Simple: data(Name, kind)
          tyNode = st[2]
          blkIdx = 3
        let ty = nimTypeToEponym(tyNode)
        result.add("data " & name & paramStr & " : " & ty & " where\n")
        # The block is at blkIdx
        let blk = st[blkIdx]
        if blk.kind != nnkStmtList:
          error("data expects a block of constructors", st)
        for ctor in blk:
          if ctor.kind != nnkProcDef:
            error("data block expects proc constructors", ctor)
          var cname = $ctor[0]
          # Map Nim-safe names to Eponym names (nil is a Nim keyword)
          if cname == "vecnil": cname = "nil"
          let cparams = ctor[3]
          var cparamStrs: seq[string] = @[]
          var cretTy = "?"
          if cparams.len > 0 and cparams[0].kind != nnkEmpty:
            cretTy = nimTypeToEponym(cparams[0])
          for i in 1 ..< cparams.len:
            let p = cparams[i]
            let ty2 = nimTypeToEponym(p[^2])
            for j in 0 ..< p.len - 2:
              let q = qtyPrefix(p[j])
              cparamStrs.add("(" & q & binderName(p[j]) & " : " & ty2 & ")")
          result.add("| " & cname & " " & cparamStrs.join(" ") & " : " & cretTy & "\n")
      elif head == "record":
        # record(Point): block -> record Point: | ...
        # block statements are field(name, Type) calls (issue #37)
        if st.len != 3 or st[1].kind != nnkIdent:
          error("record expects (name) with a block of field(name, type)", st)
        let name = $st[1]
        result.add("record " & name & ":\n")
        let blk = st[2]
        if blk.kind != nnkStmtList:
          error("record expects a block of field(name, type) statements", st)
        for f in blk:
          if f.kind != nnkCall or f[0].kind != nnkIdent or $f[0] != "field":
            error("record block expects field(name, type) statements", f)
          if f.len != 3 or f[1].kind != nnkIdent:
            error("field expects (name, type)", f)
          result.add("| " & $f[1] & " : " & nimTypeToEponym(f[2]) & "\n")
      elif head == "bindPostulate":
        # Host binding is consumed by eponymBlock after checking its Eponym
        # contract; it is not part of the Eponym source text.
        if st.len < 3 or st[1].kind != nnkIdent:
          error("bindPostulate expects (postulateName, nimProcedure[, EponymType...])", st)
      elif head == "bindPostulateValue":
        # Deliberate raw runtime escape hatch; the Nim adapter owns codecs.
        if st.len != 3 or st[1].kind != nnkIdent:
          error("bindPostulateValue expects (postulateName, nimProcedure)", st)
      elif head == "bindPostulateMutable":
        # Explicit mutable-local adapter; host mutation is trusted and its
        # resulting value must be returned through the postulate result.
        if st.len < 4 or st[1].kind != nnkIdent:
          error("bindPostulateMutable expects (postulateName, nimProcedure, EponymArgument[, ...], EponymResult)", st)
        for i in 3 ..< st.len:
          if st[i].kind != nnkIdent:
            error("bindPostulateMutable Eponym types must be identifiers", st[i])
      elif head == "bindPostulatePair":
        # Typed adapter for A1 -> ... -> An -> Sig(B, C).
        if st.len notin {6, 7, 8} or st[1].kind != nnkIdent:
          error("bindPostulatePair expects (name, nimProc, Argument[, Argument...], First, Second)", st)
        for i in 3 ..< st.len:
          if st[i].kind != nnkIdent:
            error("bindPostulatePair Eponym types must be identifiers", st[i])
      elif head == "bindPostulatePairTrusted":
        # Same codec as bindPostulatePair, with a trusted dependent index.
        if st.len notin {6, 7, 8} or st[1].kind != nnkIdent:
          error("bindPostulatePairTrusted expects (name, nimProc, Argument[, Argument...], First, Second)", st)
        for i in 3 ..< st.len:
          if st[i].kind != nnkIdent:
            error("bindPostulatePairTrusted Eponym types must be identifiers", st[i])
      elif head == "runtimeType":
        # Explicit opaque Nim/Eponym representation mapping, consumed by the
        # wrapper generator and never interpreted as an Eponym declaration.
        if st.len != 3 or st[1].kind != nnkIdent:
          error("runtimeType expects (EponymType, NimType)", st)
      elif head == "runtimeCodec":
        # Typed host codec for any named Eponym type or family.
        if st.len != 5 or st[1].kind != nnkIdent or
            st[3].kind notin {nnkIdent, nnkSym} or
            st[4].kind notin {nnkIdent, nnkSym}:
          error("runtimeCodec expects (EponymType, NimType, encoder, decoder)",
            st)
      elif head == "runtimeVector":
        # Structural runtime codec for a Vec family with canonical nil/cons
        # constructor names.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeVector expects (VecFamily)", st)
      elif head == "runtimeList":
        # Structural runtime codec for a List family with canonical nil/cons.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeList expects (ListFamily)", st)
      elif head == "runtimeOption":
        # Structural runtime codec for a unary Option family.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeOption expects (OptionFamily)", st)
      elif head == "runtimeVariant":
        # Raw structural codec for payload-bearing data families.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeVariant expects (DataFamily)", st)
      elif head == "runtimeValue":
        # Request a raw Eponym Value wrapper for a checked definition,
        # typically for a host interpreter of reified data.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeValue expects (checkedDefinition)", st)
      elif head == "runtimePairTrusted":
        # Explicitly trust the host correspondence for dependent Sigma indices
        # in one generated definition's typed runtime interface.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimePairTrusted expects (checkedDefinition)", st)
      elif head == "runtimeRecordTrusted":
        # Explicitly trust host values to satisfy dependent record indices;
        # codecs still enforce any structural constraints they represent.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeRecordTrusted expects (RecordType)", st)
      else:
        error("eponymBlock: unsupported call: " & head, st)
    else:
      error("eponymBlock: unsupported statement: " & $st.kind, st)
    if captureSourceMap:
      let emittedLines = result[statementStart ..< result.len].count('\n')
      let sourceLoc = diagnosticSourceLoc(st)
      for _ in 0 ..< emittedLines:
        sourceLineMap.add(sourceLoc)

proc sourceMappedDiagnostic(message: string, loc: Loc,
    sourceLineMap: seq[DiagnosticSourceLoc]): string =
  if loc.line <= 0 or loc.line > sourceLineMap.len:
    return message
  let sourceLoc = sourceLineMap[loc.line - 1]
  if sourceLoc.filename.len == 0 or sourceLoc.line <= 0:
    return message
  let details = message.split(": ", 1)
  let explanation = if details.len > 1: details[1] else: message
  sourceLoc.filename & "(" & $sourceLoc.line & ", " &
    $sourceLoc.column & "): " & explanation

proc blockToEponym*(body: NimNode, sourceDir = ""): string =
  var ignoredSourceLineMap: seq[DiagnosticSourceLoc]
  blockToEponymInternal(body, sourceDir, ignoredSourceLineMap, false)

type HostPostulateBinding = object
  postulateName: string
  implementation: NimNode
  eponymTypes: seq[string]
  pairResultType: NimNode
  pairResultArgNames: seq[string]
  pairResult: bool
  pairArgCount: int
  trustedPairIndex: bool
  rawValue: bool
  mutableArgs: bool

proc isSyntheticGenericRuntimeType(mapping: HostRuntimeType): bool =
  mapping.nimType.kind in {nnkIdent, nnkSym} and
    $mapping.nimType == mapping.eponymName

proc mentionsName(node: NimNode, name: string): bool

type HostRecordField = object
  name: string
  eponymType: NimNode

type HostRecord = object
  name: string
  fields: seq[HostRecordField]
  hasDependentField: bool
  isVariant: bool
  constructors: seq[string]
  trustDependentFields: bool

proc hostRecords(body: NimNode,
                 trustedDependent: HashSet[string]): seq[HostRecord] =
  for st in body:
    if st.kind != nnkCall or st.len == 0 or st[0].kind != nnkIdent:
      continue
    let isRecord = $st[0] == "record" and st.len == 3 and
      st[2].kind == nnkStmtList
    let isVariant = $st[0] == "data" and st.len == 4 and
      st[3].kind == nnkStmtList
    if (not isRecord and not isVariant) or st[1].kind != nnkIdent:
      continue
    var record = HostRecord(name: $st[1], isVariant: isVariant,
      trustDependentFields: $st[1] in trustedDependent)
    if isVariant:
      for ctor in st[3]:
        if ctor.kind != nnkProcDef or ctor[0].kind != nnkIdent or
            ctor[3].kind != nnkFormalParams or ctor[3].len != 1 or
            ctor[3][0].kind != nnkIdent or $ctor[3][0] != record.name:
          record.hasDependentField = true
          break
        record.constructors.add($ctor[0])
      if record.constructors.len == 0:
        record.hasDependentField = true
      result.add(record)
      continue
    for field in st[2]:
      if field.kind != nnkCall or field.len != 3 or
          field[0].kind != nnkIdent or $field[0] != "field" or
          field[1].kind != nnkIdent:
        continue # blockToEponym reports malformed record fields
      let fieldType = field[2]
      for previous in record.fields:
        if mentionsName(fieldType, previous.name):
          record.hasDependentField = true
      record.fields.add(HostRecordField(name: $field[1],
                                         eponymType: fieldType))
    result.add(record)

proc findHostRecord(records: seq[HostRecord], name: string): int =
  for i, record in records:
    if record.name == name: return i
  -1

proc hostRuntimeTypes(body: NimNode, checkedGlobals: Globals):
    seq[HostRuntimeType] =
  var seen = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] in ["runtimeType", "runtimeVector", "runtimeList",
                   "runtimeOption", "runtimeVariant", "runtimeCodec"]:
      let isVector = $st[0] == "runtimeVector"
      let isList = $st[0] == "runtimeList"
      let isOption = $st[0] == "runtimeOption"
      let isVariant = $st[0] == "runtimeVariant"
      let isCodec = $st[0] == "runtimeCodec"
      if ((isVector or isList or isOption or isVariant) and
          (st.len != 2 or st[1].kind != nnkIdent)) or
          (isCodec and (st.len != 5 or st[1].kind != nnkIdent or
            st[3].kind notin {nnkIdent, nnkSym} or
            st[4].kind notin {nnkIdent, nnkSym})) or
          (not isVector and not isList and not isOption and not isVariant and
            not isCodec and
            (st.len != 3 or st[1].kind != nnkIdent)):
        error(if isVector: "runtimeVector expects (VecFamily)"
          elif isList: "runtimeList expects (ListFamily)"
          elif isOption: "runtimeOption expects (OptionFamily)"
          elif isVariant: "runtimeVariant expects (DataFamily)"
          elif isCodec: "runtimeCodec expects (EponymType, NimType, encoder, decoder)"
          else: "runtimeType expects (EponymType, NimType)", st)
      let name = $st[1]
      if name in seen:
        error("duplicate runtime type mapping for '" & name & "'", st)
      seen.incl(name)
      var genericTypeWitnessable = not isCodec
      if isCodec and name in checkedGlobals:
        let checkedType = checkedGlobals[name].ty
        genericTypeWitnessable = not checkedType.isNil and
          checkedType.kind == tType and checkedType.lvl == 0
      result.add(HostRuntimeType(eponymName: name,
        nimType: if isVector or isList: ident"seq"
          elif isVariant: bindSym"RuntimeVariant"
          elif isOption: ident"Option" else: st[2],
        isRuntimeVector: isVector, isRuntimeList: isList,
        isRuntimeOption: isOption, isRuntimeVariant: isVariant,
        isRuntimeCodec: isCodec,
        isGenericTypeWitnessable: genericTypeWitnessable,
        encoder: if isCodec: st[3] else: nil,
        decoder: if isCodec: st[4] else: nil))

proc validateHostBoolCodec(globals: Globals) =
  if "Bool" notin globals:
    raise newException(ValueError, "Bool is not declared; import bool.ep")
  let boolId = globals["Bool"].tm.refId
  for constructorName in ["true", "false"]:
    if constructorName notin globals:
      raise newException(ValueError,
        "Bool constructor '" & constructorName & "' is not declared; import bool.ep")
    let constructor = globals[constructorName]
    if not constructor.isDataConstructor or constructor.ty.isNil or
        constructor.ty.kind != tR or constructor.ty.refId != boolId:
      raise newException(ValueError,
        "Bool codec requires '" & constructorName & "' to construct Bool")

proc runtimeTypeAfterArgs(n: NimNode, count: int,
    argNames: var seq[string]): NimNode =
  ## Extract the result type after the explicit arrows/Pi binders accepted by
  ## a typed pair adapter. Keep this original type AST so dependent Sigma
  ## codecs can see the actual index expressions from the postulate.
  if count < 0: return nil
  if count == 0: return copyNimTree(n)
  if n.kind == nnkInfix and n.len == 3 and $n[0] == "->":
    argNames.add("")
    return runtimeTypeAfterArgs(n[2], count - 1, argNames)
  if n.kind in {nnkCall, nnkObjConstr} and n.len >= 3 and
      n[0].kind == nnkIdent and $n[0] == "Pi":
    var remaining = count
    for i in 1 ..< n.len - 1:
      let binder = n[i]
      if binder.kind == nnkExprColonExpr:
        argNames.add(binderName(binder[0]))
        dec remaining
      elif binder.kind == nnkTableConstr:
        for _ in binder: argNames.add("")
        remaining -= binder.len
      else:
        return nil
      if remaining < 0: return nil
    return runtimeTypeAfterArgs(n[^1], remaining, argNames)
  nil

proc runtimeTermTypeAst(term: Term, ctx: seq[string],
    refNames: Table[int, string]): NimNode =
  if term.isNil: return nil
  case term.kind
  of tR:
    if term.refId in refNames: ident(refNames[term.refId]) else: nil
  of tV:
    if term.idx >= 0 and term.idx < ctx.len: ident(ctx[term.idx]) else: nil
  of tPi, tSi:
    if term.kind == tPi:
      var callbackParams = newNimNode(nnkFormalParams)
      callbackParams.add(newEmptyNode())
      var callbackCtx = ctx
      var callbackNames: seq[string] = @[]
      var current = term
      var argumentIndex = 0
      while not current.isNil and current.kind == tPi:
        if current.impl or current.qty != qOmega or current.dom.isNil or
            current.dom.kind == tType:
          return nil
        var name = if current.scope.adv.len > 0 and
            current.scope.adv != "_": current.scope.adv
          else: "runtimeCallbackArg" & $argumentIndex
        if name in ctx or name in callbackNames:
          name = "runtimeCallbackArg" & $argumentIndex
          while name in ctx or name in callbackNames:
            name.add('_')
        let argType = runtimeTermTypeAst(current.dom, callbackCtx, refNames)
        if argType.isNil: return nil
        callbackParams.add(newIdentDefs(ident(name), argType,
          newEmptyNode()))
        callbackNames.add(name)
        callbackCtx = @[name] & callbackCtx
        current = current.scope.bdy
        inc argumentIndex
      let callbackResult = runtimeTermTypeAst(current, callbackCtx, refNames)
      if callbackResult.isNil: return nil
      callbackParams[0] = callbackResult
      result = newNimNode(nnkProcTy)
      result.add(callbackParams)
      var callbackPragmas = newNimNode(nnkPragma)
      callbackPragmas.add(ident"closure")
      result.add(callbackPragmas)
      return
    let binderName = if term.scope.adv.len > 0 and term.scope.adv != "_":
      term.scope.adv else: "runtimeIndex" & $ctx.len
    let domain = runtimeTermTypeAst(term.dom, ctx, refNames)
    let body = runtimeTermTypeAst(term.scope.bdy,
      @[binderName] & ctx, refNames)
    if domain.isNil or body.isNil: return nil
    let binder = newTree(nnkExprColonExpr, ident(binderName), domain)
    newCall(if term.kind == tPi: ident"Pi" else: ident"Sig", binder, body)
  of tApp:
    var args: seq[Term] = @[]
    var head = term
    while not head.isNil and head.kind == tApp:
      args.add(head.arg)
      head = head.fn
    let callee = runtimeTermTypeAst(head, ctx, refNames)
    if callee.isNil: return nil
    var application = newCall(callee)
    for i in countdown(args.high, 0):
      let arg = runtimeTermTypeAst(args[i], ctx, refNames)
      if arg.isNil: return nil
      application.add(arg)
    application
  of tInt: newLit(term.intVal)
  of tNatLit: newLit(term.natLitVal)
  of tNatSing: newLit(term.natSingVal)
  of tType:
    if term.lvl == 0: ident"Univ" else: nil
  else: nil

proc runtimeTermTypeAfterArgs(ty: Term, count: int, globals: Globals):
    tuple[resultType: NimNode, argNames: seq[string]] =
  var current = ty
  for i in 0 ..< count:
    if current.isNil or current.kind != tPi: return
    let binderName = if current.scope.adv.len > 0 and
        current.scope.adv != "_": current.scope.adv
      else: "runtimePairArg" & $i
    result.argNames.add(if current.scope.adv == "_": "" else: binderName)
    current = current.scope.bdy
  var refNames = initTable[int, string]()
  for name, entry in globals:
    if not entry.tm.isNil and entry.tm.kind == tR:
      refNames[entry.tm.refId] = name
  var ctx = newSeq[string](result.argNames.len)
  for i, name in result.argNames:
    ctx[result.argNames.high - i] = if name.len == 0:
      "runtimePairArg" & $i else: name
  result.resultType = runtimeTermTypeAst(current, ctx, refNames)

proc importedRuntimeProcDecl(definition: ElabDef,
                             globals: Globals): NimNode =
  ## Rebuild a simple imported Pi signature as a synthetic Nim proc AST so
  ## the ordinary codec generator can emit typed wrappers for it.
  var refNames = initTable[int, string]()
  for name, entry in globals:
    if not entry.tm.isNil and entry.tm.kind == tR:
      refNames[entry.tm.refId] = name
  var current = definition.tyTm
  var ctx: seq[string] = @[]
  var genericParams = newNimNode(nnkGenericParams)
  var formal = newNimNode(nnkFormalParams)
  formal.add(newEmptyNode())
  var argumentIndex = 0
  var genericIndex = 0
  while not current.isNil and current.kind == tPi:
    if current.impl or current.dom.isNil:
      return nil
    var name = if current.scope.adv.len > 0 and
        current.scope.adv != "_": current.scope.adv
      else: (if current.dom.kind == tType: "RuntimeType" & $genericIndex
             else: "runtimeArg" & $argumentIndex)
    if name in ctx:
      name = (if current.dom.kind == tType: "RuntimeType" & $genericIndex
              else: "runtimeArg" & $argumentIndex)
      while name in ctx:
        name.add('_')
    if current.dom.kind == tType:
      if current.dom.lvl != 0:
        return nil
      genericParams.add(newIdentDefs(ident(name), ident"Univ",
        newEmptyNode()))
      ctx = @[name] & ctx
      current = current.scope.bdy
      inc genericIndex
      continue
    let argType = runtimeTermTypeAst(current.dom, ctx, refNames)
    if argType.isNil: return nil
    formal.add(newIdentDefs(ident(name), argType, newEmptyNode()))
    ctx = @[name] & ctx
    current = current.scope.bdy
    inc argumentIndex
  if argumentIndex == 0: return nil
  let resultType = runtimeTermTypeAst(current, ctx, refNames)
  if resultType.isNil: return nil
  formal[0] = resultType
  result = newNimNode(nnkProcDef)
  result.add(ident(definition.name))
  result.add(newEmptyNode())
  result.add(if genericParams.len > 0: genericParams else: newEmptyNode())
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(newEmptyNode())

proc hostPostulateBindings(body: NimNode): seq[HostPostulateBinding] =
  var seen = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] in ["bindPostulate", "bindPostulateValue", "bindPostulatePair",
                   "bindPostulatePairTrusted", "bindPostulateMutable"]:
      let rawValue = $st[0] == "bindPostulateValue"
      let mutableArgs = $st[0] == "bindPostulateMutable"
      let pairResult = $st[0] in ["bindPostulatePair", "bindPostulatePairTrusted"]
      let trustedPairIndex = $st[0] == "bindPostulatePairTrusted"
      if pairResult:
        if st.len notin {6, 7, 8} or st[1].kind != nnkIdent:
          error($st[0] & " expects (name, nimProc, Argument[, Argument...], First, Second)", st)
      elif st.len < 3 or st[1].kind != nnkIdent:
        error("bindPostulate expects (postulateName, nimProcedure[, EponymType...])", st)
      let name = $st[1]
      if name in seen:
        error("duplicate bindPostulate for '" & name & "'", st)
      seen.incl(name)
      var typeNames: seq[string] = @[]
      for i in 3 ..< st.len:
        if st[i].kind != nnkIdent:
          error("bindPostulate Eponym type mappings must be identifiers", st[i])
        typeNames.add($st[i])
      var pairResultType: NimNode = nil
      var pairResultArgNames: seq[string] = @[]
      if pairResult:
        for declaration in body:
          if declaration.kind == nnkCall and declaration.len == 3 and
              declaration[0].kind == nnkIdent and
              $declaration[0] == "postulate" and
              declaration[1].kind == nnkIdent and
              $declaration[1] == name:
            pairResultType = runtimeTypeAfterArgs(declaration[2],
              typeNames.len - 2, pairResultArgNames)
            break
      result.add(HostPostulateBinding(postulateName: name,
                                     implementation: st[2],
                                     eponymTypes: typeNames,
                                     pairResultType: pairResultType,
                                     pairResultArgNames: pairResultArgNames,
                                     pairResult: pairResult,
                                     pairArgCount: if pairResult:
                                       typeNames.len - 2 else: 0,
                                     trustedPairIndex: trustedPairIndex,
                                     rawValue: rawValue,
                                     mutableArgs: mutableArgs))

proc mentionsName(node: NimNode, name: string): bool =
  if node.kind in {nnkIdent, nnkSym} and $node == name:
    return true
  for child in node:
    if mentionsName(child, name):
      return true

proc bindingIsReferenced(body: NimNode, postulateName: string): bool =
  ## A binding is useful only if some checked proc body calls its postulate.
  ## This deliberately checks direct references; call-graph reachability is a
  ## separate question because any generated wrapper can be called by Nim.
  for st in body:
    if st.kind == nnkProcDef and st.len > 6 and
        mentionsName(st[6], postulateName):
      return true

proc termReferencesRef(term: Term, refId: int): bool =
  ## Whether a checked term mentions a global, including under binders.
  if term.isNil: return false
  case term.kind
  of tR: term.refId == refId
  of tPi, tSi, tLam:
    termReferencesRef(term.dom, refId) or
      termReferencesRef(term.scope.bdy, refId)
  of tPair:
    termReferencesRef(term.pFst, refId) or
      termReferencesRef(term.pSnd, refId) or
      termReferencesRef(term.pScope.bdy, refId)
  of tApp: termReferencesRef(term.fn, refId) or termReferencesRef(term.arg, refId)
  of tFst, tSnd, tAbsurd: termReferencesRef(term.sub, refId)
  of tLet:
    termReferencesRef(term.letVal, refId) or
      termReferencesRef(term.letTy, refId) or
      termReferencesRef(term.letScope.bdy, refId)
  of tMeta:
    for item in term.metaSpine:
      if termReferencesRef(item, refId): return true
    false
  of tV, tC, tType, tInt, tNatLit, tNatSing, tPrim: false

proc checkedDefReferences(definition: ElabDef, refId: int): bool =
  termReferencesRef(definition.tyTm, refId) or
    termReferencesRef(definition.tmTm, refId)

proc bindingIsReferenced(body: NimNode, postulateName: string,
                         allDefs: seq[ElabDef], globals: Globals): bool =
  ## Keep checking local Nim bodies, and include checked imported bodies.
  if bindingIsReferenced(body, postulateName): return true
  if postulateName notin globals: return false
  let refId = globals[postulateName].tm.refId
  for definition in allDefs:
    if checkedDefReferences(definition, refId): return true
  false

proc trustBoundaryReportLines(bindings: seq[HostPostulateBinding],
    mappings: seq[HostRuntimeType], trustedPairs, trustedRecords: HashSet[string]):
    seq[string] =
  ## Human-readable inventory of explicit block-level host trust boundaries.
  for binding in bindings:
    var form = "bindPostulate"
    var promise = "the Nim adapter behavior is trusted; " &
      "its signature is checked"
    if binding.rawValue:
      form = "bindPostulateValue"
      promise = "the raw RuntimeValue adapter behavior and " &
        "interpretation are trusted"
    elif binding.pairResult:
      form = if binding.trustedPairIndex:
        "bindPostulatePairTrusted" else: "bindPostulatePair"
      if binding.trustedPairIndex:
        promise = "the host result's dependent Sigma index relationship is trusted"
      else:
        promise = "the generated non-dependent pair codec checks field " &
          "types; adapter behavior is trusted"
    elif binding.mutableArgs:
      form = "bindPostulateMutable"
      promise = "the adapter mutates decoded local var arguments and returns " &
        "their encoded result; host effects and aliases are trusted"
    result.add(form & "(" & binding.postulateName & ", " &
      binding.implementation.repr & "): " & promise)

  for mapping in mappings:
    if mapping.isRuntimeCodec:
      result.add("runtimeCodec(" & mapping.eponymName & ", " &
        mapping.nimType.repr & "): custom encoder/decoder behavior " &
        "is trusted")
    elif not mapping.isRuntimeVector and not mapping.isRuntimeList and
        not mapping.isRuntimeOption and not mapping.isRuntimeVariant:
      result.add("runtimeType(" & mapping.eponymName & ", " &
        mapping.nimType.repr & "): Nim/Eponym type correspondence is " &
        "trusted; host identity, aliasing, and lifetime rules remain with " &
        "the caller")

  var pairNames = toSeq(trustedPairs.items)
  pairNames.sort()
  for name in pairNames:
    result.add("runtimePairTrusted(" & name & "): typed wrappers trust " &
      "dependent Sigma index relationships not reconstructed by codecs")
  var recordNames = toSeq(trustedRecords.items)
  recordNames.sort()
  for name in recordNames:
    result.add("runtimeRecordTrusted(" & name & "): typed wrappers trust " &
      "dependent record relationships not checked by field codecs")

proc isCheckedNatType(globals: Globals, typeName: string): bool =
  ## Classify Nat by the checked declaration's identity, not by its spelling.
  if "Nat" notin globals or typeName notin globals:
    return false
  let nat = globals["Nat"].tm
  let candidate = globals[typeName].tm
  not nat.isNil and not candidate.isNil and nat.kind == tR and
    candidate.kind == tR and nat.refId == candidate.refId

proc simpleRuntimeCodec(n: NimNode): string =
  if n.kind == nnkIdent:
    case $n
    of "Int": result = "int"
    of "Nat": result = "nat"
    of "Bool": result = "bool"
    else: result = ""

proc trustedRuntimePairNames(body: NimNode): HashSet[string] =
  result = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] == "runtimePairTrusted":
      let name = $st[1]
      if name in result:
        error("duplicate runtimePairTrusted declaration for '" & name & "'", st)
      result.incl(name)

proc trustedRuntimeRecordNames(body: NimNode): HashSet[string] =
  result = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] == "runtimeRecordTrusted":
      if st.len != 2 or st[1].kind != nnkIdent:
        error("runtimeRecordTrusted expects (RecordType)", st)
      let name = $st[1]
      if name in result:
        error("duplicate runtimeRecordTrusted declaration for '" & name & "'", st)
      result.incl(name)

proc runtimeSigmaComponents(n: NimNode, allowDependent = false):
    tuple[first, second: NimNode, binder: string] =
  ## Runtime tuples represent two-field Sig types. Unless the enclosing
  ## definition or record explicitly trusts dependent indices, reject a
  ## dependent tail rather than erase the first component from its type.
  if n.kind notin {nnkCall, nnkObjConstr} or n.len != 3 or
      n[0].kind != nnkIdent or
      $n[0] != "Sig":
    return
  if n[1].kind == nnkExprColonExpr:
    if n[1].len != 2 or n[1][0].kind != nnkIdent or
        (mentionsName(n[2], $n[1][0]) and not allowDependent):
      return
    return (n[1][1], n[2], $n[1][0])
  (n[1], n[2], "")

proc containsDependentSigma(n: NimNode): bool =
  if n.kind in {nnkCall, nnkObjConstr} and n.len == 3 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "Sig" and
      n[1].kind == nnkExprColonExpr and n[1].len == 2 and
      n[1][0].kind in {nnkIdent, nnkSym} and
      mentionsName(n[2], $n[1][0]):
    return true
  for child in n:
    if containsDependentSigma(child): return true

proc containsEponymPiType(n: NimNode): bool =
  if n.kind in {nnkCall, nnkObjConstr} and n.len >= 3 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "Pi":
    return true
  if n.kind == nnkInfix and n.len == 3 and $n[0] == "->":
    return true
  for child in n:
    if containsEponymPiType(child): return true

proc runtimeSigmaFields(n: NimNode, allowDependent = false):
    seq[tuple[fieldType: NimNode, binder: string]] =
  ## Flatten a right-nested Sigma telescope. Each field binder scopes over
  ## the remaining fields, matching Eponym's right-associated pair values.
  var current = n
  while current.kind in {nnkCall, nnkObjConstr} and current.len == 3 and
      current[0].kind in {nnkIdent, nnkSym} and $current[0] == "Sig":
    let binder = current[1]
    if binder.kind == nnkExprColonExpr:
      if binder.len != 2 or binder[0].kind notin {nnkIdent, nnkSym} or
          (mentionsName(current[2], $binder[0]) and not allowDependent):
        return @[]
      result.add((binder[1], $binder[0]))
    else:
      result.add((binder, ""))
    current = current[2]
  if result.len == 0: return
  result.add((current, ""))

proc runtimeVectorComponents(n: NimNode, familyName: string):
    tuple[elementType, length: NimNode] =
  if n.kind notin {nnkCall, nnkObjConstr, nnkBracketExpr} or n.len != 3 or
      n[0].kind != nnkIdent or $n[0] != familyName:
    return
  (n[1], n[2])

proc runtimeListElementType(n: NimNode, familyName: string): NimNode =
  if n.kind notin {nnkCall, nnkObjConstr, nnkBracketExpr} or n.len != 2 or
      n[0].kind != nnkIdent or $n[0] != familyName:
    return nil
  n[1]

proc runtimeOptionElementType(n: NimNode, familyName: string): NimNode =
  if n.kind notin {nnkCall, nnkObjConstr, nnkBracketExpr} or n.len != 2 or
      n[0].kind != nnkIdent or $n[0] != familyName:
    return nil
  n[1]

proc runtimeTypeHead(n: NimNode): NimNode =
  result = n
  while result.kind in {nnkCall, nnkCommand, nnkBracketExpr} and result.len > 0:
    result = result[0]

proc runtimeBoolIndexExpr(n: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]] = @[]): NimNode =
  ## Lower the Bool subset accepted in runtime conditional Nat indices.
  if n.kind in {nnkStmtListExpr, nnkPar}:
    if n.len != 1: return nil
    return runtimeBoolIndexExpr(n[0], overrides)
  if n.kind in {nnkIdent, nnkSym}:
    if overrides.len > 0:
      for i in countdown(overrides.high, 0):
        if $n == overrides[i].name:
          return copyNimTree(overrides[i].value)
    return copyNimTree(n)
  if n.kind == nnkPrefix and n.len == 2 and $n[0] == "not":
    let operand = runtimeBoolIndexExpr(n[1], overrides)
    if operand.isNil: return nil
    return newTree(nnkPrefix, copyNimTree(n[0]), operand)
  if n.kind == nnkInfix and n.len == 3 and $n[0] in ["and", "or"]:
    let left = runtimeBoolIndexExpr(n[1], overrides)
    let right = runtimeBoolIndexExpr(n[2], overrides)
    if left.isNil or right.isNil: return nil
    return newTree(nnkInfix, copyNimTree(n[0]), left, right)
  nil

proc runtimeNatIndexExpr(n: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]] = @[]): NimNode =
  ## Lower supported Nat index expressions to checked Nim int arithmetic,
  ## substituting nearer Sigma/record binders as ordinary Nim operands.
  if n.kind == nnkStmtListExpr:
    if n.len != 1: return nil
    return runtimeNatIndexExpr(n[0], overrides)
  if n.kind in {nnkIdent, nnkSym}:
    if overrides.len > 0:
      for i in countdown(overrides.high, 0):
        if $n == overrides[i].name:
          return copyNimTree(overrides[i].value)
    if $n == "zero": return newLit(0)
    return copyNimTree(n)
  if n.kind == nnkDotExpr:
    return copyNimTree(n)
  if n.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                nnkInt64Lit}:
    if n.intVal < 0: return nil
    return copyNimTree(n)
  if n.kind in {nnkIfExpr, nnkIfStmt}:
    var branches: seq[tuple[condition, value: NimNode]] = @[]
    var elseBranch: NimNode = nil
    for branch in n:
      case branch.kind
      of nnkElifExpr, nnkElifBranch:
        if branch.len != 2: return nil
        let condition = runtimeBoolIndexExpr(branch[0], overrides)
        if condition.isNil: return nil
        var valueNode = branch[1]
        if valueNode.kind == nnkStmtList:
          if valueNode.len != 1: return nil
          valueNode = valueNode[0]
        let value = runtimeNatIndexExpr(valueNode, overrides)
        if value.isNil: return nil
        branches.add((condition, value))
      of nnkElseExpr, nnkElse:
        if branch.len != 1: return nil
        elseBranch = branch[0]
      else:
        return nil
    if branches.len == 0 or elseBranch.isNil: return nil
    if elseBranch.kind == nnkStmtList:
      if elseBranch.len != 1: return nil
      elseBranch = elseBranch[0]
    result = runtimeNatIndexExpr(elseBranch, overrides)
    if result.isNil: return nil
    for i in countdown(branches.high, 0):
      result = newTree(nnkIfExpr,
        newTree(nnkElifExpr, branches[i].condition, branches[i].value),
        newTree(nnkElseExpr, result))
    return
  if n.kind == nnkCall and n.len >= 2 and n[0].kind == nnkIdent:
    case $n[0]
    of "suc":
      if n.len != 2: return nil
      let index = runtimeNatIndexExpr(n[1], overrides)
      if index.isNil: return nil
      return newCall(bindSym"natIndexSucc", index)
    of "add", "mul":
      if n.len != 3: return nil
      let left = runtimeNatIndexExpr(n[1], overrides)
      let right = runtimeNatIndexExpr(n[2], overrides)
      if left.isNil or right.isNil: return nil
      return newCall(if $n[0] == "add": bindSym"natIndexAdd" else:
        bindSym"natIndexMul", left, right)
  nil

proc runtimeIndexDependencyCodecSupports(n: NimNode, binder: string,
    mappings: seq[HostRuntimeType]): bool =
  ## Check that every occurrence of an outer Sigma index is guarded by a
  ## structural codec that validates the corresponding host value.
  if not mentionsName(n, binder): return true
  for mapping in mappings:
    if mapping.isRuntimeVector:
      let vector = runtimeVectorComponents(n, mapping.eponymName)
      if not vector.elementType.isNil and
          not runtimeNatIndexExpr(vector.length).isNil:
        return runtimeIndexDependencyCodecSupports(vector.elementType,
          binder, mappings)
    elif mapping.isRuntimeList:
      let elementType = runtimeListElementType(n, mapping.eponymName)
      if not elementType.isNil:
        return runtimeIndexDependencyCodecSupports(elementType, binder,
          mappings)
    elif mapping.isRuntimeOption:
      let elementType = runtimeOptionElementType(n, mapping.eponymName)
      if not elementType.isNil:
        return runtimeIndexDependencyCodecSupports(elementType, binder,
          mappings)
  let sigma = runtimeSigmaComponents(n, allowDependent = true)
  if not sigma.first.isNil:
    return runtimeIndexDependencyCodecSupports(sigma.first, binder,
      mappings) and runtimeIndexDependencyCodecSupports(sigma.second, binder,
      mappings)
  false

proc runtimeSigmaComponentsForCodec(n: NimNode,
    mappings: seq[HostRuntimeType], allowDependentSigma: bool):
    tuple[first, second: NimNode, binder: string] =
  ## A dependent pair can omit the trust opt-in only when the dependency is
  ## enforced by registered structural codecs: the preceding field must be
  ## Nat, and its name may occur only in index expressions where encoding
  ## checks the corresponding host values.
  result = runtimeSigmaComponents(n, allowDependentSigma)
  if not result.first.isNil or allowDependentSigma:
    return
  let dependent = runtimeSigmaComponents(n, allowDependent = true)
  if dependent.first.isNil or dependent.binder.len == 0 or
      simpleRuntimeCodec(dependent.first) != "nat":
    return
  if runtimeIndexDependencyCodecSupports(dependent.second, dependent.binder,
      mappings):
    return dependent

proc runtimeRecordDependenciesCodecSupported(record: HostRecord,
    mappings: seq[HostRuntimeType]): bool =
  ## A dependent record may omit its trust opt-in only when each earlier field
  ## used by a later field is Nat and every use is enforced by structural
  ## codecs such as Vec length checks.
  for i, field in record.fields:
    for earlierIndex in 0 ..< i:
      let earlier = record.fields[earlierIndex]
      if not mentionsName(field.eponymType, earlier.name):
        continue
      if simpleRuntimeCodec(earlier.eponymType) != "nat" or
          not runtimeIndexDependencyCodecSupports(field.eponymType,
            earlier.name, mappings):
        return false
  true

type RuntimeProcParts = object
  argTypes: seq[NimNode]
  argNames: seq[string]
  resultType: NimNode

proc runtimeProcParts(n: NimNode): RuntimeProcParts =
  if n.kind != nnkProcTy or n.len != 2 or n[0].kind != nnkFormalParams or
      n[0].len < 2:
    return
  for i in 1 ..< n[0].len:
    let p = n[0][i]
    if p.kind != nnkIdentDefs or p.len < 3:
      return RuntimeProcParts()
    for j in 0 ..< p.len - 2:
      result.argTypes.add(p[^2])
      result.argNames.add(if p[j].kind == nnkEmpty: "callbackArg" &
        $result.argNames.len else: binderName(p[j]))
  if result.argTypes.len > 0:
    result.resultType = n[0][0]

proc runtimeEponymPiParts(n: NimNode): RuntimeProcParts =
  var current = n
  while true:
    if current.kind in {nnkCall, nnkObjConstr} and current.len >= 3 and
        current[0].kind in {nnkIdent, nnkSym} and $current[0] == "Pi":
      for i in 1 ..< current.len - 1:
        let binder = current[i]
        if binder.kind != nnkExprColonExpr or binder.len != 2 or
            binder[0].kind notin {nnkIdent, nnkSym}:
          return RuntimeProcParts()
        result.argNames.add(binderName(binder[0]))
        result.argTypes.add(binder[1])
      current = current[^1]
    elif current.kind == nnkInfix and current.len == 3 and
        $current[0] == "->":
      result.argNames.add("runtimeCallbackArg" & $result.argNames.len)
      result.argTypes.add(current[1])
      current = current[2]
    else:
      break
  if result.argTypes.len == 0:
    return RuntimeProcParts()
  result.resultType = current

proc hasClosurePragma(n: NimNode): bool =
  if n.kind == nnkProcTy and n.len == 2 and n[1].kind == nnkPragma:
    for pragma in n[1]:
      if pragma.kind in {nnkIdent, nnkSym} and $pragma == "closure":
        return true

proc hasRawValuePragma(n: NimNode): bool =
  if n.kind == nnkProcTy and n.len == 2 and n[1].kind == nnkPragma:
    for pragma in n[1]:
      if pragma.kind in {nnkIdent, nnkSym} and $pragma == "rawValue":
        return true

proc rawValueCallbackType(n: NimNode): NimNode =
  result = copyNimTree(n)
  result[0][0] = bindSym"RuntimeValue"
  for i in 1 ..< result[0].len:
    result[0][i][^2] = bindSym"RuntimeValue"

proc runtimeNimType(n: NimNode, mappings: seq[HostRuntimeType],
                    records: seq[HostRecord],
                    allowDependentSigma = false): NimNode =
  let procParts = runtimeProcParts(n)
  if not procParts.resultType.isNil:
    if hasRawValuePragma(n): return rawValueCallbackType(n)
    let resultType = runtimeNimType(procParts.resultType, mappings, records,
                                    allowDependentSigma)
    if resultType.isNil: return nil
    result = copyNimTree(n)
    result[0][0] = resultType
    var argIndex = 0
    for i in 1 ..< result[0].len:
      let param = result[0][i]
      let argType = runtimeNimType(procParts.argTypes[argIndex], mappings,
        records, allowDependentSigma)
      if argType.isNil: return nil
      param[^2] = argType
      argIndex += param.len - 2
    return
  let eponymPi = runtimeEponymPiParts(n)
  if not eponymPi.resultType.isNil:
    let resultType = runtimeNimType(eponymPi.resultType, mappings, records,
                                    allowDependentSigma)
    if resultType.isNil: return nil
    var formal = newNimNode(nnkFormalParams)
    formal.add(resultType)
    for i, argTypeAst in eponymPi.argTypes:
      let argType = runtimeNimType(argTypeAst, mappings, records,
                                   allowDependentSigma)
      if argType.isNil: return nil
      formal.add(newIdentDefs(ident(eponymPi.argNames[i]), argType,
        newEmptyNode()))
    let closurePragma = newNimNode(nnkPragma)
    closurePragma.add(ident"closure")
    return newTree(nnkProcTy, formal, closurePragma)
  let typeHead = runtimeTypeHead(n)
  if typeHead.kind == nnkIdent:
    for mapping in mappings:
      if mapping.isRuntimeCodec and mapping.eponymName == $typeHead:
        return mapping.nimType
      if mapping.isRuntimeVariant and mapping.eponymName == $typeHead:
        return bindSym"RuntimeVariant"
  for mapping in mappings:
    if mapping.isRuntimeVector:
      let vector = runtimeVectorComponents(n, mapping.eponymName)
      if not vector.elementType.isNil:
        if runtimeNatIndexExpr(vector.length).isNil: return nil
        let elementType = runtimeNimType(vector.elementType, mappings,
          records, allowDependentSigma)
        if elementType.isNil: return nil
        return newTree(nnkBracketExpr, ident"seq", elementType)
    elif mapping.isRuntimeList:
      let listElement = runtimeListElementType(n, mapping.eponymName)
      if not listElement.isNil:
        let elementType = runtimeNimType(listElement, mappings, records,
          allowDependentSigma)
        if elementType.isNil: return nil
        return newTree(nnkBracketExpr, ident"seq", elementType)
    elif mapping.isRuntimeOption:
      let elementType = runtimeOptionElementType(n, mapping.eponymName)
      if not elementType.isNil:
        let nimElementType = runtimeNimType(elementType, mappings, records,
          allowDependentSigma)
        if nimElementType.isNil: return nil
        return newTree(nnkBracketExpr, bindSym"Option", nimElementType)
  let sigma = runtimeSigmaComponentsForCodec(n, mappings,
    allowDependentSigma)
  if not sigma.first.isNil:
    let first = runtimeNimType(sigma.first, mappings, records,
                               allowDependentSigma)
    let second = runtimeNimType(sigma.second, mappings, records,
                                allowDependentSigma)
    if first.isNil or second.isNil: return nil
    result = newNimNode(nnkTupleConstr)
    result.add(first)
    result.add(second)
    return
  var head = n
  while head.kind in {nnkCall, nnkCommand, nnkBracketExpr} and head.len > 0:
    head = head[0]
  if head.kind == nnkIdent:
    let recordIndex = findHostRecord(records, $head)
    if recordIndex >= 0:
      let record = records[recordIndex]
      if record.isVariant:
        if record.hasDependentField or record.constructors.len == 0:
          return nil
        for mapping in mappings:
          if mapping.eponymName == $head:
            return mapping.nimType
        return nil
      let dependenciesCodecChecked =
        runtimeRecordDependenciesCodecSupported(record, mappings)
      if (record.hasDependentField and not record.trustDependentFields and
          not dependenciesCodecChecked) or record.fields.len == 0:
        return nil
      let recordAllowsDependentFields = allowDependentSigma or
        record.trustDependentFields
      for field in record.fields:
        if runtimeNimType(field.eponymType, mappings, records,
                          recordAllowsDependentFields).isNil:
          return nil
      for mapping in mappings:
        if mapping.eponymName == $head:
          return mapping.nimType
      return nil
    case $head
    of "Int", "Nat": return ident("int")
    of "Bool": return ident("bool")
    else:
      for mapping in mappings:
        if mapping.eponymName == $head:
          return mapping.nimType
  nil

proc hasCodecBackedDynamicValueBinder(decl: NimNode,
    mappings: seq[HostRuntimeType], records: seq[HostRecord]): bool =
  if decl.kind != nnkProcDef or decl[2].kind == nnkEmpty: return false
  for param in decl[2]:
    if param.kind != nnkIdentDefs:
      continue
    let hasDependentSigma = containsDependentSigma(param[^2])
    let hasPi = containsEponymPiType(param[^2])
    if not hasDependentSigma and not hasPi:
      continue
    if runtimeNimType(param[^2], mappings, records,
        allowDependentSigma = true).isNil:
      continue
    # Avoid generating a duplicate when the ordinary dynamic wrapper already
    # has the same codec-backed host signature. Pi callbacks still need the
    # explicit function-value path even when their Nim type has a codec.
    if hasPi or runtimeNimType(param[^2], mappings, records).isNil:
      return true

proc runtimeValueConverter(eponymType, nimType: NimNode,
                           toValue: bool,
                           records: seq[HostRecord]): NimNode =
  if simpleRuntimeCodec(eponymType) == "int":
    if toValue: return bindSym"intToValue"
    return bindSym"valueToInt"
  if simpleRuntimeCodec(eponymType) == "nat":
    if toValue: return bindSym"natToValue"
    return bindSym"valueToNat"
  if simpleRuntimeCodec(eponymType) == "bool":
    if toValue: return bindSym"boolToValue"
    return bindSym"valueToBool"
  if eponymType.kind == nnkCall and eponymType.len == 3 and
      eponymType[0].kind == nnkIdent and $eponymType[0] == "Sig":
    return nil # handled structurally by runtimeValueConversionExpr
  if eponymType.kind == nnkIdent and findHostRecord(records, $eponymType) >= 0:
    return nil # handled structurally by runtimeValueConversionExpr
  let generic = if toValue: bindSym"toHostValue" else: bindSym"valueToHost"
  newTree(nnkBracketExpr, generic, nimType)

proc runtimeTypeValueExpr(n: NimNode, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]]): NimNode

proc runtimeTypeReferencesName(n: NimNode, name: string,
    shadowed: seq[string] = @[]): bool =
  if n.isNil: return false
  if n.kind in {nnkIdent, nnkSym}:
    return $n == name and name notin shadowed
  if n.kind in {nnkCall, nnkObjConstr} and n.len >= 3 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] in ["Pi", "Sig"]:
    var localShadowed = shadowed
    for i in 1 ..< n.len - 1:
      let binder = n[i]
      if binder.kind != nnkExprColonExpr or binder.len != 2:
        return true # Conservatively retain overrides for unknown syntax.
      if runtimeTypeReferencesName(binder[1], name, localShadowed):
        return true
      localShadowed.add($binder[0])
    return runtimeTypeReferencesName(n[^1], name, localShadowed)
  for child in n:
    if runtimeTypeReferencesName(child, name, shadowed): return true
  false

proc runtimePiTypeValueExpr(n, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]]): NimNode =
  if n.kind notin {nnkCall, nnkObjConstr} or n.len < 3 or
      n[0].kind notin {nnkIdent, nnkSym} or $n[0] != "Pi":
    return nil
  var binders: seq[tuple[name: string, domain: NimNode]] = @[]
  for i in 1 ..< n.len - 1:
    let binder = n[i]
    if binder.kind != nnkExprColonExpr or binder.len != 2 or
        binder[0].kind notin {nnkIdent, nnkSym}:
      return nil
    binders.add(($binder[0], binder[1]))
  proc build(index: int,
      localOverrides: seq[tuple[name: string, value: NimNode]]): NimNode =
    let domain = runtimeTypeValueExpr(binders[index].domain, globals,
      localOverrides)
    if domain.isNil: return nil
    let argument = genSym(nskParam, "runtimePiArgument")
    var codomainOverrides = localOverrides
    codomainOverrides.add((binders[index].name, argument))
    let codomain = if index + 1 < binders.len:
      build(index + 1, codomainOverrides)
    else:
      runtimeTypeValueExpr(n[^1], globals, codomainOverrides)
    if codomain.isNil: return nil
    let callback = newProc(
      params = @[bindSym"Value",
        newIdentDefs(argument, bindSym"Value", newEmptyNode())],
      body = newStmtList(codomain))
    var priorArguments = newNimNode(nnkBracket)
    for i, override in localOverrides:
      if i >= overrides.len or runtimeTypeReferencesName(n,
          overrides[i].name):
        priorArguments.add(copyNimTree(override.value))
    newCall(bindSym"runtimeDependentArrowType", domain, globals, callback,
      newTree(nnkPrefix, ident"@", priorArguments))
  build(0, overrides)

proc isGenericTypeWitnessMapping(mapping: HostRuntimeType): bool =
  not isSyntheticGenericRuntimeType(mapping) and
    not mapping.isRuntimeVector and not mapping.isRuntimeList and
    not mapping.isRuntimeOption and not mapping.isRuntimeVariant and
    (not mapping.isRuntimeCodec or mapping.isGenericTypeWitnessable)

proc runtimeGenericTypeWitnessExpr(n, globals: NimNode,
    mappings: seq[HostRuntimeType]): NimNode =
  if n.kind notin {nnkIdent, nnkSym}: return nil
  if $n in ["Int", "Nat", "Bool"]: return nil
  for mapping in mappings:
    if mapping.eponymName == $n and
        not isSyntheticGenericRuntimeType(mapping): return nil
  let typeName = copyNimTree(n)
  var branches = newNimNode(nnkWhenStmt)
  var candidateNames = initHashSet[string]()
  for mapping in mappings:
    if not isGenericTypeWitnessMapping(mapping): continue
    let nimTypeName = mapping.nimType.repr
    if nimTypeName.len == 0 or nimTypeName in candidateNames: continue
    var sameNimTypeCount = 0
    for other in mappings:
      if isGenericTypeWitnessMapping(other) and
          other.nimType.repr == nimTypeName:
        inc sameNimTypeCount
    if sameNimTypeCount != 1: continue
    candidateNames.incl(nimTypeName)
    let condition = newCall(newTree(nnkBracketExpr,
      bindSym"sameHostType", copyNimTree(typeName),
      copyNimTree(mapping.nimType)))
    let witness = newCall(bindSym"runtimeGlobalTypeWitness", globals,
      newLit(mapping.eponymName))
    branches.add(newTree(nnkElifBranch, condition,
      newStmtList(newAssignment(ident"runtimeTypeWitness", witness))))
  if branches.len == 0: return nil
  branches.add(newTree(nnkElse, newStmtList()))
  let witnessSym = ident"runtimeTypeWitness"
  let body = newStmtList(
    newTree(nnkVarSection,
      newIdentDefs(witnessSym, bindSym"Value", newNilLit())),
    branches,
    witnessSym)
  newTree(nnkBlockExpr, newEmptyNode(), body)

proc runtimeGenericCodecConversionExpr(eponymType, nimType, value: NimNode,
    toValue: bool, globals: NimNode, mappings: seq[HostRuntimeType],
    fallback: NimNode): NimNode =
  if eponymType.kind notin {nnkIdent, nnkSym}: return nil
  var isGenericTypeParameter = false
  for mapping in mappings:
    if mapping.eponymName == $eponymType and
        isSyntheticGenericRuntimeType(mapping):
      isGenericTypeParameter = true
      break
  if not isGenericTypeParameter: return nil

  var branches = newNimNode(nnkWhenStmt)
  var emitted = initHashSet[string]()
  for mapping in mappings:
    if not mapping.isRuntimeCodec or
        not isGenericTypeWitnessMapping(mapping):
      continue
    let nimTypeName = mapping.nimType.repr
    if nimTypeName.len == 0 or nimTypeName in emitted: continue
    var sameNimTypeCount = 0
    for other in mappings:
      if isGenericTypeWitnessMapping(other) and
          other.nimType.repr == nimTypeName:
        inc sameNimTypeCount
    if sameNimTypeCount != 1: continue
    emitted.incl(nimTypeName)
    let condition = newCall(newTree(nnkBracketExpr,
      bindSym"sameHostType", copyNimTree(nimType),
      copyNimTree(mapping.nimType)))
    let codec = copyNimTree(if toValue: mapping.encoder else: mapping.decoder)
    branches.add(newTree(nnkElifBranch, condition,
      newStmtList(newCall(codec, copyNimTree(value), globals))))
  if branches.len == 0: return nil
  branches.add(newTree(nnkElse, newStmtList(fallback)))
  newTree(nnkBlockExpr, newEmptyNode(), newStmtList(branches))

proc runtimeRepresentedTypeValueExpr(n, globals: NimNode,
    mappings: seq[HostRuntimeType],
    overrides: seq[tuple[name: string, value: NimNode]]): NimNode =
  for mapping in mappings:
    if mapping.isRuntimeVector:
      let vector = runtimeVectorComponents(n, mapping.eponymName)
      if not vector.elementType.isNil:
        let elementType = runtimeRepresentedTypeValueExpr(
          vector.elementType, globals, mappings, overrides)
        let length = runtimeNatIndexExpr(vector.length, overrides)
        if elementType.isNil or length.isNil: return nil
        return newCall(bindSym"callRuntimeValue",
          newCall(bindSym"runtimeGlobalValue", globals,
            newLit(mapping.eponymName)),
          newTree(nnkBracket, elementType,
            newCall(bindSym"natToValue", length, globals)))
    elif mapping.isRuntimeList:
      let elementType = runtimeListElementType(n, mapping.eponymName)
      if not elementType.isNil:
        let representedElement = runtimeRepresentedTypeValueExpr(
          elementType, globals, mappings, overrides)
        if representedElement.isNil: return nil
        return newCall(bindSym"callRuntimeValue",
          newCall(bindSym"runtimeGlobalValue", globals,
            newLit(mapping.eponymName)),
          newTree(nnkBracket, representedElement))
    elif mapping.isRuntimeOption:
      let elementType = runtimeOptionElementType(n, mapping.eponymName)
      if not elementType.isNil:
        let representedElement = runtimeRepresentedTypeValueExpr(
          elementType, globals, mappings, overrides)
        if representedElement.isNil: return nil
        return newCall(bindSym"callRuntimeValue",
          newCall(bindSym"runtimeGlobalValue", globals,
            newLit(mapping.eponymName)),
          newTree(nnkBracket, representedElement))
  if n.kind in {nnkIdent, nnkSym}:
    let genericWitness = runtimeGenericTypeWitnessExpr(n, globals, mappings)
    if not genericWitness.isNil: return genericWitness
  if n.kind in {nnkIdent, nnkSym} and $n notin ["Int", "Nat", "Bool"]:
    var hasRuntimeType = false
    for mapping in mappings:
      if mapping.eponymName == $n and
          not isSyntheticGenericRuntimeType(mapping):
        hasRuntimeType = true
        break
    if not hasRuntimeType: return nil
  runtimeTypeValueExpr(n, globals, overrides)

proc runtimeValueConversionExpr(eponymType, nimType, value: NimNode,
                               toValue: bool,
                               mappings: seq[HostRuntimeType],
                               records: seq[HostRecord],
                               globals: NimNode,
                               allowDependentSigma = false,
                               indexOverrides: seq[tuple[name: string,
                                 value: NimNode]] = @[]): NimNode =
  var procParts = runtimeProcParts(eponymType)
  if procParts.resultType.isNil:
    procParts = runtimeEponymPiParts(eponymType)
  if not procParts.resultType.isNil:
    let rawValueCallback = hasRawValuePragma(nimType)
    if rawValueCallback:
      var argValueSyms: seq[NimNode] = @[]
      var argSyms: seq[NimNode] = @[]
      for i, _ in procParts.argTypes:
        argValueSyms.add(genSym(nskParam, "rawCallbackValue" & $i))
        argSyms.add(genSym(nskParam, "rawCallbackArgument" & $i))
      if toValue:
        var hostCall = newCall(value)
        for argSym in argValueSyms:
          hostCall.add(argSym)
        var callbackValue = hostCall
        for i in countdown(argValueSyms.high, 0):
          let hostCallback = newProc(params = @[bindSym"RuntimeValue",
            newIdentDefs(argValueSyms[i], bindSym"RuntimeValue", newEmptyNode())],
            body = newStmtList(callbackValue))
          callbackValue = newCall(bindSym"vHostFunc", hostCallback)
        return callbackValue
      var callbackArgs = newNimNode(nnkBracket)
      var formal: seq[NimNode] = @[bindSym"RuntimeValue"]
      for argSym in argSyms:
        callbackArgs.add(argSym)
        formal.add(newIdentDefs(argSym, bindSym"RuntimeValue", newEmptyNode()))
      let applied = newCall(bindSym"callRuntimeValue", value,
        newTree(nnkPrefix, ident"@", callbackArgs))
      return newProc(params = formal, body = newStmtList(applied))
    # A checked Eponym function may close over runtime state, so converting it
    # back to a Nim function pointer would discard that environment. Nim's
    # closure calling convention is required for this direction.
    if not toValue and not hasClosurePragma(nimType): return nil
    let resultNimType = runtimeNimType(procParts.resultType, mappings, records,
                                       allowDependentSigma)
    if resultNimType.isNil: return nil
    var argNimTypes: seq[NimNode] = @[]
    var argValueSyms: seq[NimNode] = @[]
    var argSyms: seq[NimNode] = @[]
    for i, argType in procParts.argTypes:
      let argNimType = runtimeNimType(argType, mappings, records,
                                      allowDependentSigma)
      if argNimType.isNil: return nil
      argNimTypes.add(argNimType)
      argValueSyms.add(genSym(nskParam, "runtimeCallbackValue" & $i))
      argSyms.add(genSym(nskParam, "runtimeCallbackArgument" & $i))
    if toValue:
      var decodedArgs: seq[NimNode] = @[]
      var callbackIndexOverrides = indexOverrides
      for i, argType in procParts.argTypes:
        let decodedArg = runtimeValueConversionExpr(argType, argNimTypes[i],
          argValueSyms[i], false, mappings, records, globals,
          allowDependentSigma, callbackIndexOverrides)
        if decodedArg.isNil: return nil
        decodedArgs.add(decodedArg)
        callbackIndexOverrides.add((procParts.argNames[i], decodedArg))
      var hostResult = newCall(value)
      for decodedArg in decodedArgs:
        hostResult.add(decodedArg)
      let encodedResult = runtimeValueConversionExpr(procParts.resultType,
        resultNimType, hostResult, true, mappings, records, globals,
        allowDependentSigma, callbackIndexOverrides)
      if encodedResult.isNil: return nil
      let callbackType = runtimeTypeValueExpr(eponymType, globals,
        indexOverrides)
      let callbackTypeSym = if callbackType.isNil: nil else:
        genSym(nskLet, "runtimeCallbackType")
      var callbackValue: NimNode = nil
      for i in countdown(argValueSyms.high, 0):
        var callbackBody = newStmtList()
        var needsArgumentGuard = false
        if procParts.argTypes[i].kind in
            {nnkCall, nnkObjConstr, nnkBracketExpr} and
            procParts.argTypes[i].len > 0 and
            procParts.argTypes[i][0].kind in {nnkIdent, nnkSym}:
          for mapping in mappings:
            if mapping.isRuntimeCodec and
                mapping.eponymName == $procParts.argTypes[i][0]:
              needsArgumentGuard = true
              break
        if needsArgumentGuard and not callbackTypeSym.isNil:
          var priorArguments = newNimNode(nnkBracket)
          for priorIndex in 0 ..< i:
            priorArguments.add(argValueSyms[priorIndex])
          let expectedArgumentType = newCall(
            bindSym"runtimePiDomainAfterArgs", callbackTypeSym,
            newTree(nnkPrefix, ident"@", priorArguments))
          callbackBody.add(newCall(bindSym"validateRuntimeValueAgainstType",
            argValueSyms[i], expectedArgumentType, globals))
        if i == argValueSyms.high:
          let encodedResultSym = genSym(nskLet, "runtimeCallbackResult")
          callbackBody.add(newLetStmt(encodedResultSym, encodedResult))
          var needsResultGuard = false
          if procParts.resultType.kind in
              {nnkCall, nnkObjConstr, nnkBracketExpr} and
              procParts.resultType.len > 0 and
              procParts.resultType[0].kind in {nnkIdent, nnkSym}:
            for mapping in mappings:
              if mapping.isRuntimeCodec and
                  mapping.eponymName == $procParts.resultType[0]:
                needsResultGuard = true
                break
          if needsResultGuard and not callbackTypeSym.isNil:
            var allArguments = newNimNode(nnkBracket)
            for argValueSym in argValueSyms:
              allArguments.add(argValueSym)
            let expectedResultType = newCall(
              bindSym"runtimePiResultAfterArgs", callbackTypeSym,
              newTree(nnkPrefix, ident"@", allArguments))
            callbackBody.add(newCall(bindSym"validateRuntimeValueAgainstType",
              encodedResultSym, expectedResultType, globals))
          callbackBody.add(encodedResultSym)
        else:
          callbackBody.add(callbackValue)
        let hostCallback = newProc(params = @[bindSym"RuntimeValue",
          newIdentDefs(argValueSyms[i], bindSym"RuntimeValue", newEmptyNode())],
          body = callbackBody)
        callbackValue = if i == 0 and not callbackType.isNil:
          newCall(bindSym"vHostFuncWithType", hostCallback, callbackTypeSym)
        else:
          newCall(bindSym"vHostFunc", hostCallback)
      if not callbackTypeSym.isNil:
        return newTree(nnkBlockExpr, newEmptyNode(), newStmtList(
          newLetStmt(callbackTypeSym, callbackType), callbackValue))
      return callbackValue
    var encodedArgs = newNimNode(nnkBracket)
    var formal: seq[NimNode] = @[resultNimType]
    var callbackIndexOverrides = indexOverrides
    for i, argType in procParts.argTypes:
      let encodedArg = runtimeValueConversionExpr(argType, argNimTypes[i],
        argSyms[i], true, mappings, records, globals, allowDependentSigma,
        callbackIndexOverrides)
      if encodedArg.isNil: return nil
      encodedArgs.add(encodedArg)
      formal.add(newIdentDefs(argSyms[i], argNimTypes[i], newEmptyNode()))
      callbackIndexOverrides.add((procParts.argNames[i], argSyms[i]))
    let applied = newCall(bindSym"callRuntimeValue", value,
      newTree(nnkPrefix, ident"@", encodedArgs))
    let decodedResult = runtimeValueConversionExpr(procParts.resultType,
      resultNimType, applied, false, mappings, records, globals,
      allowDependentSigma, callbackIndexOverrides)
    if decodedResult.isNil: return nil
    return newProc(params = formal, body = newStmtList(decodedResult))
  let typeHead = runtimeTypeHead(eponymType)
  if typeHead.kind == nnkIdent:
    for mapping in mappings:
      if mapping.isRuntimeCodec and mapping.eponymName == $typeHead:
        let codec = copyNimTree(if toValue: mapping.encoder else: mapping.decoder)
        return newCall(codec, value, globals)
      if mapping.isRuntimeVariant and mapping.eponymName == $typeHead:
        let familyName = newLit(mapping.eponymName)
        let constructors = newCall(bindSym"runtimeVariantConstructorNames",
          globals, familyName)
        if toValue:
          return newCall(bindSym"runtimeVariantToValue", value, globals,
            familyName, constructors)
        return newCall(bindSym"valueToRuntimeVariant", value, globals,
          familyName, constructors)
    if toValue and eponymType.kind in {nnkIdent, nnkSym}:
      for mapping in mappings:
        if mapping.eponymName == $typeHead and
            not isSyntheticGenericRuntimeType(mapping) and
            not mapping.isRuntimeCodec and not mapping.isRuntimeVariant and
            not mapping.isRuntimeVector and not mapping.isRuntimeList and
            not mapping.isRuntimeOption and
            findHostRecord(records, mapping.eponymName) < 0:
          return newCall(bindSym"toHostValueWithType", value,
            runtimeTypeValueExpr(eponymType, globals, indexOverrides))
  if eponymType.kind in {nnkIdent, nnkSym}:
    var isGenericTypeParameter = false
    for mapping in mappings:
      if mapping.eponymName == $eponymType and
          isSyntheticGenericRuntimeType(mapping):
        isGenericTypeParameter = true
        break
    if isGenericTypeParameter:
      var fallback: NimNode
      if toValue:
        let representedType = runtimeRepresentedTypeValueExpr(eponymType,
          globals, mappings, indexOverrides)
        if representedType.isNil:
          fallback = newCall(newTree(nnkBracketExpr,
            bindSym"toHostValue", copyNimTree(nimType)), value)
        else:
          fallback = newCall(bindSym"toHostValueWithType", value,
            representedType)
      else:
        fallback = newCall(newTree(nnkBracketExpr,
          bindSym"valueToHost", copyNimTree(nimType)), value)
      let genericCodec = runtimeGenericCodecConversionExpr(eponymType,
        nimType, value, toValue, globals, mappings, fallback)
      if not genericCodec.isNil: return genericCodec
  for mapping in mappings:
    if mapping.isRuntimeVector:
      let vector = runtimeVectorComponents(eponymType, mapping.eponymName)
      if not vector.elementType.isNil:
        # Lower the original supported Nat grammar while substituting named
        # Sigma/record indices as Nim operands. This keeps Eponym `add`/`mul`
        # mapped to checked integer helpers even when an operand is a host
        # field or tuple projection.
        let expectedLength = runtimeNatIndexExpr(vector.length, indexOverrides)
        let elementNimType = runtimeNimType(vector.elementType, mappings,
          records, allowDependentSigma)
        if expectedLength.isNil or elementNimType.isNil: return nil
        let itemSym = genSym(nskParam, "runtimeVectorItem")
        let codecGlobalsSym = genSym(nskParam, "runtimeVectorGlobals")
        if toValue:
          let encodedItem = runtimeValueConversionExpr(vector.elementType,
            elementNimType, itemSym, true, mappings, records,
            codecGlobalsSym, allowDependentSigma, indexOverrides)
          if encodedItem.isNil: return nil
          let encoder = newProc(params = @[bindSym"RuntimeValue",
            newIdentDefs(itemSym, elementNimType, newEmptyNode()),
            newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
            body = newStmtList(encodedItem))
          let elementTypeValue = runtimeRepresentedTypeValueExpr(
            vector.elementType, globals, mappings, indexOverrides)
          if not elementTypeValue.isNil:
            return newCall(bindSym"seqToVecValue", value, expectedLength,
              globals, newLit(mapping.eponymName), encoder, elementTypeValue)
          return newCall(bindSym"seqToVecValue", value, expectedLength,
            globals, newLit(mapping.eponymName), encoder)
        let decodedItem = runtimeValueConversionExpr(vector.elementType,
          elementNimType, itemSym, false, mappings, records,
          codecGlobalsSym, allowDependentSigma, indexOverrides)
        if decodedItem.isNil: return nil
        let decoder = newProc(params = @[elementNimType,
          newIdentDefs(itemSym, bindSym"RuntimeValue", newEmptyNode()),
          newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
          body = newStmtList(decodedItem))
        return newCall(bindSym"vecValueToSeq", value, expectedLength,
          globals, newLit(mapping.eponymName), decoder)
    elif mapping.isRuntimeList:
      let elementType = runtimeListElementType(eponymType, mapping.eponymName)
      if not elementType.isNil:
        let elementNimType = runtimeNimType(elementType, mappings, records,
          allowDependentSigma)
        if elementNimType.isNil: return nil
        let itemSym = genSym(nskParam, "runtimeListItem")
        let codecGlobalsSym = genSym(nskParam, "runtimeListGlobals")
        if toValue:
          let encodedItem = runtimeValueConversionExpr(elementType,
            elementNimType, itemSym, true, mappings, records,
            codecGlobalsSym, allowDependentSigma, indexOverrides)
          if encodedItem.isNil: return nil
          let encoder = newProc(params = @[bindSym"RuntimeValue",
            newIdentDefs(itemSym, elementNimType, newEmptyNode()),
            newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
            body = newStmtList(encodedItem))
          let elementTypeValue = runtimeRepresentedTypeValueExpr(
            elementType, globals, mappings, indexOverrides)
          if not elementTypeValue.isNil:
            return newCall(bindSym"seqToListValue", value, globals,
              newLit(mapping.eponymName), encoder, elementTypeValue)
          return newCall(bindSym"seqToListValue", value, globals,
            newLit(mapping.eponymName), encoder)
        let decodedItem = runtimeValueConversionExpr(elementType,
          elementNimType, itemSym, false, mappings, records,
          codecGlobalsSym, allowDependentSigma, indexOverrides)
        if decodedItem.isNil: return nil
        let decoder = newProc(params = @[elementNimType,
          newIdentDefs(itemSym, bindSym"RuntimeValue", newEmptyNode()),
          newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
          body = newStmtList(decodedItem))
        return newCall(bindSym"listValueToSeq", value, globals,
          newLit(mapping.eponymName), decoder)
    elif mapping.isRuntimeOption:
      let elementType = runtimeOptionElementType(eponymType,
        mapping.eponymName)
      if not elementType.isNil:
        let elementNimType = runtimeNimType(elementType, mappings, records,
          allowDependentSigma)
        if elementNimType.isNil: return nil
        let itemSym = genSym(nskParam, "runtimeOptionItem")
        let codecGlobalsSym = genSym(nskParam, "runtimeOptionGlobals")
        if toValue:
          let encodedItem = runtimeValueConversionExpr(elementType,
            elementNimType, itemSym, true, mappings, records,
            codecGlobalsSym, allowDependentSigma, indexOverrides)
          if encodedItem.isNil: return nil
          let encoder = newProc(params = @[bindSym"RuntimeValue",
            newIdentDefs(itemSym, elementNimType, newEmptyNode()),
            newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
            body = newStmtList(encodedItem))
          let elementTypeValue = runtimeRepresentedTypeValueExpr(
            elementType, globals, mappings, indexOverrides)
          if not elementTypeValue.isNil:
            return newCall(bindSym"optionToValue", value, globals,
              newLit(mapping.eponymName), encoder, elementTypeValue)
          return newCall(bindSym"optionToValue", value, globals,
            newLit(mapping.eponymName), encoder)
        let decodedItem = runtimeValueConversionExpr(elementType,
          elementNimType, itemSym, false, mappings, records,
          codecGlobalsSym, allowDependentSigma, indexOverrides)
        if decodedItem.isNil: return nil
        let decoder = newProc(params = @[elementNimType,
          newIdentDefs(itemSym, bindSym"RuntimeValue", newEmptyNode()),
          newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
          body = newStmtList(decodedItem))
        return newCall(bindSym"valueToOption", value, globals,
          newLit(mapping.eponymName), decoder)
  let sigma = runtimeSigmaComponentsForCodec(eponymType, mappings,
    allowDependentSigma)
  if not sigma.first.isNil:
    if nimType.kind notin {nnkTupleConstr, nnkTupleTy} or nimType.len != 2:
      return nil
    if toValue:
      let firstValue = newTree(nnkBracketExpr, value, newLit(0))
      let first = runtimeValueConversionExpr(sigma.first, nimType[0],
        firstValue, true, mappings, records,
        globals, allowDependentSigma, indexOverrides)
      var secondOverrides = indexOverrides
      if sigma.binder.len > 0:
        secondOverrides.add((sigma.binder, firstValue))
      let second = runtimeValueConversionExpr(sigma.second, nimType[1],
        newTree(nnkBracketExpr, value, newLit(1)), true, mappings, records,
        globals, allowDependentSigma, secondOverrides)
      if first.isNil or second.isNil: return nil
      return newCall(bindSym"pairValue", first, second)
    let firstValue = newCall(bindSym"runtimePairFirst", value)
    let secondValue = newCall(bindSym"runtimePairSecond", value)
    let first = runtimeValueConversionExpr(sigma.first, nimType[0],
      firstValue, false, mappings, records, globals, allowDependentSigma,
      indexOverrides)
    var secondOverrides = indexOverrides
    if sigma.binder.len > 0:
      secondOverrides.add((sigma.binder, first))
    let second = runtimeValueConversionExpr(sigma.second, nimType[1],
      secondValue, false, mappings, records, globals, allowDependentSigma,
      secondOverrides)
    if first.isNil or second.isNil: return nil
    return newTree(nnkTupleConstr, first, second)
  if eponymType.kind == nnkIdent:
    var isDeclaredType = $eponymType in ["Int", "Nat", "Bool"] or
      findHostRecord(records, $eponymType) >= 0
    for mapping in mappings:
      if mapping.eponymName == $eponymType and
          not isSyntheticGenericRuntimeType(mapping): isDeclaredType = true
    if toValue and not isDeclaredType:
      let representedType = runtimeRepresentedTypeValueExpr(eponymType,
        globals, mappings, indexOverrides)
      if not representedType.isNil:
        return newCall(bindSym"toHostValueWithType", value, representedType)
    let recordIndex = findHostRecord(records, $eponymType)
    if recordIndex >= 0:
      let record = records[recordIndex]
      if record.isVariant:
        if record.hasDependentField or record.constructors.len == 0:
          return nil
        var constructorNames = newNimNode(nnkBracket)
        for constructor in record.constructors:
          constructorNames.add(newLit(constructor))
        let namesSeq = newTree(nnkPrefix, ident"@", constructorNames)
        if toValue:
          return newCall(bindSym"enumToValue", value, globals, namesSeq)
        return newCall(newTree(nnkBracketExpr, bindSym"valueToEnum", nimType),
                       value, globals, namesSeq)
      let dependenciesCodecChecked =
        runtimeRecordDependenciesCodecSupported(record, mappings)
      if (record.hasDependentField and not record.trustDependentFields and
          not dependenciesCodecChecked) or record.fields.len == 0:
        return nil
      let recordAllowsDependentFields = allowDependentSigma or
        record.trustDependentFields
      if toValue:
        var convertedFields: seq[NimNode] = @[]
        var indexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
        for field in record.fields:
          let fieldType = runtimeNimType(field.eponymType, mappings, records,
                                         recordAllowsDependentFields)
          if fieldType.isNil: return nil
          let fieldValue = newTree(nnkDotExpr, value, ident(field.name))
          let converted = runtimeValueConversionExpr(field.eponymType,
            fieldType, fieldValue, true, mappings, records, globals,
            recordAllowsDependentFields, indexOverrides)
          if converted.isNil: return nil
          convertedFields.add(converted)
          indexOverrides.add((field.name, fieldValue))
        var tail = newCall(bindSym"unitValue")
        for i in countdown(convertedFields.high, 0):
          tail = newCall(bindSym"pairValue", convertedFields[i], tail)
        return tail
      var current = value
      var fields = newNimNode(nnkObjConstr)
      fields.add(nimType)
      var decodeBody = newStmtList()
      var indexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
      for field in record.fields:
        let fieldType = runtimeNimType(field.eponymType, mappings, records,
                                       recordAllowsDependentFields)
        if fieldType.isNil: return nil
        let fieldSym = genSym(nskLet, field.name)
        let converted = runtimeValueConversionExpr(field.eponymType,
          fieldType, newCall(bindSym"runtimePairFirst", current), false,
          mappings, records, globals, recordAllowsDependentFields,
          indexOverrides)
        if converted.isNil: return nil
        decodeBody.add(newLetStmt(fieldSym, converted))
        fields.add(newTree(nnkExprColonExpr, ident(field.name), fieldSym))
        indexOverrides.add((field.name, fieldSym))
        current = newCall(bindSym"runtimePairSecond", current)
      decodeBody.add(fields)
      return newBlockStmt(decodeBody)
  let valueFn = runtimeValueConverter(eponymType, nimType, toValue, records)
  if valueFn.isNil: return nil
  if simpleRuntimeCodec(eponymType) == "bool" or
      (simpleRuntimeCodec(eponymType) == "nat" and not toValue):
    return newCall(valueFn, value, globals)
  if simpleRuntimeCodec(eponymType) == "nat" and toValue:
    return newCall(bindSym"natToValue", value, globals)
  if simpleRuntimeCodec(eponymType) == "nat" and not toValue:
    return newCall(bindSym"valueToNat", value, globals)
  newCall(valueFn, value)

proc genericRuntimeInfo(decl: NimNode,
                        mappings: seq[HostRuntimeType],
                        records: seq[HostRecord],
                        allowGenericValues = false,
                        allowUnmappedValues = false,
                        allowDependentSigma = false,
                        allowGenericFunctionValues = false): tuple[
    genericParams: NimNode, typeNames: seq[string],
    genericNames: seq[NimNode], genericNatArgs: seq[bool],
    genericBoolArgs: seq[bool], genericIntArgs: seq[bool],
    genericValueArgs: seq[bool], genericValueTypes: seq[NimNode],
    genericValueTypeNames: seq[string],
    genericValueTypeExprs: seq[NimNode],
    genericMappedTypes: seq[NimNode], genericMappedNimTypes: seq[NimNode],
    codecMappings: seq[HostRuntimeType], error: string] =
  result.genericParams = newEmptyNode()
  result.codecMappings = mappings
  if decl[2].kind == nnkEmpty:
    return
  result.genericParams = newNimNode(nnkGenericParams)
  for param in decl[2]:
    if param.kind != nnkIdentDefs or param[^2].kind == nnkEmpty:
      result.error = "runtime wrappers require explicitly typed generic binders"
      return
    let binderType = nimTypeToEponym(param[^2])
    let binderTypeHead = runtimeTypeHead(param[^2])
    let binderTypeHeadName = if binderTypeHead.kind == nnkIdent:
      $binderTypeHead else: ""
    let hostRecordIndex = findHostRecord(records, binderTypeHeadName)
    let hasRecordValueCodec = hostRecordIndex >= 0 and
      not records[hostRecordIndex].isVariant and
      not runtimeNimType(param[^2], mappings, records,
        allowDependentSigma).isNil
    var mappedBinder: HostRuntimeType
    var hasMappedBinder = false
    var hasStructuralValueCodec =
      not runtimeSigmaComponentsForCodec(param[^2], mappings,
        allowDependentSigma).first.isNil
    if hasRecordValueCodec:
      hasStructuralValueCodec = true
    if allowGenericFunctionValues and
        containsEponymPiType(param[^2]):
      hasStructuralValueCodec = true
    for mapping in mappings:
      if mapping.eponymName == binderType:
        if hasRecordValueCodec:
          hasStructuralValueCodec = true
        else:
          mappedBinder = mapping
          hasMappedBinder = true
          break
      if mapping.eponymName == binderTypeHeadName:
        if mapping.isRuntimeVector:
          hasStructuralValueCodec = true
        elif mapping.isRuntimeList and
            not runtimeListElementType(param[^2], mapping.eponymName).isNil:
          hasStructuralValueCodec = true
        elif mapping.isRuntimeOption and
            not runtimeOptionElementType(param[^2], mapping.eponymName).isNil:
          hasStructuralValueCodec = true
        elif hasRecordValueCodec:
          hasStructuralValueCodec = true
        else:
          mappedBinder = mapping
          hasMappedBinder = true
          break
    if binderType notin ["Type 0", "Nat", "Bool", "Int"] and
        not hasMappedBinder and
        not (allowGenericValues and hasStructuralValueCodec) and
        not allowUnmappedValues:
      result.error = "runtime wrappers currently support only type-level " &
        "binders annotated with Univ, primitive value indices, or values " &
        "with an explicit runtimeType mapping"
      return
    for i in 0 ..< param.len - 2:
      let name = $param[i]
      if name in result.genericNames.mapIt($it):
        result.error = "duplicate generic runtime parameter '" & name & "'"
        return
      if binderType == "Type 0" and decl.len > 6 and not decl[6].isNil and
          mentionsName(decl[6], name):
        result.error = "generic type parameter '" & name &
          "' is used by the runtime body; an explicit runtime type " &
          "representation is required"
        return
      let genericName = copyNimTree(param[i])
      result.genericNames.add(genericName)
      result.genericMappedTypes.add(nil)
      result.genericMappedNimTypes.add(nil)
      result.genericValueArgs.add(false)
      result.genericValueTypes.add(nil)
      result.genericValueTypeNames.add("")
      result.genericValueTypeExprs.add(copyNimTree(param[^2]))
      if binderType == "Type 0":
        result.typeNames.add(name)
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]),
          newEmptyNode(), newEmptyNode()))
        result.genericNatArgs.add(false)
        result.genericBoolArgs.add(false)
        result.genericIntArgs.add(false)
        result.codecMappings.add(HostRuntimeType(eponymName: name,
          nimType: copyNimTree(param[i])))
      elif binderType == "Nat":
        let staticInt = newTree(nnkBracketExpr, ident"static", ident"int")
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]), staticInt,
          newEmptyNode()))
        result.genericNatArgs.add(true)
        result.genericBoolArgs.add(false)
        result.genericIntArgs.add(false)
      elif binderType == "Bool":
        let staticBool = newTree(nnkBracketExpr, ident"static", ident"bool")
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]), staticBool,
          newEmptyNode()))
        result.genericNatArgs.add(false)
        result.genericBoolArgs.add(true)
        result.genericIntArgs.add(false)
      else:
        if allowGenericValues and hasStructuralValueCodec:
          result.genericParams.add(newIdentDefs(copyNimTree(param[i]),
            bindSym"RuntimeValue", newEmptyNode()))
          result.genericNatArgs.add(false)
          result.genericBoolArgs.add(false)
          result.genericIntArgs.add(false)
          result.genericValueArgs[^1] = true
          result.genericValueTypes[^1] = copyNimTree(param[^2])
          continue
        if hasMappedBinder:
          let staticMapped = newTree(nnkBracketExpr, ident"static",
                                     copyNimTree(mappedBinder.nimType))
          result.genericParams.add(newIdentDefs(copyNimTree(param[i]),
            staticMapped, newEmptyNode()))
          result.genericNatArgs.add(false)
          result.genericBoolArgs.add(false)
          result.genericIntArgs.add(false)
          result.genericMappedTypes[^1] = copyNimTree(param[^2])
          result.genericMappedNimTypes[^1] = copyNimTree(mappedBinder.nimType)
          continue
        if binderType == "Int":
          let staticInt = newTree(nnkBracketExpr, ident"static", ident"int")
          result.genericParams.add(newIdentDefs(copyNimTree(param[i]), staticInt,
            newEmptyNode()))
          result.genericNatArgs.add(false)
          result.genericBoolArgs.add(false)
          result.genericIntArgs.add(true)
          continue
        if allowUnmappedValues:
          result.genericParams.add(newIdentDefs(copyNimTree(param[i]),
            bindSym"RuntimeValue", newEmptyNode()))
          result.genericNatArgs.add(false)
          result.genericBoolArgs.add(false)
          result.genericIntArgs.add(false)
          result.genericValueArgs[^1] = true
          if param[^2].kind == nnkIdent:
            result.genericValueTypeNames[^1] = binderType
          continue
        let staticInt = newTree(nnkBracketExpr, ident"static", ident"int")
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]), staticInt,
          newEmptyNode()))
        result.genericNatArgs.add(false)
        result.genericBoolArgs.add(false)
        result.genericIntArgs.add(true)

proc callbackCanDeferGenericInference(params: NimNode, paramIndex: int,
    typeNames: seq[string]): bool =
  ## Nim does not revisit an earlier callback argument after it infers a
  ## generic type from a later value argument. Leave that callback untyped in
  ## the generated wrapper; invoking it in the wrapper body still checks its
  ## concrete argument and result types.
  if paramIndex <= 0 or paramIndex >= params.len or
      params[paramIndex].kind != nnkIdentDefs:
    return false
  let callbackType = params[paramIndex][^2]
  if runtimeProcParts(callbackType).resultType.isNil:
    return false
  for genericName in typeNames:
    if not mentionsName(callbackType, genericName):
      continue
    for otherIndex in 1 ..< params.len:
      if otherIndex == paramIndex or params[otherIndex].kind != nnkIdentDefs:
        continue
      let otherType = params[otherIndex][^2]
      if runtimeProcParts(otherType).resultType.isNil and
          mentionsName(otherType, genericName):
        return true

proc genericRuntimeValueArgs(generic: tuple[genericParams: NimNode,
    typeNames: seq[string], genericNames: seq[NimNode],
    genericNatArgs: seq[bool], genericBoolArgs: seq[bool],
    genericIntArgs: seq[bool], genericValueArgs: seq[bool],
    genericValueTypes: seq[NimNode], genericValueTypeNames: seq[string],
    genericValueTypeExprs: seq[NimNode],
    genericMappedTypes: seq[NimNode], genericMappedNimTypes: seq[NimNode],
    codecMappings: seq[HostRuntimeType],
    error: string], globals: NimNode, mappings: seq[HostRuntimeType],
    records: seq[HostRecord]): seq[NimNode] =
  for i, genericName in generic.genericNames:
    if generic.genericNatArgs[i]:
      result.add(newCall(bindSym"natToValue", copyNimTree(genericName),
                         globals))
    elif generic.genericBoolArgs[i]:
      result.add(newCall(bindSym"boolToValue", copyNimTree(genericName),
                         globals))
    elif generic.genericIntArgs[i]:
      result.add(newCall(bindSym"intToValue", copyNimTree(genericName)))
    elif not generic.genericMappedTypes[i].isNil:
      let encoded = runtimeValueConversionExpr(
        generic.genericMappedTypes[i], generic.genericMappedNimTypes[i],
        copyNimTree(genericName), true, mappings, records, globals)
      if encoded.isNil:
        error("generic runtime value needs a codec for Eponym type '" &
          repr(generic.genericMappedTypes[i]) & "'")
      result.add(encoded)
    else:
      let typeWitness = runtimeGenericTypeWitnessExpr(genericName, globals,
        mappings)
      if typeWitness.isNil:
        result.add(newCall(bindSym"vType", newLit(0)))
      else:
        result.add(newCall(bindSym"runtimeTypeWitnessOrUniverse", typeWitness))

proc bindingCall(binding: HostPostulateBinding, bindingsSym, globalsSym: NimNode,
                 mappings: seq[HostRuntimeType], records: seq[HostRecord],
                 checkedGlobals: Globals): NimNode =
  let nameLit = newLit(binding.postulateName)
  if binding.rawValue:
    return newCall(bindSym"bindHostValueNary", bindingsSym, globalsSym,
                   nameLit, binding.implementation)
  if binding.pairResult:
    let bindingForm = if binding.trustedPairIndex:
      "bindPostulatePairTrusted"
    else:
      "bindPostulatePair"
    let pairType = if not binding.pairResultType.isNil:
      copyNimTree(binding.pairResultType)
    else:
      newCall(ident"Sig",
        ident(binding.eponymTypes[binding.pairArgCount]),
        ident(binding.eponymTypes[binding.pairArgCount + 1]))
    let pairNimType = runtimeNimType(pairType, mappings, records,
                                    binding.trustedPairIndex)
    if pairNimType.isNil:
      error(bindingForm & " needs runtime codecs for both pair fields")
    var runtimeArgs: seq[NimNode] = @[]
    var decodedArgs: seq[NimNode] = @[]
    var adapterBody = newStmtList()
    var pairIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
    for i in 0 ..< binding.pairArgCount:
      let eponymArgType = ident(binding.eponymTypes[i])
      let nimArgType = runtimeNimType(eponymArgType, mappings, records)
      if nimArgType.isNil:
        error(bindingForm & " needs a runtime codec for argument '" &
          binding.eponymTypes[i] & "'")
      let runtimeArg = genSym(nskParam, "runtimeArgument")
      runtimeArgs.add(runtimeArg)
      let decoded = runtimeValueConversionExpr(eponymArgType, nimArgType,
        runtimeArg, false, mappings, records, globalsSym)
      if decoded.isNil:
        error(bindingForm & " could not build an argument codec")
      let decodedArg = genSym(nskLet, "hostPairArgument")
      adapterBody.add(newLetStmt(decodedArg, decoded))
      decodedArgs.add(decodedArg)
      if i < binding.pairResultArgNames.len and
          binding.pairResultArgNames[i].len > 0:
        pairIndexOverrides.add((binding.pairResultArgNames[i], decodedArg))
    let hostResult = genSym(nskLet, "hostPairResult")
    let encodedResult = runtimeValueConversionExpr(pairType, pairNimType,
      hostResult, true, mappings, records, globalsSym,
      binding.trustedPairIndex, pairIndexOverrides)
    if encodedResult.isNil:
      error(bindingForm & " could not build a value codec")
    var implementationCall = newCall(binding.implementation)
    for decodedArg in decodedArgs:
      implementationCall.add(decodedArg)
    adapterBody.add(newLetStmt(hostResult, implementationCall))
    adapterBody.add(encodedResult)
    var adapterValue = newCall(bindSym"vHostFunc",
      newProc(params = @[bindSym"RuntimeValue",
        newIdentDefs(runtimeArgs[^1], bindSym"RuntimeValue", newEmptyNode())],
        body = adapterBody))
    if binding.pairArgCount > 1:
      for i in countdown(binding.pairArgCount - 2, 0):
        let partialBody = newStmtList(adapterValue)
        let partialProc = newProc(params = @[bindSym"RuntimeValue",
          newIdentDefs(runtimeArgs[i], bindSym"RuntimeValue", newEmptyNode())],
          body = partialBody)
        adapterValue = newCall(bindSym"vHostFunc", partialProc)
    return newCall(bindSym"bindHostValue", bindingsSym, globalsSym,
                   nameLit, adapterValue)
  var adapterTypes = binding.eponymTypes
  var usesCustomCodec = false
  for typeName in binding.eponymTypes:
    for mapping in mappings:
      if mapping.eponymName == typeName and mapping.isRuntimeCodec:
        usesCustomCodec = true
  if binding.eponymTypes.len == 1 and usesCustomCodec:
    adapterTypes = @[binding.eponymTypes[0], binding.eponymTypes[0]]
  if binding.eponymTypes.len >= 7 or usesCustomCodec or binding.mutableArgs:
    let argumentCount = adapterTypes.len - 1
    var decodedArgs: seq[NimNode] = @[]
    var decodedArgDecls = newStmtList()
    for i in 0 ..< argumentCount:
      let eponymType = ident(adapterTypes[i])
      let nimType = runtimeNimType(eponymType, mappings, records)
      if nimType.isNil:
        error("bindPostulate for '" & binding.postulateName &
          "' needs a runtime codec for argument type '" &
          adapterTypes[i] & "'")
      let decoded = runtimeValueConversionExpr(eponymType, nimType,
        newTree(nnkBracketExpr, ident"runtimeArguments", newLit(i)), false,
        mappings, records, ident"runtimeGlobals")
      if decoded.isNil:
        error("bindPostulate could not build a runtime codec for argument '" &
          adapterTypes[i] & "'")
      if binding.mutableArgs:
        let decodedArg = genSym(nskVar, "hostArgument")
        decodedArgs.add(decodedArg)
        decodedArgDecls.add(newVarStmt(decodedArg, decoded))
      else:
        decodedArgs.add(decoded)
    let resultEponymType = ident(adapterTypes[^1])
    let resultNimType = runtimeNimType(resultEponymType, mappings, records)
    if resultNimType.isNil:
      error("bindPostulate for '" & binding.postulateName &
        "' needs a runtime codec for result type '" &
        adapterTypes[^1] & "'")
    var implementationCall = newCall(binding.implementation)
    for decodedArg in decodedArgs:
      implementationCall.add(decodedArg)
    let encodedResult = runtimeValueConversionExpr(resultEponymType,
      resultNimType, implementationCall, true, mappings, records,
      ident"runtimeGlobals")
    if encodedResult.isNil:
      error("bindPostulate could not build a runtime codec for result '" &
        adapterTypes[^1] & "'")
    let runtimeArgsSym = ident"runtimeArguments"
    let runtimeGlobalsSym = ident"runtimeGlobals"
    var adapterBody = decodedArgDecls
    adapterBody.add(encodedResult)
    let adapter = newProc(params = @[bindSym"RuntimeValue",
      newIdentDefs(runtimeArgsSym,
        newTree(nnkBracketExpr, ident"seq", bindSym"RuntimeValue"), newEmptyNode()),
      newIdentDefs(runtimeGlobalsSym, bindSym"Globals", newEmptyNode())],
      body = adapterBody)
    return newCall(bindSym"bindHostValueNary", bindingsSym, globalsSym,
      nameLit, adapter)
  if binding.eponymTypes.len == 0:
    return newCall(bindSym"bindHostIntUnary", bindingsSym, globalsSym,
                   nameLit, binding.implementation)
  var typeIndexes: seq[int] = @[]
  let isNatType = proc(typeIndex: int): bool =
    if typeIndex < 0 or typeIndex >= binding.eponymTypes.len: return false
    let typeName = binding.eponymTypes[typeIndex]
    isCheckedNatType(checkedGlobals, typeName)
  if binding.eponymTypes.len == 2 and isNatType(1):
    typeIndexes = @[0]
  elif binding.eponymTypes.len == 2:
    typeIndexes = @[0, 1]
  elif binding.eponymTypes.len == 3 and isNatType(0):
    typeIndexes = @[1, 2]
  else:
    for i in 0 ..< binding.eponymTypes.len:
      typeIndexes.add(i)
  var typeArgs: seq[NimNode] = @[]
  for typeIndex in typeIndexes:
    let eponymName = binding.eponymTypes[typeIndex]
    var nimType: NimNode = nil
    for mapping in mappings:
      if mapping.eponymName == eponymName:
        nimType = mapping.nimType
        break
    if nimType.isNil:
      error("bindPostulate for '" & binding.postulateName &
        "' needs runtimeType(" & eponymName & ", NimType)")
    typeArgs.add(nimType)
  let natOpaqueHomogeneous = binding.eponymTypes.len == 3 and
    isNatType(0) and typeArgs[0].repr == typeArgs[1].repr
  let adapter =
    if binding.eponymTypes.len == 1: bindSym"bindHostOpaqueUnary"
    elif binding.eponymTypes.len == 2 and isNatType(1):
      bindSym"bindHostOpaqueNatUnary"
    elif binding.eponymTypes.len == 2: bindSym"bindHostOpaqueMapUnary"
    elif binding.eponymTypes.len == 3 and isNatType(0):
      if natOpaqueHomogeneous: bindSym"bindHostNatOpaqueBinary"
      else: bindSym"bindHostNatOpaqueMapBinary"
    elif binding.eponymTypes.len == 3: bindSym"bindHostOpaqueBinary"
    elif binding.eponymTypes.len == 4: bindSym"bindHostOpaqueTernary"
    elif binding.eponymTypes.len == 5: bindSym"bindHostOpaqueQuaternary"
    elif binding.eponymTypes.len == 6: bindSym"bindHostOpaqueQuinary"
    else:
      error("unsupported bindPostulate codec combination for '" &
            binding.postulateName & "'")
  var genericAdapter = newNimNode(nnkBracketExpr)
  genericAdapter.add(adapter)
  let genericTypeArgs = if natOpaqueHomogeneous: typeArgs[0 .. 0] else: typeArgs
  for typeArg in genericTypeArgs:
    genericAdapter.add(typeArg)
  var call = newCall(genericAdapter, bindingsSym, globalsSym, nameLit)
  if binding.eponymTypes.len == 2 and isNatType(1):
    call.add(newLit(binding.eponymTypes[0]))
  elif binding.eponymTypes.len == 3 and isNatType(0):
    call.add(newLit(binding.eponymTypes[1]))
    call.add(newLit(binding.eponymTypes[2]))
  else:
    for eponymName in binding.eponymTypes:
      call.add(newLit(eponymName))
  call.add(binding.implementation)
  call

proc unsupportedRuntimeWrapper(decl: NimNode, defName: string,
                               mappings: seq[HostRuntimeType],
                               records: seq[HostRecord],
                               allowDependentSigma = false): NimNode =
  let params = decl[3]
  var reason = "unsupported generic or higher-order signature"
  if decl[2].kind != nnkEmpty:
    reason = "generic Eponym procedures do not yet have runtime wrappers"
  elif params.len == 0 or params[0].kind == nnkEmpty:
    reason = "Eponym procedure has no explicit runtime result type"
  elif not runtimeProcParts(params[0]).resultType.isNil and
      not hasClosurePragma(params[0]):
    reason = "Nim function results require {.closure.} because checked " &
      "Eponym functions may capture runtime state"
  elif runtimeNimType(params[0], mappings, records,
                      allowDependentSigma).isNil:
    reason = "no runtime codec for Eponym result type '" & repr(params[0]) & "'"
  else:
    for i in 1 ..< params.len:
      let p = params[i]
      if p.kind != nnkIdentDefs:
        reason = "unsupported Nim parameter declaration for Eponym procedure '" &
          defName & "'"
        break
      if runtimeNimType(p[^2], mappings, records,
                        allowDependentSigma).isNil:
        reason = "no runtime codec for Eponym parameter type '" & repr(p[^2]) & "'"
        break
  let name = ident(defName)
  let message = newLit("eponymBlock wrapper '" & defName & "': " & reason &
    "; add runtimeType for an opaque postulated type or use a supported primitive")
  result = quote do:
    template `name`*(args: varargs[untyped]): untyped =
      {.error: `message`.}

proc unreconstructableRuntimeWrapper(defName: string): NimNode =
  let name = ident(defName)
  let message = newLit("eponymBlock wrapper '" & defName &
    "': cannot reconstruct a supported Nim signature from the checked " &
    "Eponym type; add an explicit Nim proc signature or use runtimeValue(" &
    defName & ")")
  result = quote do:
    template `name`*(args: varargs[untyped]): untyped =
      {.error: `message`.}

proc runtimePiValueSlots(globals: Globals, defName: string,
                         wrapperNames: seq[string]):
                         tuple[slots: seq[bool], aligned: bool] =
  ## Whether each checked Pi binder needs a runtime argument. Also verify
  ## that wrapper values correspond to binders in the same order; otherwise
  ## generated code must keep the interpreter path.
  result.aligned = defName in globals
  if not result.aligned: return
  var ty = globals[defName].ty
  var i = 0
  while not ty.isNil and ty.kind == tPi:
    if i >= wrapperNames.len or
        cmpIgnoreStyle(ty.scope.adv, wrapperNames[i]) != 0:
      result.aligned = false
    result.slots.add(ty.qty != q0)
    ty = ty.scope.bdy
    inc i
  if i != wrapperNames.len:
    result.aligned = false

proc nimTypeMatchesRepr(n: NimNode, want: string): bool =
  ## Does the surface Nim type AST denote the repr-tier type name
  ## (`int`, `seq[int]`, or `Option[int]`)? Structural match: the wrapper
  ## identity-boundary check (issue #330 v3) compares the declared
  ## formals/result against the repr signature threaded through
  ## `compileBlockProcs`, so a `seq[int]` wrapper never calls an `int`
  ## repr proc.
  case want
  of "int":
    n.kind in {nnkIdent, nnkSym} and $n == "int"
  of "seq[int]":
    n.kind == nnkBracketExpr and n.len == 2 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "seq" and
      n[1].kind in {nnkIdent, nnkSym} and $n[1] == "int"
  of "Option[int]":
    n.kind == nnkBracketExpr and n.len == 2 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "Option" and
      n[1].kind in {nnkIdent, nnkSym} and $n[1] == "int"
  else: false

proc typedRuntimeWrapper(decl: NimNode, baseDir, src, defName: string,
                         bindings: seq[HostPostulateBinding],
                         mappings: seq[HostRuntimeType],
                         checkedGlobals: Globals,
                         records: seq[HostRecord],
                         allowDependentSigma = false,
                         compiled: Table[string, string],
                         compiledRepr: Table[string, string] =
                           initTable[string, string](),
                         compiledReprTypes: Table[string, seq[string]] =
                           initTable[string, seq[string]]()): NimNode =
  ## Emit concrete Nim wrappers for first-order types, including generic type
  ## variables represented as opaque host boxes.
  if decl.kind != nnkProcDef:
    return nil
  let generic = genericRuntimeInfo(decl, mappings, records,
    allowDependentSigma = allowDependentSigma)
  if generic.error.len > 0: return nil
  let codecMappings = generic.codecMappings
  let params = decl[3]
  if params.len == 0 or params[0].kind == nnkEmpty:
    return nil
  let resultType = runtimeNimType(params[0], codecMappings, records,
                                  allowDependentSigma)
  if resultType.isNil: return nil

  var formal = newNimNode(nnkFormalParams)
  formal.add(ident("int"))
  var argSyms: seq[NimNode] = @[]
  var argNames: seq[string] = @[]
  var argEponymTypes: seq[NimNode] = @[]
  var argNimTypes: seq[NimNode] = @[]
  for i in 1 ..< params.len:
    let p = params[i]
    if p.kind != nnkIdentDefs: return nil
    let argType = runtimeNimType(p[^2], codecMappings, records,
                                 allowDependentSigma)
    if argType.isNil: return nil
    for j in 0 ..< p.len - 2:
      let argName = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
      let argSym = genSym(nskParam, $argName)
      let formalType = if callbackCanDeferGenericInference(params, i,
          generic.typeNames): ident"auto"
        else: argType
      let defaultValue = if p[^1].kind == nnkEmpty: newEmptyNode()
                         else: copyNimTree(p[^1])
      formal.add(newIdentDefs(argSym, formalType, defaultValue))
      argSyms.add(argSym)
      argNames.add($argName)
      argEponymTypes.add(p[^2])
      argNimTypes.add(argType)

  formal[0] = resultType

  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  let nameLit = newLit(defName)
  var wrapperBody = newStmtList()
  let globalsSym = genSym(nskLet, "checkedGlobals")
  wrapperBody.add(newLetStmt(globalsSym,
    newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
  var bindingSym: NimNode = nil
  if bindings.len > 0:
    bindingSym = genSym(nskVar, "runtimeBindings")
    wrapperBody.add(newVarStmt(bindingSym,
      newCall(bindSym"initRuntimeBindings")))
    for binding in bindings:
      wrapperBody.add(bindingCall(binding, bindingSym, globalsSym,
                                  codecMappings, records, checkedGlobals))

  var values = newNimNode(nnkBracket)
  for genericArg in genericRuntimeValueArgs(generic, globalsSym,
      codecMappings, records):
    values.add(genericArg)
  var wrapperIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  for i, argSym in argSyms:
    values.add(runtimeValueConversionExpr(argEponymTypes[i], argNimTypes[i],
      argSym, true, codecMappings, records, globalsSym,
      allowDependentSigma, wrapperIndexOverrides))
    if values[^1].isNil: return nil
    wrapperIndexOverrides.add((argNames[i], argSym))
  let valuesSeq = newTree(nnkPrefix, ident("@"), values)
  var wrapperValueNames = generic.genericNames.mapIt($it)
  wrapperValueNames.add(argNames)
  let piValueSlots = runtimePiValueSlots(checkedGlobals, defName,
    wrapperValueNames)
  let piRuntimeSlots = piValueSlots.slots
  let runtimeValues = newNimNode(nnkBracket)
  let q0Values = newNimNode(nnkBracket)
  let slotAlignmentMatches = piValueSlots.aligned and
    piRuntimeSlots.len == values.len
  if slotAlignmentMatches:
    for i, value in values:
      if piRuntimeSlots[i]: runtimeValues.add(value)
      else: q0Values.add(value)
  let runtimeValuesSeq = newTree(nnkPrefix, ident("@"), runtimeValues)
  let q0ValuesSeq = newTree(nnkPrefix, ident("@"), q0Values)
  var callArgs = @[dirLit, srcLit, nameLit, valuesSeq]
  if not bindingSym.isNil: callArgs.add(bindingSym)
  let runtimeValue = genSym(nskLet, "runtimeValue")
  var compiledName = compiled.getOrDefault(defName, "")
  let compiledReprName = compiledRepr.getOrDefault(defName, "")
  if compiledName.len > 0 and not slotAlignmentMatches:
    # The legacy interpreter path re-elaborates omitted implicits. Keep it
    # when the macro-time source telescope cannot be aligned exactly with
    # the checked Pi telescope used by generated code.
    compiledName = ""
  # Issue #330: when the definition has a representation-specialized proc
  # and the wrapper boundary is the identity (every formal and the result
  # are already the host representation — v1: `int`; v3: `int`,
  # `seq[int]`, `Option[int]`), call it directly with the host arguments.
  # No Value is allocated and no codec runs. The declared formals/result
  # are compared against the repr signature threaded through
  # `compileBlockProcs` (`compiledReprTypes`), not just shape-checked, so
  # a wrapper whose surface types disagree with the compiled repr proc
  # keeps the Value path instead of mis-calling it.
  var useRepr = compiledReprName.len > 0 and slotAlignmentMatches
  if useRepr:
    # Compare against the runtime slots only: the repr signature erases
    # q0 binders, while the surface formals still declare them.
    let wantTypes = compiledReprTypes.getOrDefault(defName, @[])
    var runtimeTypes: seq[NimNode] = @[]
    for i, at in argNimTypes:
      let slot = generic.genericNames.len + i
      if slot < piRuntimeSlots.len and piRuntimeSlots[slot]:
        runtimeTypes.add(at)
    if wantTypes.len != runtimeTypes.len + 1:
      useRepr = false
    else:
      for i, at in runtimeTypes:
        if not nimTypeMatchesRepr(at, wantTypes[i]):
          useRepr = false
          break
      if useRepr and not nimTypeMatchesRepr(resultType, wantTypes[^1]):
        useRepr = false
  if useRepr:
    if piRuntimeSlots.len != generic.genericNames.len + argSyms.len:
      useRepr = false
    var reprCall = newCall(ident(compiledReprName))
    for i, argSym in argSyms:
      let slot = generic.genericNames.len + i
      if slot < piRuntimeSlots.len and piRuntimeSlots[slot]:
        reprCall.add(argSym)
    if useRepr:
      result = newNimNode(nnkProcDef)
      result.add(newTree(nnkPostfix, ident("*"), ident(defName)))
      result.add(newEmptyNode())
      result.add(generic.genericParams)
      result.add(formal)
      result.add(newEmptyNode())
      result.add(newEmptyNode())
      result.add(reprCall)
      return result
  if compiledName.len > 0:
    # Issue #329: the definition has a native Value proc; evaluate through
    # it instead of re-walking the definition's term per call. The typed
    # calling convention (codecs, bindings) is unchanged.
    let bindingsArg = if bindingSym.isNil:
      newCall(bindSym"initRuntimeBindings")
    else:
      bindingSym
    wrapperBody.add(newLetStmt(runtimeValue,
      newCall(ident(compiledName), runtimeValuesSeq, bindingsArg,
        q0ValuesSeq)))
  else:
    wrapperBody.add(newLetStmt(runtimeValue,
      newCall(bindSym"callValueFuncDir", callArgs)))
  let resultExpr = runtimeValueConversionExpr(params[0], resultType,
    runtimeValue, false, codecMappings, records, globalsSym,
    allowDependentSigma, wrapperIndexOverrides)
  if resultExpr.isNil: return nil
  wrapperBody.add(resultExpr)

  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident("*"), ident(defName)))
  result.add(newEmptyNode())
  result.add(generic.genericParams)
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(wrapperBody)

proc runtimeTypeValueExpr(n: NimNode, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]]): NimNode =
  if n.isNil: return nil
  if n.kind == nnkStmtListExpr:
    if n.len != 1: return nil
    return runtimeTypeValueExpr(n[0], globals, overrides)
  if n.kind in {nnkCall, nnkObjConstr} and n.len > 0 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "Sig":
    let fields = runtimeSigmaFields(n, allowDependent = true)
    if fields.len < 2: return nil
    proc buildSigma(index: int,
        localOverrides: seq[tuple[name: string, value: NimNode]]): NimNode =
      if index == fields.high:
        return runtimeTypeValueExpr(fields[index].fieldType, globals,
          localOverrides)
      let domain = runtimeTypeValueExpr(fields[index].fieldType, globals,
        localOverrides)
      if domain.isNil: return nil
      var codomainOverrides = localOverrides
      var argument: NimNode = nil
      if fields[index].binder.len > 0:
        argument = genSym(nskParam, "runtimeSigmaArgument")
        codomainOverrides.add((fields[index].binder, argument))
      let codomain = buildSigma(index + 1, codomainOverrides)
      if codomain.isNil: return nil
      if argument.isNil:
        return newCall(bindSym"runtimeSigmaType", domain, codomain)
      let callback = newProc(
        params = @[bindSym"Value",
          newIdentDefs(argument, bindSym"Value", newEmptyNode())],
        body = newStmtList(codomain))
      var priorArguments = newNimNode(nnkBracket)
      for i, override in localOverrides:
        if i >= overrides.len or runtimeTypeReferencesName(n,
            overrides[i].name):
          priorArguments.add(copyNimTree(override.value))
      newCall(bindSym"runtimeDependentSigmaType", domain, globals,
        callback, newTree(nnkPrefix, ident"@", priorArguments))
    return buildSigma(0, overrides)
  if n.kind in {nnkIdent, nnkSym}:
    if overrides.len > 0:
      for i in countdown(overrides.high, 0):
        if $n == overrides[i].name:
          return copyNimTree(overrides[i].value)
    return newCall(bindSym"runtimeGlobalValue", globals, newLit($n))
  if n.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                nnkInt64Lit}:
    if n.intVal < 0: return newCall(bindSym"intToValue", newLit(n.intVal))
    return newCall(bindSym"natToValue", newLit(n.intVal), globals)
  if n.kind == nnkPrefix and n.len == 2 and $n[0] == "-" and
      n[1].kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                    nnkInt64Lit}:
    return newCall(bindSym"intToValue", newLit(-n[1].intVal))
  if n.kind == nnkPar and n.len == 1:
    return runtimeTypeValueExpr(n[0], globals, overrides)
  if n.kind in {nnkIfExpr, nnkIfStmt}:
    var branches: seq[tuple[condition, value: NimNode]] = @[]
    var elseBranch: NimNode = nil
    for branch in n:
      case branch.kind
      of nnkElifExpr, nnkElifBranch:
        if branch.len != 2: return nil
        let conditionValue = runtimeTypeValueExpr(branch[0], globals,
          overrides)
        if conditionValue.isNil: return nil
        var valueNode = branch[1]
        if valueNode.kind == nnkStmtList:
          if valueNode.len != 1: return nil
          valueNode = valueNode[0]
        let value = runtimeTypeValueExpr(valueNode, globals, overrides)
        if value.isNil: return nil
        branches.add((conditionValue, value))
      of nnkElseExpr, nnkElse:
        if branch.len != 1: return nil
        elseBranch = branch[0]
      else:
        return nil
    if branches.len == 0 or elseBranch.isNil: return nil
    if elseBranch.kind == nnkStmtList:
      if elseBranch.len != 1: return nil
      elseBranch = elseBranch[0]
    result = runtimeTypeValueExpr(elseBranch, globals, overrides)
    if result.isNil: return nil
    let ifThenElse = newCall(bindSym"runtimeGlobalValue", globals,
      newLit("ifThenElse"))
    for i in countdown(branches.high, 0):
      let branchType = newCall(bindSym"runtimeValueTypeOf",
        branches[i].value, globals)
      result = newCall(bindSym"callRuntimeValue", ifThenElse,
        newTree(nnkBracket, branchType, branches[i].condition,
          branches[i].value, result))
    return
  if n.kind in {nnkCall, nnkObjConstr} and n.len > 0 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "Pi":
    return runtimePiTypeValueExpr(n, globals, overrides)
  if n.kind == nnkInfix and n.len == 3 and $n[0] == "->":
    let domain = runtimeTypeValueExpr(n[1], globals, overrides)
    let codomain = runtimeTypeValueExpr(n[2], globals, overrides)
    if domain.isNil or codomain.isNil: return nil
    return newCall(bindSym"runtimeArrowType", domain, codomain)
  if n.kind in {nnkCall, nnkCommand, nnkBracketExpr, nnkObjConstr,
                nnkInfix} and n.len >= 2:
    let fnNode = if n.kind == nnkInfix:
      ident($n[0]) else: n[0]
    let fnValue = runtimeTypeValueExpr(fnNode, globals, overrides)
    if fnValue.isNil: return nil
    var args = newNimNode(nnkBracket)
    let firstArg = if n.kind == nnkInfix: 1 else: 1
    for i in firstArg ..< n.len:
      let argValue = runtimeTypeValueExpr(n[i], globals, overrides)
      if argValue.isNil: return nil
      args.add(argValue)
    return newCall(bindSym"callRuntimeValue", fnValue,
      newTree(nnkPrefix, ident"@", args))
  nil

proc dynamicGenericRuntimeWrapper(decl: NimNode, baseDir, src,
    defName: string, bindings: seq[HostPostulateBinding],
    mappings: seq[HostRuntimeType], checkedGlobals: Globals,
    records: seq[HostRecord],
    allowDependentSigma = false,
    returnRuntimeValue = false,
    allowGenericFunctionValues = false): NimNode =
  ## Emit a sibling wrapper where supported value-indexed generics are
  ## ordinary runtime parameters instead of Nim `static` parameters. For
  ## dependent Sigma values, the caller can request a typed overload whose
  ## codecs are checked against the generated Sigma witness.
  let generic = genericRuntimeInfo(decl, mappings, records,
    allowGenericValues = true,
    allowUnmappedValues = true,
    allowDependentSigma = allowDependentSigma,
    allowGenericFunctionValues = allowGenericFunctionValues)
  if generic.error.len > 0 or generic.genericNames.len == 0 or
      generic.typeNames.len > 0:
    return nil
  let params = decl[3]
  if params.len == 0 or params[0].kind == nnkEmpty: return nil
  let resultType = if returnRuntimeValue:
    nil
  else:
    runtimeNimType(params[0], generic.codecMappings, records,
      allowDependentSigma)
  if not returnRuntimeValue and resultType.isNil: return nil
  var formal = newNimNode(nnkFormalParams)
  formal.add(if returnRuntimeValue:
    bindSym"RuntimeValueResult" else: resultType)
  var genericSyms: seq[NimNode] = @[]
  var genericNimTypes: seq[NimNode] = @[]
  var genericValueHasCodec: seq[bool] = @[]
  for i, genericName in generic.genericNames:
    var dynamicType: NimNode = nil
    var hasValueCodec = false
    if generic.genericNatArgs[i] or generic.genericIntArgs[i]:
      dynamicType = ident"int"
    elif generic.genericBoolArgs[i]:
      dynamicType = ident"bool"
    elif generic.genericValueArgs[i]:
      if not generic.genericValueTypes[i].isNil:
        let codecType = runtimeNimType(generic.genericValueTypes[i],
          generic.codecMappings, records, allowDependentSigma)
        hasValueCodec = not codecType.isNil
        if hasValueCodec:
          dynamicType = if not runtimeEponymPiParts(
              generic.genericValueTypes[i]).resultType.isNil:
            ident"auto"
          else:
            codecType
      if dynamicType.isNil:
        dynamicType = bindSym"RuntimeValue"
    elif not generic.genericMappedTypes[i].isNil:
      dynamicType = copyNimTree(generic.genericMappedNimTypes[i])
    if dynamicType.isNil: return nil
    let sym = genSym(nskParam, "dynamicGeneric" & $genericName)
    formal.add(newIdentDefs(sym, dynamicType, newEmptyNode()))
    genericSyms.add(sym)
    genericNimTypes.add(dynamicType)
    genericValueHasCodec.add(hasValueCodec)
  var argSyms: seq[NimNode] = @[]
  var argNames: seq[string] = @[]
  var argEponymTypes: seq[NimNode] = @[]
  var argNimTypes: seq[NimNode] = @[]
  for i in 1 ..< params.len:
    let p = params[i]
    if p.kind != nnkIdentDefs: return nil
    let argType = runtimeNimType(p[^2], generic.codecMappings, records,
                                 allowDependentSigma)
    if argType.isNil: return nil
    for j in 0 ..< p.len - 2:
      let argName = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
      let argSym = genSym(nskParam, $argName)
      formal.add(newIdentDefs(argSym, argType, newEmptyNode()))
      argSyms.add(argSym)
      argNames.add($argName)
      argEponymTypes.add(p[^2])
      argNimTypes.add(argType)
  let globalsSym = genSym(nskLet, "dynamicGlobals")
  let defsSym = genSym(nskLet, "dynamicDefs")
  let bindingsSym = genSym(nskVar, "dynamicBindings")
  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  let nameLit = newLit(defName)
  var body = newStmtList()
  body.add(newLetStmt(globalsSym,
    newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
  var typeIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  var genericIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  for i, genericSym in genericSyms:
    var encodedGeneric: NimNode
    if generic.genericNatArgs[i]:
      encodedGeneric = newCall(bindSym"natToValue", genericSym, globalsSym)
    elif generic.genericBoolArgs[i]:
      encodedGeneric = newCall(bindSym"boolToValue", genericSym, globalsSym)
    elif generic.genericIntArgs[i]:
      encodedGeneric = newCall(bindSym"intToValue", genericSym)
    elif generic.genericValueArgs[i]:
      if genericValueHasCodec[i]:
        encodedGeneric = runtimeValueConversionExpr(
          generic.genericValueTypes[i], genericNimTypes[i], genericSym,
          true, generic.codecMappings, records, globalsSym,
          allowDependentSigma, genericIndexOverrides)
      else:
        encodedGeneric = copyNimTree(genericSym)
    elif not generic.genericMappedTypes[i].isNil:
      encodedGeneric = runtimeValueConversionExpr(
        generic.genericMappedTypes[i], generic.genericMappedNimTypes[i],
        genericSym, true, generic.codecMappings, records, globalsSym,
        allowDependentSigma, genericIndexOverrides)
    if encodedGeneric.isNil: return nil
    var validateEncodedMappedVariant = false
    var validateEncodedIndexedCodec = false
    if not generic.genericValueArgs[i] and
        not generic.genericMappedTypes[i].isNil:
      let mappedHead = runtimeTypeHead(generic.genericValueTypeExprs[i])
      if mappedHead.kind == nnkIdent:
        for mapping in mappings:
          if mapping.isRuntimeVariant and
              mapping.eponymName == $mappedHead:
            validateEncodedMappedVariant = true
          if mapping.isRuntimeCodec and
              mapping.eponymName == $mappedHead and
              generic.genericValueTypeExprs[i].kind in
                {nnkCall, nnkObjConstr, nnkBracketExpr}:
            validateEncodedIndexedCodec = true
    let validateUnmappedValue = generic.genericValueArgs[i] and
      not genericValueHasCodec[i]
    let validateCodecBackedDependentSigma =
      generic.genericValueArgs[i] and genericValueHasCodec[i] and
      containsDependentSigma(generic.genericValueTypeExprs[i])
    let validateCodecBackedFunctionValue =
      generic.genericValueArgs[i] and genericValueHasCodec[i] and
      containsEponymPiType(generic.genericValueTypeExprs[i])
    if validateUnmappedValue or validateEncodedMappedVariant or
        validateEncodedIndexedCodec or validateCodecBackedDependentSigma or
        validateCodecBackedFunctionValue:
      let expectedType = runtimeTypeValueExpr(
        generic.genericValueTypeExprs[i], globalsSym, typeIndexOverrides)
      if expectedType.isNil: return nil
      body.add(newCall(bindSym"validateRuntimeValueAgainstType",
        if validateUnmappedValue: genericSym else: encodedGeneric,
        expectedType, globalsSym))
    typeIndexOverrides.add(($generic.genericNames[i], encodedGeneric))
    genericIndexOverrides.add(($generic.genericNames[i], genericSym))
  body.add(newLetStmt(defsSym,
    newCall(bindSym"getDefsDir", dirLit, srcLit)))
  body.add(newVarStmt(bindingsSym, newCall(bindSym"initRuntimeBindings")))
  for binding in bindings:
    body.add(bindingCall(binding, bindingsSym, globalsSym,
                         generic.codecMappings, records, checkedGlobals))
  var values = newNimNode(nnkBracket)
  var indexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  for i, genericName in generic.genericNames:
    var encoded: NimNode
    if generic.genericNatArgs[i]:
      encoded = newCall(bindSym"natToValue", genericSyms[i], globalsSym)
    elif generic.genericBoolArgs[i]:
      encoded = newCall(bindSym"boolToValue", genericSyms[i], globalsSym)
    elif generic.genericIntArgs[i]:
      encoded = newCall(bindSym"intToValue", genericSyms[i])
    elif generic.genericValueArgs[i]:
      if genericValueHasCodec[i]:
        encoded = runtimeValueConversionExpr(generic.genericValueTypes[i],
          genericNimTypes[i], genericSyms[i], true, generic.codecMappings,
          records, globalsSym, allowDependentSigma, indexOverrides)
      else:
        encoded = copyNimTree(genericSyms[i])
    else:
      encoded = runtimeValueConversionExpr(generic.genericMappedTypes[i],
        genericNimTypes[i], genericSyms[i], true, generic.codecMappings,
        records, globalsSym, allowDependentSigma, indexOverrides)
    if encoded.isNil: return nil
    values.add(encoded)
    indexOverrides.add(($genericName, genericSyms[i]))
  for i, argSym in argSyms:
    let encoded = runtimeValueConversionExpr(argEponymTypes[i], argNimTypes[i],
      argSym, true, generic.codecMappings, records, globalsSym,
      allowDependentSigma, indexOverrides)
    if encoded.isNil: return nil
    values.add(encoded)
    indexOverrides.add((argNames[i], argSym))
  let runtimeResult = genSym(nskLet, "dynamicRuntimeResult")
  let call = newCall(bindSym"callDefValueWithBindings",
    newCall(bindSym"findDef", defsSym, nameLit),
    newTree(nnkPrefix, ident"@", values), bindingsSym, globalsSym)
  body.add(newLetStmt(runtimeResult, call))
  if returnRuntimeValue:
    body.add(newTree(nnkTupleConstr, runtimeResult, globalsSym))
  else:
    let decoded = runtimeValueConversionExpr(params[0], resultType,
      runtimeResult, false, generic.codecMappings, records, globalsSym,
      allowDependentSigma, indexOverrides)
    if decoded.isNil: return nil
    body.add(decoded)
  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident"*", ident(if returnRuntimeValue:
    defName & "RuntimeValueDynamic" else: defName & "Dynamic")))
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(body)

proc typedRuntimeValueWrapper(decl: NimNode, baseDir, src, defName: string,
                              bindings: seq[HostPostulateBinding],
                              mappings: seq[HostRuntimeType],
                              checkedGlobals: Globals,
                              records: seq[HostRecord],
                              allowDependentSigma = false,
                              compiled: Table[string, string]): NimNode =
  ## Emit a typed host-argument overload that returns the checked result as a
  ## Value. This keeps the definition's full Eponym signature while exposing
  ## only codecs explicitly described by runtimeType and the primitive codecs.
  if decl.kind != nnkProcDef:
    return nil
  let generic = genericRuntimeInfo(decl, mappings, records,
    allowDependentSigma = allowDependentSigma)
  if generic.error.len > 0: return nil
  let codecMappings = generic.codecMappings
  let params = decl[3]
  if params.len <= 1 or params[0].kind == nnkEmpty:
    return nil

  var formal = newNimNode(nnkFormalParams)
  formal.add(bindSym"RuntimeValueResult")
  var argSyms: seq[NimNode] = @[]
  var argNames: seq[string] = @[]
  var eponymTypes: seq[NimNode] = @[]
  var nimTypes: seq[NimNode] = @[]
  for i in 1 ..< params.len:
    let p = params[i]
    if p.kind != nnkIdentDefs: return nil
    let nimType = runtimeNimType(p[^2], codecMappings, records,
                                 allowDependentSigma)
    if nimType.isNil: return nil
    for j in 0 ..< p.len - 2:
      let argName = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
      let argSym = genSym(nskParam, $argName)
      let formalType = if callbackCanDeferGenericInference(params, i,
          generic.typeNames): ident"auto"
        else: nimType
      let defaultValue = if p[^1].kind == nnkEmpty: newEmptyNode()
                         else: copyNimTree(p[^1])
      formal.add(newIdentDefs(argSym, formalType, defaultValue))
      argSyms.add(argSym)
      argNames.add($argName)
      eponymTypes.add(p[^2])
      nimTypes.add(nimType)

  let globalsSym = genSym(nskLet, "runtimeGlobals")
  var values = newNimNode(nnkBracket)
  for genericArg in genericRuntimeValueArgs(generic, globalsSym,
      codecMappings, records):
    values.add(genericArg)
  var runtimeValueIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  for i, argSym in argSyms:
    let converted = runtimeValueConversionExpr(eponymTypes[i], nimTypes[i],
      argSym, true, codecMappings, records, globalsSym,
      allowDependentSigma, runtimeValueIndexOverrides)
    if converted.isNil: return nil
    values.add(converted)
    runtimeValueIndexOverrides.add((argNames[i], argSym))
  let valuesSeq = newTree(nnkPrefix, ident("@"), values)
  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  let nameLit = newLit(defName)
  let defsSym = genSym(nskLet, "runtimeDefs")
  let runtimeValueSym = genSym(nskLet, "runtimeValue")
  var body = newStmtList()
  body.add(newLetStmt(globalsSym,
    newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
  body.add(newLetStmt(defsSym,
    newCall(bindSym"getDefsDir", dirLit, srcLit)))
  var bindingSym: NimNode = nil
  bindingSym = genSym(nskVar, "runtimeBindings")
  body.add(newVarStmt(bindingSym, newCall(bindSym"initRuntimeBindings")))
  if bindings.len > 0:
    for binding in bindings:
      body.add(bindingCall(binding, bindingSym, globalsSym, codecMappings,
                           records, checkedGlobals))
  var wrapperValueNames = generic.genericNames.mapIt($it)
  wrapperValueNames.add(argNames)
  let piValueSlots = runtimePiValueSlots(checkedGlobals, defName,
    wrapperValueNames)
  let piRuntimeSlots = piValueSlots.slots
  let compiledArgs = newNimNode(nnkBracket)
  let q0Args = newNimNode(nnkBracket)
  let slotAlignmentMatches = piValueSlots.aligned and
    piRuntimeSlots.len == values.len
  if slotAlignmentMatches:
    for i, value in values:
      if piRuntimeSlots[i]: compiledArgs.add(value)
      else: q0Args.add(value)
  let compiledArgsSeq = newTree(nnkPrefix, ident("@"), compiledArgs)
  let q0ArgsSeq = newTree(nnkPrefix, ident("@"), q0Args)
  let compiledName = compiled.getOrDefault(defName, "")
  let runtimeCall =
    if compiledName.len > 0 and slotAlignmentMatches:
      # Issue #329: evaluate through the definition's native Value proc.
      newCall(ident(compiledName), compiledArgsSeq, bindingSym, q0ArgsSeq)
    else:
      newCall(bindSym"callDefValueWithBindings",
        newCall(bindSym"findDef", defsSym, nameLit), valuesSeq, bindingSym)
  body.add(newLetStmt(runtimeValueSym,
    runtimeCall))
  body.add(newTree(nnkTupleConstr, runtimeValueSym, globalsSym))

  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident("*"), ident(defName & "RuntimeValue")))
  result.add(newEmptyNode())
  result.add(generic.genericParams)
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(body)

proc checkedLambdaArity(definition: ElabDef): int =
  ## Imported definitions have no Nim declaration from which to get arity.
  ## Their checked lambda telescope is the source of truth for the raw ABI.
  var body = definition.tmTm
  while not body.isNil and body.kind == tLam:
    inc result
    body = body.scope.bdy

proc rawRuntimeValueWrapper(baseDir, src, defName: string,
    expectedArity: int,
    bindings: seq[HostPostulateBinding], mappings: seq[HostRuntimeType],
    records: seq[HostRecord], checkedGlobals: Globals,
    wrapperSuffix = "RuntimeValue"): NimNode =
  ## Expose an imported checked definition when no local Nim signature is
  ## available. Callers explicitly pass its arguments as Eponym Values.
  let argsSym = genSym(nskParam, "runtimeArguments")
  let globalsSym = genSym(nskLet, "runtimeGlobals")
  let defsSym = genSym(nskLet, "runtimeDefs")
  let bindingsSym = genSym(nskVar, "runtimeBindings")
  let valueSym = genSym(nskLet, "runtimeValue")
  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  let nameLit = newLit(defName)
  let arityLit = newLit(expectedArity)
  var body = newStmtList()
  body.add quote do:
    if `argsSym`.len != `arityLit`:
      raise newException(ValueError,
        "runtimeValue argument count mismatch for " & `nameLit`)
  body.add(newLetStmt(globalsSym,
    newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
  body.add(newLetStmt(defsSym,
    newCall(bindSym"getDefsDir", dirLit, srcLit)))
  body.add(newVarStmt(bindingsSym, newCall(bindSym"initRuntimeBindings")))
  for binding in bindings:
    body.add(bindingCall(binding, bindingsSym, globalsSym, mappings, records,
                         checkedGlobals))
  body.add(newLetStmt(valueSym,
    newCall(bindSym"callDefValueWithBindings",
      newCall(bindSym"findDef", defsSym, nameLit), argsSym, bindingsSym,
      globalsSym)))
  body.add(newTree(nnkTupleConstr, valueSym, globalsSym))
  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident"*",
    ident(defName & wrapperSuffix)))
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  var formal = newNimNode(nnkFormalParams)
  formal.add(bindSym"RuntimeValueResult")
  formal.add(newIdentDefs(argsSym,
    newTree(nnkBracketExpr, ident"openArray", bindSym"RuntimeValue"), newEmptyNode()))
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(body)

macro eponymBlock*(body: untyped): untyped =
  ## Elaborate a block of Nim-syntax Eponym definitions (no """).
  ## Uses call syntax: proc f(x: Int): Int = ..., postulate(I, Univ),
  ## data(N, Univ): block.
  ## Quantity binders (Issue #28/#64): `ch {.linear.}` / `ch {.erased.}`
  ## in proc/data params emit `(1 ch : ...)` / `(0 ch : ...)` binders.
  ## Dependent Pi/Sigma types: Pi(x: A, y {.linear.}: B, C),
  ## Sig(x: A, B), Sig(A, B).
  ## `import "path.ep"` (Issue #131): Eponym-module import, resolved
  ## relative to the Nim file containing the eponymBlock call; makes prelude
  ## definitions (lib/*.ep) available without redefinition.
  ## `elim(name, Ty)` / `red(lhs, rhs)` (Issue #151): eliminator and
  ## computation-rule declarations, e.g. the Bool/Nat eliminators of smoke
  ## tests 07/08.
  ## `def(name, Ty):` with a block of `clause([pat, ...], rhs)` (Issue #151):
  ## clause-style definitions; constructor-application patterns are
  ## parenthesized automatically.
  ## `byTac(name)` (Issue #151): tactic term (`by refl`, smoke test 14).
  ## `x {.qvar(q).}` (Issue #151): quantity-variable binder `(q x : T)`.
  ## Nim-safe name mappings: `vecnil` -> `nil`, `unitv` -> `<>`,
  ## `unitTy` -> `1` (unit type), `emptyTy` -> `O` (empty type).
  ## Generates callable fixed-arity wrappers for primitive Int/Nat and
  ## explicitly mapped opaque postulated types. Unsupported legacy shapes
  ## retain the varargs[int] compatibility wrapper.
  let baseDir = callerDir(body)
  var sourceLineMap: seq[DiagnosticSourceLoc]
  var hasEponymImport = false
  for st in body:
    if st.kind == nnkImportStmt:
      hasEponymImport = true
      break
  let src = if hasEponymImport:
    blockToEponym(body, baseDir)
  else:
    blockToEponymInternal(body, baseDir, sourceLineMap, true)
  var runtimeValueNames = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len == 2 and st[0].kind == nnkIdent and
        $st[0] == "runtimeValue":
      let name = $st[1]
      if name in runtimeValueNames:
        error("duplicate runtimeValue request for '" & name & "'", st)
      runtimeValueNames.incl(name)
  # Issue #131: imports resolve relative to the calling Nim file's dir.
  var defs: seq[ElabDef]
  var allDefs: seq[ElabDef]
  var checkedGlobals: Globals
  try:
    let checked = elabCheckDirStateAll(src, baseDir)
    defs = checked.defs
    allDefs = checked.allDefs
    checkedGlobals = checked.globals
  except ElabError as e:
    let detail = if hasEponymImport: e.msg else:
      sourceMappedDiagnostic(e.msg, e.loc, sourceLineMap)
    error("eponymBlock elaboration error: " & detail, body)
  except ParseError as e:
    let detail = if hasEponymImport: e.msg else:
      sourceMappedDiagnostic(e.msg, e.loc, sourceLineMap)
    error("eponymBlock parse error: " & detail, body)

  for requested in runtimeValueNames:
    var found = false
    for d in allDefs:
      if d.name == requested: found = true
    if not found:
      error("runtimeValue names no checked definition: " & requested, body)
    var declaration: NimNode = nil
    for st in body:
      if st.kind == nnkProcDef and $st[0] == requested:
        declaration = st
        break
    if declaration.isNil:
      continue # Imported checked definitions use the raw Value ABI.
    if declaration[3].len == 0 or declaration[3][0].kind == nnkEmpty:
      error("runtimeValue requires a checked definition with a result: " &
        requested, body)
    for i in 1 ..< declaration[3].len:
      if declaration[3][i].kind != nnkIdentDefs:
        error("runtimeValue supports ordinary fixed-arity parameters: " & requested,
          declaration)

  var bindings = hostPostulateBindings(body)
  for binding in bindings.mitems:
    if binding.pairResult and binding.pairResultType.isNil and
        binding.postulateName in checkedGlobals:
      let checkedShape = runtimeTermTypeAfterArgs(
        checkedGlobals[binding.postulateName].ty, binding.pairArgCount,
        checkedGlobals)
      if not checkedShape.resultType.isNil:
        binding.pairResultType = checkedShape.resultType
        binding.pairResultArgNames = checkedShape.argNames
  for binding in bindings:
    if not bindingIsReferenced(body, binding.postulateName, allDefs,
                               checkedGlobals):
      error("eponymBlock binding error: binding for postulate '" &
        binding.postulateName & "' is unused by every proc body", body)
  let runtimeTypes = hostRuntimeTypes(body, checkedGlobals)
  let trustedRuntimeRecords = trustedRuntimeRecordNames(body)
  let records = hostRecords(body, trustedRuntimeRecords)
  for requested in trustedRuntimeRecords:
    let recordIndex = findHostRecord(records, requested)
    if recordIndex < 0 or records[recordIndex].isVariant:
      error("runtimeRecordTrusted names no record: " & requested, body)
    var hasRuntimeMapping = false
    for mapping in runtimeTypes:
      if mapping.eponymName == requested and not mapping.isRuntimeVector and
          not mapping.isRuntimeList and not mapping.isRuntimeOption and
          not mapping.isRuntimeCodec:
        hasRuntimeMapping = true
    if not hasRuntimeMapping:
      error("runtimeRecordTrusted requires runtimeType(" & requested & ", NimType)",
        body)
  let trustedRuntimePairs = trustedRuntimePairNames(body)
  for requested in trustedRuntimePairs:
    var found = false
    for d in defs:
      if d.name == requested: found = true
    if not found:
      error("runtimePairTrusted names no checked definition: " & requested,
        body)
    var declaration: NimNode = nil
    for st in body:
      if st.kind == nnkProcDef and $st[0] == requested:
        declaration = st
        break
    if declaration.isNil:
      error("runtimePairTrusted requires a Nim declaration for: " & requested,
        body)
  var usesBoolCodec = false
  for st in body:
    if st.kind == nnkProcDef and mentionsName(st[3], "Bool"):
      usesBoolCodec = true
  if usesBoolCodec:
    try:
      validateHostBoolCodec(checkedGlobals)
    except ValueError as e:
      error("eponymBlock runtimeType error: " & e.msg, body)
  for mapping in runtimeTypes:
    try:
      if mapping.isRuntimeVector:
        validateHostVectorCodec(checkedGlobals, mapping.eponymName)
      elif mapping.isRuntimeList:
        validateHostListCodec(checkedGlobals, mapping.eponymName)
      elif mapping.isRuntimeOption:
        validateHostOptionCodec(checkedGlobals, mapping.eponymName)
      elif mapping.isRuntimeVariant:
        let constructors = runtimeVariantConstructorNames(checkedGlobals,
          mapping.eponymName)
        validateRuntimeVariantConstructors(checkedGlobals,
          mapping.eponymName, constructors)
      elif mapping.isRuntimeCodec:
        validateHostRuntimeCodecType(checkedGlobals, mapping.eponymName)
      else:
        let recordIndex = findHostRecord(records, mapping.eponymName)
        if recordIndex >= 0:
          let record = records[recordIndex]
          if record.isVariant and
              (record.hasDependentField or record.constructors.len == 0):
            raise newException(ValueError,
              "runtime enum codec for '" & mapping.eponymName &
              "' requires only nullary constructors returning the unindexed family")
        else:
          validateHostOpaqueType(checkedGlobals, mapping.eponymName)
    except ValueError as e:
      error("eponymBlock runtimeType error: " & e.msg, body)
  for binding in bindings:
    try:
      if binding.rawValue:
        discard validateHostValueNaryType(checkedGlobals,
                                          binding.postulateName)
        continue
      if binding.pairResult:
        let pairArgs = binding.eponymTypes[0 ..< binding.pairArgCount]
        validateHostSigmaAdapterType(checkedGlobals,
          binding.postulateName, pairArgs,
          binding.eponymTypes[binding.pairArgCount],
          binding.eponymTypes[binding.pairArgCount + 1],
          binding.trustedPairIndex)
        continue
      var usesCustomCodec = false
      for typeName in binding.eponymTypes:
        for mapping in runtimeTypes:
          if mapping.eponymName == typeName and mapping.isRuntimeCodec:
            usesCustomCodec = true
      if binding.eponymTypes.len >= 7 or usesCustomCodec:
        var adapterTypes = binding.eponymTypes
        if binding.eponymTypes.len == 1:
          adapterTypes = @[binding.eponymTypes[0], binding.eponymTypes[0]]
        validateHostMappedNaryType(checkedGlobals, binding.postulateName,
                                   adapterTypes)
        continue
      case binding.eponymTypes.len
      of 0:
        validateHostIntUnaryType(checkedGlobals, binding.postulateName)
      of 1:
        let required = validateHostOpaqueUnaryType(checkedGlobals,
                                                    binding.postulateName)
        if required != binding.eponymTypes[0]:
          raise newException(ValueError,
            "postulate '" & binding.postulateName & "' requires opaque Eponym type '" &
            required & "', not '" & binding.eponymTypes[0] & "'")
      of 2:
        if isCheckedNatType(checkedGlobals, binding.eponymTypes[1]):
          validateHostOpaqueNatUnaryType(checkedGlobals,
            binding.postulateName, binding.eponymTypes[0])
        else:
          validateHostOpaqueMapUnaryType(checkedGlobals,
            binding.postulateName, binding.eponymTypes[0],
            binding.eponymTypes[1])
      of 3:
        if isCheckedNatType(checkedGlobals, binding.eponymTypes[0]):
          validateHostNatOpaqueBinaryType(checkedGlobals,
            binding.postulateName, binding.eponymTypes[1],
            binding.eponymTypes[2])
        else:
          validateHostOpaqueBinaryType(checkedGlobals, binding.postulateName,
            binding.eponymTypes[0], binding.eponymTypes[1],
            binding.eponymTypes[2])
      of 4:
        validateHostOpaqueTernaryType(checkedGlobals, binding.postulateName,
          binding.eponymTypes[0], binding.eponymTypes[1],
          binding.eponymTypes[2], binding.eponymTypes[3])
      of 5:
        validateHostOpaqueQuaternaryType(checkedGlobals,
          binding.postulateName, binding.eponymTypes[0],
          binding.eponymTypes[1], binding.eponymTypes[2],
          binding.eponymTypes[3], binding.eponymTypes[4])
      of 6:
        validateHostOpaqueQuinaryType(checkedGlobals,
          binding.postulateName, binding.eponymTypes[0],
          binding.eponymTypes[1], binding.eponymTypes[2],
          binding.eponymTypes[3], binding.eponymTypes[4],
          binding.eponymTypes[5])
      else:
        let bindingForm = if binding.mutableArgs:
          "bindPostulateMutable" else: "bindPostulate"
        raise newException(ValueError,
          bindingForm & " supports Int -> Int, opaque T -> T, opaque T -> U, " &
          "opaque T -> Nat, Nat -> opaque T -> opaque U, opaque A -> B -> C, " &
          "opaque A -> B -> C -> D, opaque A -> B -> C -> D -> E, and " &
          "opaque A -> B -> C -> D -> E -> F")
    except ValueError as e:
      error("eponymBlock binding error: " & e.msg, body)

  when defined(eponymTrustReport):
    let trustLines = trustBoundaryReportLines(bindings, runtimeTypes,
      trustedRuntimePairs, trustedRuntimeRecords)
    echo "[eponym trust] block at " & lineInfoObj(body).filename & ":" &
      $lineInfoObj(body).line
    if trustLines.len == 0:
      echo "[eponym trust]   no explicit host runtime opt-ins"
    else:
      for trustLine in trustLines:
        echo "[eponym trust]   " & trustLine
    echo "[eponym trust]   QTT single-use applies inside checked Eponym terms; " &
      "Nim aliases around mapped references are outside that check"

  # Issue #329: compile eligible definitions to native Value procs, emitted
  # before the wrappers (callees before callers). Wrappers for compiled
  # definitions reroute their evaluation call to the compiled proc.
  # cgUserLines maps each def to its line in the calling file, so runtime
  # errors in compiled code report user source positions.
  let cgLocFile = lineInfoObj(body).filename
  var cgUserLines = initTable[string, int]()
  for d in defs:
    var userLine = lineInfoObj(body).line
    for st in body:
      if st.kind == nnkProcDef and $st[0] == d.name:
        userLine = lineInfoObj(st).line
        break
      if st.kind == nnkCall and st.len > 1 and st[0].kind == nnkIdent and
          $st[0] == "def" and st[1].kind == nnkIdent and $st[1] == d.name:
        userLine = lineInfoObj(st).line
        break
    cgUserLines[d.name] = userLine
  let cgBlock = compileBlockProcs(defs, checkedGlobals, baseDir, src,
    cgLocFile, cgUserLines, runtimeTypes)

  when defined(eponymCodegenReport):
    for d in defs:
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

  result = newStmtList()
  let dirLit = newLit(baseDir)
  for p in cgBlock.procs:
    result.add(p)
  for d in defs:
    let srcLit = newLit(src)
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
          let srcLit = newLit(src)
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
            baseDir, src, d.name, bindings, runtimeTypes, checkedGlobals,
            records, allowDependentSigma, cgBlock.compiled)
          if not typedValueWrapper.isNil:
            result.add(typedValueWrapper)
      let allowDependentSigma = d.name in trustedRuntimePairs
      let typedWrapper = typedRuntimeWrapper(procDecl, baseDir, src, d.name,
        bindings, runtimeTypes, checkedGlobals, records, allowDependentSigma,
        cgBlock.compiled, cgBlock.compiledRepr, cgBlock.reprTypes)
      if not typedWrapper.isNil:
        result.add(typedWrapper)
      else:
        result.add(unsupportedRuntimeWrapper(procDecl, d.name, runtimeTypes,
          records, allowDependentSigma))
      let dynamicWrapper = dynamicGenericRuntimeWrapper(procDecl, baseDir,
        src, d.name, bindings, runtimeTypes, checkedGlobals, records,
        allowDependentSigma)
      if not dynamicWrapper.isNil:
        result.add(dynamicWrapper)
      let addTypedDynamicGenericValueOverloads =
        not allowDependentSigma and
        hasCodecBackedDynamicValueBinder(procDecl, runtimeTypes, records)
      if addTypedDynamicGenericValueOverloads:
        let typedDynamicGenericValueWrapper = dynamicGenericRuntimeWrapper(
          procDecl, baseDir, src, d.name, bindings, runtimeTypes,
          checkedGlobals, records, allowDependentSigma = true,
          allowGenericFunctionValues = true)
        if not typedDynamicGenericValueWrapper.isNil:
          result.add(typedDynamicGenericValueWrapper)
      if d.name in runtimeValueNames:
        let dynamicRuntimeValueWrapper = dynamicGenericRuntimeWrapper(procDecl,
          baseDir, src, d.name, bindings, runtimeTypes, checkedGlobals,
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
            dynamicGenericRuntimeWrapper(procDecl, baseDir, src, d.name,
              bindings, runtimeTypes, checkedGlobals, records,
              allowDependentSigma = true, returnRuntimeValue = true,
              allowGenericFunctionValues = true)
          if not typedDynamicGenericValueRuntimeValueWrapper.isNil:
            result.add(typedDynamicGenericValueRuntimeValueWrapper)
      continue
    if d.name in runtimeValueNames:
      result.add(rawRuntimeValueWrapper(baseDir, src, d.name,
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
            baseDir, src, requested, bindings, runtimeTypes, checkedGlobals,
            records, false, initTable[string, string]())
          if not typedImportedWrapper.isNil:
            result.add(typedImportedWrapper)
          let typedImportedValueWrapper = typedRuntimeValueWrapper(
            importedDecl, baseDir, src, requested, bindings, runtimeTypes,
            checkedGlobals, records, false, initTable[string, string]())
          if not typedImportedValueWrapper.isNil:
            result.add(typedImportedValueWrapper)
        result.add(rawRuntimeValueWrapper(baseDir, src, requested,
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
proc twice (A : Type 0) (f : A -> A) (x : A) : A =
  f (f x)
proc pairSwap (A : Type 0) (B : Type 0) (p : Sig (u : A). B) : Sig (v : B). A =
  (snd p, fst p)
"""
  echo "ok: eponym macro accepts well-typed programs at compile time"
