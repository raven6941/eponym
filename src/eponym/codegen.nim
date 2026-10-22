## Phase 1 codegen (Issue #329): naive Value-level backend.
##
## Compiles erased, closed core `Term`s to Nim AST that manipulates `Value`s
## directly: constructors become `Value` constructions, eliminators become
## case dispatches. Same semantics as the `evalWhnf` interpreter, but no
## dispatch loop over `Term` nodes and no per-call re-walk of the definition's
## term (today every wrapper call re-runs `evalWithBindings` on the def term).
##
## Runs at macro-expansion time (inside the Nim VM): pure functions over
## `Term`, no module-level state. Per-definition tiering: a definition
## outside the supported fragment gets no compiled proc and keeps today's
## interpreter wrapper. The typed-wrapper calling convention is unchanged;
## only the wrapper body's evaluation call is rerouted.
##
## Issue #330 adds a representation-specialized tier on top: definitions
## whose signatures map to plain host representations (the int fragment:
## Eponym types mapped to Nim `int` via `runtimeType` — `Int`, `Nat`, `Bool`)
## get an additional `eponymCompiledRepr_<name>(p1: int, ...): int` proc
## whose body is direct host code — primitive Int ops become Nim arithmetic,
## Nat/Bool constructors become int literals and arithmetic, `natElim`
## becomes an iterative fold and `boolElim` a conditional, calls become
## direct calls. The typed wrapper prefers the repr proc when the boundary
## is the identity (all-int formals and result), skipping the Value
## conversions.
##
## Supported fragment (anything else -> interpreter fallback):
## - all term forms except `tMeta` (rejected already by erasure)
## - `tR` to postulates / data constructors: neutral value or bindings lookup
## - `tR` to definitions compiled in the same block: direct recursive call
## - `tR` to other definitions: slow path through `callValueFuncDir`
## - eliminators (`wRed`): only fully applied, via a generated
##   `eponymElim_<name>` proc holding the static case dispatch over the
##   registered reduction rules; emitted constructor labels are validated
##   against that table before code is returned; partially-applied or bare
##   eliminator references fall back to the interpreter
## - `tPrim`: primitive Int ops via the existing `vPrim` accumulation
##
## Deliberate deviations from the interpreter (all unreachable in checked
## code, documented here):
## - `syn` fields are approximate (never nil, but not substituted): semantics
##   live in `whnf`; `syn` is only a fallback for runtime type inference.
## - an eliminator scrutinee whose spine length is not exactly
##   `nParams + ctorArity` yields a stuck neutral instead of proceeding with
##   a short environment (the interpreter would raise `IndexDefect` there).
## - refIds are baked in as integer literals. `compileBlockProcs` validates
##   every emitted id against the current Globals table and refuses to emit
##   code if it cannot resolve the id to its expected name.
## - reduction-rule contractum templates are compiled as written (unerased):
##   erasure is a closed-term pass and templates are open. This matches the
##   interpreter, which fires `fireRed` on the unerased template.

import std/[tables, macros, algorithm]
import eponym_init   # Term, Value, WhnfKind, smart constructors
import preterm       # Quantity
import elab          # ElabDef, Globals, GEntry
import erasure       # eraseQ0Arguments
import eponym_embed  # callValueFuncDir, initRuntimeBindings (bindSym targets)

type
  CgUnsupported* = object of CatchableError
    ## Raised when a term is outside the compilable fragment. Caught at the
    ## definition boundary; the definition keeps its interpreter wrapper.

  CodegenTier* = enum
    cgtInterpreter, cgtValue, cgtRepr

  CodegenReportEntry* = object
    tier*: CodegenTier
    reason*: string
    slowPaths*: seq[string]

  CgRefKind* = enum
    cgkPostulate  # postulate, type former, or anything neutral
    cgkCtor       # data constructor (neutral spine growth)
    cgkElim       # eliminator with a registered reduction rule
    cgkDefn       # definition (compiled or slow path)

  CgElimCase* = object
    contractum*: Term  # contractum template; context [ctor vars, elim vars]
    ctorArity*: int   # number of constructor args (params excluded); -1 if unknown

  CgRef* = object
    name*: string
    case kind*: CgRefKind
    of cgkElim:
      nargs*: int
      nParams*: int
      cases*: Table[int, CgElimCase]  # ctor refId -> case
    of cgkDefn:
      compiledProc*: string  # "" = not compiled in this block
      piQuantities*: seq[Quantity]
    of cgkCtor:
      famRefId*: int  # Issue #330: the data family's refId when the
                      # constructor's result type is atomic; -1 otherwise.
                      # Lets the repr tier recognize int-mapped families'
                      # canonical constructors.
    else: discard

  CodegenCtx* = object
    refs*: Table[int, CgRef]
    baseDir*: string
    src*: string
    badElims*: Table[int, bool]   # elim refIds unusable (cycles, bad templates)
    usedElims*: Table[int, bool]  # elim refIds referenced by compiled code
    reps*: Table[int, HostRuntimeType]
      ## Issue #330 representation spec: type/family refId -> host runtime
      ## mapping from the block's runtimeType/runtimeVector/... declarations.
      ## The emitter consults this to compile bodies against host
      ## representations (seq, Option, opaque Nim types) instead of Values;
      ## definitions whose types have no entry keep the Phase 1 Value backend.
    reprProcs*: Table[int, tuple[name: string, arity: int]]
      ## Issue #330 repr tier: def refId -> (emitted proc name, int arity)
      ## for definitions compiled against host representations directly.
      ## Pre-assigned before compiling a body so recursion resolves.

proc cgName*(defName: string): string =
  ## The emitted proc name for a compiled definition.
  "eponymCompiled_" & defName

proc collectRefIds(t: Term, acc: var Table[int, bool])

proc validateBakedRefIds*(globals: Globals,
                          bakedIds: Table[int, string]) =
  ## Validate emitted integer literals (including constructor IDs used as
  ## eliminator dispatch labels) against the global names in the codegen
  ## context. `bakedIds` includes references and IDs embedded in
  ## non-reference positions such as `case` labels.
  var namesByRefId = initTable[int, string]()
  for name, entry in globals.pairs:
    if entry.tm != nil and entry.tm.kind == tR:
      namesByRefId[entry.tm.refId] = name
  for refId, expectedName in bakedIds.pairs:
    let actualName = namesByRefId.getOrDefault(refId, "")
    if actualName != expectedName:
      raise newException(CgUnsupported,
        "baked refId " & $refId & " expected global '" & expectedName &
        "' but resolves to '" & actualName & "'")

proc elimProcName*(elimName: string): string =
  ## The emitted proc name for a compiled eliminator.
  "eponymElim_" & elimName

proc countPiBinders(ty: Term): int =
  ## Count the syntactic Pi binders of a (zonked) type. Constructor spines at
  ## runtime carry one argument per binder (implicits are inserted by
  ## elaboration, q0 binders survive erasure as unit), so this is the
  ## constructor's runtime arity.
  var t = ty
  while t != nil and t.kind == tPi:
    inc result
    t = t.scope.bdy

proc piQuantities(ty: Term): seq[Quantity] =
  ## Quantities of a checked Pi telescope, outermost first.
  var t = ty
  while t != nil and t.kind == tPi:
    result.add(t.qty)
    t = t.scope.bdy

proc familyRefIdOf(ctorTy: Term): int =
  ## The data family's refId from a constructor's type: walk the Pi
  ## telescope to the result type, then through the family application
  ## spine to its head; the head refId when atomic, else -1. (Issue
  ## #330 v3: `nil : Pi (A : Type 0). Vec A zero` and
  ## `none : Pi (A : Type 0). Option A` have application-headed results.)
  var t = ctorTy
  while t != nil and t.kind == tPi:
    t = t.scope.bdy
  while t != nil and t.kind == tApp:
    t = t.fn
  if t != nil and t.kind == tR: t.refId else: -1

proc buildCodegenCtx*(globals: Globals, baseDir, src: string,
                     runtimeTypes: seq[HostRuntimeType] = @[]): CodegenCtx =
  ## Resolve every global reference to its codegen treatment. `runtimeTypes`
  ## is the block's codec mapping (issue #330 representation spec); each
  ## named Eponym type/family resolves to its refId for emitter lookup.
  result = CodegenCtx(refs: initTable[int, CgRef](), baseDir: baseDir,
    src: src, badElims: initTable[int, bool](),
    usedElims: initTable[int, bool](),
    reps: initTable[int, HostRuntimeType](),
    reprProcs: initTable[int, tuple[name: string, arity: int]]())
  var refIdToName = initTable[int, string]()
  for name, e in globals.pairs:
    if e.tm != nil and e.tm.kind == tR:
      refIdToName[e.tm.refId] = name
  for mapping in runtimeTypes:
    if mapping.eponymName in globals:
      let e = globals[mapping.eponymName]
      if e.tm != nil and e.tm.kind == tR:
        result.reps[e.tm.refId] = mapping
  for name, e in globals.pairs:
    if e.tm == nil or e.tm.kind != tR:
      continue
    let refId = e.tm.refId
    if e.isElim and e.tm.refVal != nil and
        e.tm.refVal.whnf.kind == wRed:
      let rule = e.tm.refVal.whnf.rule
      var cases = initTable[int, CgElimCase]()
      for ctorId, tmpl in rule.cases.pairs:
        var arity = -1
        let ctorName = refIdToName.getOrDefault(ctorId, "")
        if ctorName in globals and globals[ctorName].ty != nil:
          arity = countPiBinders(globals[ctorName].ty) - rule.nParams
        cases[ctorId] = CgElimCase(contractum: tmpl, ctorArity: arity)
      result.refs[refId] = CgRef(name: name, kind: cgkElim,
        nargs: rule.nargs, nParams: rule.nParams, cases: cases)
    elif e.isDataConstructor:
      var fam = -1
      if name in globals and globals[name].ty != nil:
        fam = familyRefIdOf(globals[name].ty)
      result.refs[refId] = CgRef(name: name, kind: cgkCtor, famRefId: fam)
    elif e.tm.refIsDefn:
      result.refs[refId] = CgRef(name: name, kind: cgkDefn,
        compiledProc: "", piQuantities: piQuantities(e.ty))
    else:
      result.refs[refId] = CgRef(name: name, kind: cgkPostulate)

proc constLit(c: Const): NimNode =
  ## Enum field (not `$c`, which renders display strings like "?").
  let field = case c
    of cStar: "cStar"
    of cOne: "cOne"
    of cVoid: "cVoid"
    of cZero: "cZero"
  newDotExpr(bindSym"Const", ident(field))

proc qtyLit(q: Quantity): NimNode =
  newDotExpr(bindSym"Quantity", ident($q))

proc primOpLit(op: PrimOp): NimNode =
  newDotExpr(bindSym"PrimOp", ident($op))

proc bracketOf(items: seq[NimNode]): NimNode =
  ## `@[items...]` as AST.
  var bracket = newNimNode(nnkBracket)
  for it in items: bracket.add(it)
  newTree(nnkPrefix, ident"@", bracket)

proc cg(ctx: var CodegenCtx, t: Term, env: seq[NimNode],
        bnd: NimNode): NimNode  # forward

proc cgLambda(psym, bodyCode: NimNode): NimNode =
  ## `proc (psym: Value): Value = bodyCode`, via quote so the irregular
  ## nnkLambda shape stays the compiler's problem. Captures outer syms
  ## (verified: nested capture coerces to the {.closure.} parameter type).
  quote do:
    proc (`psym`: Value): Value = `bodyCode`

proc cgNullaryLambda(bodyCode: NimNode): NimNode =
  ## `proc (): Value = bodyCode` for generated q0 closures.
  quote do:
    proc (): Value = `bodyCode`

proc cgAppChain(ctx: var CodegenCtx, t: Term, env: seq[NimNode],
                bnd: NimNode): NimNode =
  ## Compile `tApp` chains. Everything folds through `vCompiledAppWithBindings`
  ## (preserving the interpreter's evaluation order exactly) except
  ## fully-applied eliminators, which become calls to the eliminator's
  ## generated proc (itself a static case dispatch).
  var argTerms: seq[Term] = @[]
  var head = t
  while head.kind == tApp:
    argTerms.add(head.arg)
    head = head.fn
  var appArgs: seq[Term] = @[]
  for i in countdown(argTerms.high, 0):
    appArgs.add(argTerms[i])
  if head.kind == tR and head.refId in ctx.refs:
    let r = ctx.refs[head.refId]
    if r.kind == cgkElim:
      if head.refId in ctx.badElims:
        raise newException(CgUnsupported,
          "eliminator '" & r.name & "' is not compilable")
      if appArgs.len != r.nargs:
        raise newException(CgUnsupported,
          "eliminator '" & r.name & "' applied to " & $appArgs.len &
          " args, needs " & $r.nargs & " (partial application falls back)")
      ctx.usedElims[head.refId] = true
      var argCodes: seq[NimNode] = @[]
      for a in appArgs:
        argCodes.add(cg(ctx, a, env, bnd))
      return newCall(ident(elimProcName(r.name)), bracketOf(argCodes), bnd)
  # Uniform fold: evaluate the head, then each argument left to right,
  # applying as we go — exactly the interpreter's order.
  var acc = cg(ctx, head, env, bnd)
  for a in appArgs:
    acc = newCall(bindSym"vCompiledAppWithBindings", acc, cg(ctx, a, env, bnd), bnd)
  acc

proc cg(ctx: var CodegenCtx, t: Term, env: seq[NimNode],
        bnd: NimNode): NimNode =
  if t.isNil:
    raise newException(CgUnsupported, "nil term")
  case t.kind
  of tV:
    if t.idx < 0 or t.idx >= env.len:
      raise newException(CgUnsupported,
        "de Bruijn index " & $t.idx & " out of range")
    env[t.idx]
  of tR:
    if t.refId notin ctx.refs:
      raise newException(CgUnsupported,
        "reference id " & $t.refId & " not in codegen scope")
    let r = ctx.refs[t.refId]
    case r.kind
    of cgkPostulate, cgkCtor:
      newCall(bindSym"postulateValue", newLit(t.refId), bnd)
    of cgkElim:
      raise newException(CgUnsupported,
        "bare eliminator reference '" & r.name & "' (not fully applied)")
    of cgkDefn:
      if r.compiledProc.len > 0:
        # The definition's value: the compiled proc applied to no args.
        # Callers apply arguments themselves via the fold, preserving the
        # interpreter's head-before-args evaluation order.
        newCall(ident(r.compiledProc), bracketOf(@[]), bnd)
      else:
        # Slow path: the definition's value from the runtime globals,
        # mirroring evalWhnf's tR/defn case (resolved by refId, so synthetic
        # definitions like record projections resolve too). Callers apply
        # arguments themselves via the fold, preserving the interpreter's
        # head-before-args evaluation order.
        newCall(bindSym"defnValue",
          newLit(ctx.baseDir), newLit(ctx.src), newLit(t.refId), bnd)
  of tC:
    case t.c
    of cVoid: newCall(bindSym"unitValue")
    of cStar: newCall(bindSym"vStar")
    else: newCall(bindSym"constValue", constLit(t.c))
  of tInt: newCall(bindSym"vInt", newLit(t.intVal))
  of tNatLit: newCall(bindSym"vNatLit", newLit(t.natLitVal))
  of tNatSing: newCall(bindSym"natSingValue", newLit(t.natSingVal))
  of tType: newCall(bindSym"vType", newLit(t.lvl))
  of tPrim:
    # primTy is never read at runtime (only stored in syn); pass a dummy
    # type term rather than evaluating the annotation.
    newCall(bindSym"vPrim", primOpLit(t.primOp),
      newCall(bindSym"tmC", constLit(cStar)))
  of tPi, tSi:
    let psym = genSym(nskParam, "cgTyArg")
    let domCode = cg(ctx, t.dom, env, bnd)
    let bodyCode = cg(ctx, t.scope.bdy, @[psym] & env, bnd)
    let maker = if t.kind == tPi: bindSym"piValue" else: bindSym"siValue"
    newCall(maker, domCode, newLit(t.scope.adv), qtyLit(t.qty),
      cgLambda(psym, bodyCode))
  of tLam:
    if t.qty == q0:
      # q0 binders carry type-level/witness information but no runtime value.
      # Keep a placeholder in the compiler's de Bruijn environment so outer
      # variables retain their indices, while emitting an actually nullary
      # host closure. Erasure guarantees that no computational occurrence of
      # this binder survives into `bodyCode`.
      let bodyCode = cg(ctx, t.scope.bdy,
        @[newCall(bindSym"unitValue")] & env, bnd)
      newCall(bindSym"vHostFunc0", cgNullaryLambda(bodyCode),
        newLit(t.scope.adv))
    else:
      let psym = genSym(nskParam, "cgLamArg")
      let bodyCode = cg(ctx, t.scope.bdy, @[psym] & env, bnd)
      newCall(bindSym"vHostFunc", cgLambda(psym, bodyCode))
  of tPair:
    newCall(bindSym"pairValue",
      cg(ctx, t.pFst, env, bnd), cg(ctx, t.pSnd, env, bnd))
  of tFst: newCall(bindSym"fstValue", cg(ctx, t.sub, env, bnd))
  of tSnd: newCall(bindSym"sndValue", cg(ctx, t.sub, env, bnd))
  of tAbsurd: newCall(bindSym"absurdValue", cg(ctx, t.sub, env, bnd))
  of tApp: cgAppChain(ctx, t, env, bnd)
  of tLet:
    let vsym = genSym(nskLet, "cgLet")
    let vcode = cg(ctx, t.letVal, env, bnd)
    let bcode = cg(ctx, t.letScope.bdy, @[vsym] & env, bnd)
    var blk = newNimNode(nnkBlockStmt)
    blk.add(newEmptyNode())
    var stmts = newStmtList()
    stmts.add(newLetStmt(vsym, vcode))
    stmts.add(bcode)
    blk.add(stmts)
    blk
  of tMeta:
    raise newException(CgUnsupported,
      "unresolved metavariable ?m" & $t.metaId)

proc collectRefIds(t: Term, acc: var Table[int, bool]) =
  ## Collect every `tR` refId occurring in `t` (through binders).
  if t.isNil: return
  case t.kind
  of tR:
    acc[t.refId] = true
  of tPi, tSi, tLam:
    collectRefIds(t.dom, acc)
    collectRefIds(t.scope.bdy, acc)
  of tPair:
    collectRefIds(t.pFst, acc)
    collectRefIds(t.pSnd, acc)
  of tApp:
    collectRefIds(t.fn, acc)
    collectRefIds(t.arg, acc)
  of tFst, tSnd, tAbsurd:
    collectRefIds(t.sub, acc)
  of tLet:
    collectRefIds(t.letVal, acc)
    collectRefIds(t.letTy, acc)
    collectRefIds(t.letScope.bdy, acc)
  of tPrim:
    collectRefIds(t.primTy, acc)
  else: discard

proc collectReferencedRefIds*(t: Term): seq[int] =
  ## Return the reference IDs used by a checked term, including under binders.
  var ids = initTable[int, bool]()
  collectRefIds(t, ids)
  for id in ids.keys:
    result.add(id)

proc elimDispatchCase(procNode: NimNode): NimNode =
  ## Find the generated case over a scrutinee's constructor refId.
  if procNode.isNil: return nil
  if procNode.kind == nnkCaseStmt and procNode.len > 0 and
      procNode[0].kind == nnkCall and procNode[0].len > 0 and
      $procNode[0][0] == "whnfRefId":
    return procNode
  for child in procNode:
    result = elimDispatchCase(child)
    if not result.isNil: return

proc countCallsNamed(node: NimNode, name: string): int =
  if node.isNil: return 0
  if node.kind in {nnkCall, nnkCommand, nnkCallStrLit} and node.len > 0 and
      $node[0] == name:
    inc result
  for child in node:
    result += countCallsNamed(child, name)

proc containsIntLiteral(node: NimNode, value: int): bool =
  if node.isNil: return false
  if node.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
      nnkInt64Lit} and node.intVal == value:
    return true
  for child in node:
    if containsIntLiteral(child, value): return true

proc collectSpineKindIndices(node: NimNode, indices: var seq[int]) =
  if node.isNil: return
  if node.kind == nnkCall and node.len == 3 and $node[0] == "whnfSpineKind" and
      node[2].kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                       nnkInt64Lit}:
    indices.add(node[2].intVal.int)
  for child in node:
    collectSpineKindIndices(child, indices)

proc containsCallNamed(node: NimNode, name: string): bool =
  countCallsNamed(node, name) > 0

proc countIdentsNamed(node: NimNode, name: string): int =
  if node.isNil: return 0
  if node.kind in {nnkIdent, nnkSym} and $node == name:
    inc result
  for child in node:
    result += countIdentsNamed(child, name)

proc validateCtorBranchShape(r: CgRef, ctorId: int,
                             cs: CgElimCase, branch: NimNode) =
  ## The generated branch must reject malformed constructor spines as stuck
  ## eliminators instead of indexing past the runtime spine.
  var guard: NimNode
  proc findGuard(node: NimNode) =
    if node.isNil or not guard.isNil: return
    if node.kind == nnkIfExpr and node.len >= 2 and
        node[0].kind == nnkElifBranch:
      let cond = node[0][0]
      if containsCallNamed(cond, "whnfSpineLen"):
        guard = node
        return
    for child in node:
      findGuard(child)
  findGuard(branch)
  if guard.isNil:
    raise newException(CgUnsupported,
      "compiled eliminator '" & r.name & "' constructor refId " & $ctorId &
      " has no spine-shape guard")
  let cond = guard[0][0]
  let total = r.nParams + cs.ctorArity
  if not containsIntLiteral(cond, total):
    raise newException(CgUnsupported,
      "compiled eliminator '" & r.name & "' constructor refId " & $ctorId &
      " does not check its expected spine length")
  var indices: seq[int] = @[]
  collectSpineKindIndices(cond, indices)
  indices.sort()
  if indices.len != cs.ctorArity:
    raise newException(CgUnsupported,
      "compiled eliminator '" & r.name & "' constructor refId " & $ctorId &
      " does not check every constructor argument")
  for i, actual in indices:
    if actual != r.nParams + i:
      raise newException(CgUnsupported,
        "compiled eliminator '" & r.name & "' constructor refId " & $ctorId &
        " checks the wrong constructor-spine position")
  if countIdentsNamed(cond, "eApp") != cs.ctorArity:
    raise newException(CgUnsupported,
      "compiled eliminator '" & r.name & "' constructor refId " & $ctorId &
      " does not require application eliminations for its constructor arguments")
  if guard.len < 2 or guard[1].kind != nnkElse or
      not containsCallNamed(guard[1], "stuckElim"):
    raise newException(CgUnsupported,
      "compiled eliminator '" & r.name & "' constructor refId " & $ctorId &
      " does not preserve malformed spines as stuck eliminators")

proc validateElimDispatchCoverage*(r: CgRef, procNode: NimNode) =
  ## Translation validation: the generated constructor-tag dispatch must
  ## have exactly one branch for every kernel-validated reduction rule, plus
  ## a default branch for unknown constructors. Every branch must also guard
  ## the expected spine shape and preserve malformed spines as stuck values.
  ## This checks the emitted AST, not only the source loop that constructs it.
  if r.kind != cgkElim:
    raise newException(CgUnsupported,
      "dispatch validation requested for non-eliminator '" & r.name & "'")
  let dispatch = elimDispatchCase(procNode)
  if dispatch.isNil:
    raise newException(CgUnsupported,
      "compiled eliminator '" & r.name & "' has no constructor dispatch")
  var expected = initTable[int, CgElimCase]()
  for ctorId in r.cases.keys:
    expected[ctorId] = r.cases[ctorId]
  var actual = initTable[int, bool]()
  var hasDefault = false
  for i in 1 ..< dispatch.len:
    let branch = dispatch[i]
    case branch.kind
    of nnkOfBranch:
      if branch.len < 2 or branch[0].kind notin {
          nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit}:
        raise newException(CgUnsupported,
          "compiled eliminator '" & r.name &
          "' has a non-literal constructor dispatch label")
      let ctorId = branch[0].intVal.int
      if ctorId notin expected:
        raise newException(CgUnsupported,
          "compiled eliminator '" & r.name & "' dispatches unregistered " &
          "constructor refId " & $ctorId)
      if ctorId in actual:
        raise newException(CgUnsupported,
          "compiled eliminator '" & r.name & "' dispatches constructor refId " &
          $ctorId & " more than once")
      validateCtorBranchShape(r, ctorId, expected[ctorId], branch[1])
      actual[ctorId] = true
    of nnkElse:
      if hasDefault:
        raise newException(CgUnsupported,
          "compiled eliminator '" & r.name & "' has duplicate default branches")
      hasDefault = true
    else:
      raise newException(CgUnsupported,
        "compiled eliminator '" & r.name & "' has an unexpected dispatch branch")
  for ctorId in expected.keys:
    if ctorId notin actual:
      raise newException(CgUnsupported,
        "compiled eliminator '" & r.name &
        "' dispatch does not cover registered constructor refId " & $ctorId)
  if not hasDefault:
    raise newException(CgUnsupported,
      "compiled eliminator '" & r.name & "' has no default dispatch branch")

proc detectBadElims(ctx: var CodegenCtx) =
  ## Mark eliminators that cannot be compiled: those in reference cycles,
  ## with unknown constructor arities, or whose contractum templates fall
  ## outside the fragment. Runs before any definition is compiled, so a
  ## failing eliminator can never strand an already-compiled caller.
  # 1. reference cycles among eliminators (through templates)
  var elimDeps = initTable[int, Table[int, bool]]()
  for refId, r in ctx.refs.pairs:
    if r.kind != cgkElim: continue
    var acc = initTable[int, bool]()
    for _, cs in r.cases.pairs:
      var ids = initTable[int, bool]()
      collectRefIds(cs.contractum, ids)
      for id in ids.keys:
        if id != refId and id in ctx.refs and
            ctx.refs[id].kind == cgkElim:
          acc[id] = true
    elimDeps[refId] = acc
  var emitted = initTable[int, bool]()
  var progress = true
  while progress:
    progress = false
    for refId, deps in elimDeps.pairs:
      if emitted.getOrDefault(refId, false): continue
      var ready = true
      for dep in deps.keys:
        if dep in elimDeps and not emitted.getOrDefault(dep, false):
          ready = false
          break
      if ready:
        emitted[refId] = true
        progress = true
  for refId in elimDeps.keys:
    if not emitted.getOrDefault(refId, false):
      ctx.badElims[refId] = true
  # 2. dry-run every template; anything outside the fragment marks the elim.
  #    Iterated: a template referencing a newly-bad eliminator is bad too.
  var changed = true
  while changed:
    changed = false
    for refId, r in ctx.refs.pairs:
      if r.kind != cgkElim or refId in ctx.badElims: continue
      var dryCtx = CodegenCtx(refs: ctx.refs, baseDir: "", src: "",
        badElims: ctx.badElims, usedElims: initTable[int, bool](),
        reps: ctx.reps,
        reprProcs: initTable[int, tuple[name: string, arity: int]]())
      try:
        for _, cs in r.cases.pairs:
          if cs.ctorArity < 0:
            raise newException(CgUnsupported, "unknown constructor arity")
          var tmplEnv: seq[NimNode] = @[]
          for j in 0 ..< cs.ctorArity + r.nargs - 1:
            tmplEnv.add(genSym(nskLet, "cgDry"))
          discard cg(dryCtx, cs.contractum, tmplEnv,
            genSym(nskParam, "cgDryBnd"))
      except CgUnsupported:
        ctx.badElims[refId] = true
        changed = true

proc compileElimProc(ctx: var CodegenCtx, elimRefId: int): NimNode =
  ## Generate `eponymElim_<name>`: static case dispatch over the registered
  ## reduction rules, mirroring `fireRed`. `args` are the elim arguments in
  ## application order, last = scrutinee.
  let r = ctx.refs[elimRefId]
  let argsSym = ident"cgProcArgs"
  let bndSym = ident"cgProcBindings"
  var formal = newNimNode(nnkFormalParams)
  formal.add(bindSym"Value")
  formal.add(newIdentDefs(argsSym,
    newTree(nnkBracketExpr, ident"seq", bindSym"Value"), newEmptyNode()))
  formal.add(newIdentDefs(bndSym, bindSym"RuntimeBindings", newEmptyNode()))
  var procNode = newNimNode(nnkProcDef)
  procNode.add(newTree(nnkPostfix, ident"*", ident(elimProcName(r.name))))
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  procNode.add(formal)
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  var lets = newStmtList()
  var argSyms: seq[NimNode] = @[]
  for i in 0 ..< r.nargs:
    let s = genSym(nskLet, "cgElimArg")
    argSyms.add(s)
    lets.add(newLetStmt(s, newTree(nnkBracketExpr, argsSym, newLit(i))))
  let ss = argSyms[^1]
  let elimArgSyms = argSyms[0 ..< argSyms.high]
  let stuckCall = newCall(bindSym"stuckElim", newLit(elimRefId),
    bracketOf(argSyms))
  var innerCase = newNimNode(nnkCaseStmt)
  innerCase.add(newCall(bindSym"whnfRefId", ss))
  for ctorId, cs in r.cases.pairs:
    # (arity was validated by detectBadElims)
    let m = cs.ctorArity
    let total = r.nParams + m
    var cond = newCall(bindSym"==",
      newCall(bindSym"whnfSpineLen", ss), newLit(total))
    for i in r.nParams ..< total:
      cond = newTree(nnkInfix, ident"and", cond,
        newCall(bindSym"==",
          newCall(bindSym"whnfSpineKind", ss, newLit(i)),
          newDotExpr(bindSym"ElimVKind", ident"eApp")))
    var tmplEnv: seq[NimNode] = @[]
    for j in 0 ..< m:
      tmplEnv.add(newCall(bindSym"whnfSpineArg", ss,
        newLit(r.nParams + m - 1 - j)))
    for j in 0 ..< elimArgSyms.len:
      tmplEnv.add(elimArgSyms[elimArgSyms.high - j])
    let tmplCode = cg(ctx, cs.contractum, tmplEnv, bndSym)
    var branch = newNimNode(nnkOfBranch)
    branch.add(newLit(ctorId))
    branch.add(newTree(nnkStmtList,
      newTree(nnkIfExpr,
        newTree(nnkElifBranch, cond, tmplCode),
        newTree(nnkElse, stuckCall))))
    innerCase.add(branch)
  var innerElse = newNimNode(nnkElse)
  innerElse.add(newTree(nnkStmtList, stuckCall))
  innerCase.add(innerElse)
  var outerCase = newNimNode(nnkCaseStmt)
  outerCase.add(newCall(bindSym"whnfKind", ss))
  var wRefBranch = newNimNode(nnkOfBranch)
  wRefBranch.add(newDotExpr(bindSym"WhnfKind", ident"wRef"))
  wRefBranch.add(newTree(nnkStmtList, innerCase))
  outerCase.add(wRefBranch)
  var outerElse = newNimNode(nnkElse)
  outerElse.add(newTree(nnkStmtList, stuckCall))
  outerCase.add(outerElse)
  lets.add(outerCase)
  procNode.add(lets)
  validateElimDispatchCoverage(r, procNode)
  procNode

proc compileDefProcWithReason*(d: ElabDef, ctx: var CodegenCtx,
                     locFile: string, locLine: int,
                     failureReason: var string): NimNode =
  ## Compile one definition to `proc eponymCompiled_<name>(args: seq[Value],
  ## bindings: RuntimeBindings, q0Args: seq[Value]): Value`. Returns nil when the definition is
  ## outside the supported fragment (caller keeps the interpreter wrapper).
  ##
  ## The emitted proc computes the definition's value with direct code, then
  ## applies runtime Pi arguments from `args` and q0 witnesses from `q0Args`.
  ## q0 values stay separate from the computational argument vector, while
  ## remaining available to instantiate dependent runtime types.
  ## As `compileDefProc`, and report why the definition did not compile.
  if d.tmTm.isNil:
    failureReason = "definition has no checked body"
    return nil
  let erased =
    try: eraseQ0Arguments(d.tmTm)
    except ValueError as e:
      failureReason = "quantity erasure failed: " & e.msg
      return nil
  let argsSym = ident"cgProcArgs"
  let bndSym = ident"cgProcBindings"
  let q0ArgsSym = ident"cgProcQ0Args"
  var formal = newNimNode(nnkFormalParams)
  formal.add(bindSym"Value")
  formal.add(newIdentDefs(argsSym,
    newTree(nnkBracketExpr, ident"seq", bindSym"Value"), newEmptyNode()))
  formal.add(newIdentDefs(bndSym, bindSym"RuntimeBindings", newEmptyNode()))
  formal.add(newIdentDefs(q0ArgsSym,
    newTree(nnkBracketExpr, ident"seq", bindSym"Value"),
    newTree(nnkPrefix, ident"@", newNimNode(nnkBracket))))
  var procNode = newNimNode(nnkProcDef)
  procNode.add(newTree(nnkPostfix, ident"*", ident(cgName(d.name))))
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  procNode.add(formal)
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  let accSym = genSym(nskVar, "cgAcc")
  let argIdxSym = genSym(nskVar, "cgArgIdx")
  let q0ArgIdxSym = genSym(nskVar, "cgQ0ArgIdx")
  let canBindSym = genSym(nskVar, "cgCanBind")
  let bodyCode =
    try: cg(ctx, erased, @[], bndSym)
    except CgUnsupported as e:
      failureReason = e.msg
      return nil
  var inner = newStmtList()
  inner.add(newVarStmt(accSym, bodyCode))
  inner.add(newVarStmt(argIdxSym, newLit(0)))
  inner.add(newVarStmt(q0ArgIdxSym, newLit(0)))
  inner.add(newVarStmt(canBindSym, newLit(true)))
  for qty in piQuantities(d.tyTm):
    var bindStmts = newStmtList()
    if qty == q0:
      let q0Witness = genSym(nskLet, "cgQ0Witness")
      let hasQ0Witness = newTree(nnkInfix, ident"<", q0ArgIdxSym,
        newCall(bindSym"len", q0ArgsSym))
      bindStmts.add(newLetStmt(q0Witness,
        newTree(nnkIfExpr,
          newTree(nnkElifBranch, hasQ0Witness,
            newTree(nnkBracketExpr, q0ArgsSym, q0ArgIdxSym)),
          newTree(nnkElse, newCall(bindSym"unitValue")))))
      bindStmts.add(newAssignment(accSym,
        newCall(bindSym"vCompiledAppWithBindings", accSym,
          q0Witness, bndSym)))
      bindStmts.add(newCall(bindSym"inc", q0ArgIdxSym))
    else:
      bindStmts.add(newAssignment(accSym,
        newCall(bindSym"vCompiledAppWithBindings", accSym,
          newTree(nnkBracketExpr, argsSym, argIdxSym), bndSym)))
      bindStmts.add(newCall(bindSym"inc", argIdxSym))
    let cond = if qty == q0:
      canBindSym
    else:
      newTree(nnkInfix, ident"and", canBindSym,
        newTree(nnkInfix, ident"<", argIdxSym,
          newCall(bindSym"len", argsSym)))
    var branches = newNimNode(nnkIfStmt)
    branches.add(newTree(nnkElifBranch, cond, bindStmts))
    if qty != q0:
      branches.add(newTree(nnkElse, newStmtList(
        newAssignment(canBindSym, newLit(false)))))
    inner.add(branches)
  let restSym = genSym(nskForVar, "cgExtraArgIdx")
  inner.add(newTree(nnkForStmt, restSym,
    newTree(nnkInfix, ident"..<", argIdxSym, newCall(bindSym"len", argsSym)),
    newStmtList(newAssignment(accSym,
      newCall(bindSym"vCompiledAppWithBindings", accSym,
        newTree(nnkBracketExpr, argsSym, restSym), bndSym)))))
  inner.add(accSym)
  # Source positions (issue #329 acceptance): runtime errors raised while
  # evaluating compiled code report the definition's source location.
  # locLine is the definition's line in the user's file (not the
  # elaborator's string-relative loc).
  procNode.setLineInfo(LineInfo(filename: locFile, line: locLine, column: 0))
  procNode.add(inner)
  procNode

proc compileDefProc*(d: ElabDef, ctx: var CodegenCtx,
                     locFile: string, locLine: int): NimNode =
  ## Compatibility entrypoint for callers that do not need fallback details.
  var ignoredReason = ""
  compileDefProcWithReason(d, ctx, locFile, locLine, ignoredReason)

# ---------------------------------------------------------------------------
# Issue #330: representation-specialized tier.
#
# Definitions whose entire signature maps to plain host representations are
# compiled to procs that operate on those representations directly — no
# `Value` allocation, no interpreter dispatch, so Nim's optimizer sees real
# code. The typed wrapper calls the repr proc with the host arguments as-is
# (the boundary conversion becomes the identity); definitions outside the
# fragment keep the Phase 1 Value backend.
#
# v1 closed fragment: Eponym types mapped to Nim `int` via plain
# `runtimeType` (covers `Int` and its `tPrim` arithmetic).
# v2 adds `Nat` and `Bool` as `int`: `tNatLit` literals, the canonical
# constructors (`zero`/`suc`, `true`/`false`) as int literals/arithmetic,
# and match-compiled eliminators (`natElim` as an iterative fold,
# `boolElim` as a conditional).
# v3 adds `Vec`/`List` as `seq[int]` and `Option` as `Option[int]`:
# the canonical constructors (`nil`/`cons`, `none`/`some`) build host
# collections, and match-compiled eliminators (`vecElim`/`listElim` as
# folds, `optionElim` as a conditional) consume them. Element types must
# themselves be in the int fragment; anything else falls back to Phase 1.
# ---------------------------------------------------------------------------

proc cgReprName*(defName: string): string =
  ## The emitted proc name for a representation-specialized definition.
  "eponymCompiledRepr_" & defName

type
  ReprKind* = enum
    repInt  # Eponym type mapped to Nim `int` via plain runtimeType
    repSeq  # `Vec`/`List` family mapped to Nim `seq[int]`
    repOption  # `Option` family mapped to Nim `Option[int]`

  ReprType* = object
    ## The host representation of one signature position (a non-q0
    ## binder domain or the result type).
    kind*: ReprKind
    isVector*: bool  # for repSeq: from runtimeVector (length-indexed)
    index*: Term  # for repSeq+isVector: the length index term

proc isPlainIntMapping*(m: HostRuntimeType): bool =
  ## True when the mapping is a plain `runtimeType ... -> int` (not a
  ## vector/list/option/variant/codec mapping): the host representation
  ## is exactly Nim `int` with the identity boundary conversion.
  not m.isRuntimeVector and not m.isRuntimeList and
    not m.isRuntimeOption and not m.isRuntimeVariant and
    not m.isRuntimeCodec and
    m.nimType.kind in {nnkIdent, nnkSym} and $m.nimType == "int"

proc reprKindOf(ctx: CodegenCtx, refId: int): ReprKind =
  ## The representation kind for a type/family refId. Raises CgUnsupported
  ## when the mapping is absent or outside the fragment.
  if refId notin ctx.reps:
    raise newException(CgUnsupported,
      "type has no runtime representation mapping")
  let m = ctx.reps[refId]
  if m.isPlainIntMapping:
    return repInt
  if m.isRuntimeVector or m.isRuntimeList:
    return repSeq
  if m.isRuntimeOption:
    return repOption
  raise newException(CgUnsupported,
    "runtime representation outside the fragment")

proc checkIntElem(ctx: CodegenCtx, t: Term) =
  ## v3 scope: collection element types must be in the int fragment.
  if t.isNil or t.kind != tR or ctx.reprKindOf(t.refId) != repInt:
    raise newException(CgUnsupported,
      "collection element type outside the int fragment")

proc reprTypeOf(ctx: CodegenCtx, t: Term): ReprType =
  ## The host representation of a binder domain or result type: an atomic
  ## `tR` in the int fragment, or a fully-applied `Vec`/`List`/`Option`
  ## family over int elements. Raises CgUnsupported otherwise. The check
  ## is structural only: length-index terms are validated when compiled
  ## (entry check), never here.
  if t.isNil:
    raise newException(CgUnsupported, "nil type")
  if t.kind == tR:
    let k = ctx.reprKindOf(t.refId)
    if k != repInt:
      raise newException(CgUnsupported,
        "unapplied family outside the representation fragment")
    return ReprType(kind: repInt)
  if t.kind == tApp:
    var argTerms: seq[Term] = @[]
    var head = t
    while head.kind == tApp:
      argTerms.add(head.arg)
      head = head.fn
    var appArgs: seq[Term] = @[]
    for i in countdown(argTerms.high, 0):
      appArgs.add(argTerms[i])
    if head.kind != tR or head.refId notin ctx.reps:
      raise newException(CgUnsupported, "non-family type application")
    let m = ctx.reps[head.refId]
    if m.isRuntimeVector:
      # `Vec A n`: the family parameter then the length index. The
      # validators (validateHostVectorCodec) enforce this shape on
      # declared families, so an arity mismatch is a hard fallback.
      if appArgs.len != 2:
        raise newException(CgUnsupported,
          "Vec application has " & $appArgs.len & " args, needs 2")
      ctx.checkIntElem(appArgs[0])
      return ReprType(kind: repSeq, isVector: true, index: appArgs[1])
    if m.isRuntimeList:
      if appArgs.len != 1:
        raise newException(CgUnsupported,
          "List application has " & $appArgs.len & " args, needs 1")
      ctx.checkIntElem(appArgs[0])
      return ReprType(kind: repSeq, isVector: false)
    if m.isRuntimeOption:
      if appArgs.len != 1:
        raise newException(CgUnsupported,
          "Option application has " & $appArgs.len & " args, needs 1")
      ctx.checkIntElem(appArgs[0])
      return ReprType(kind: repOption)
    raise newException(CgUnsupported,
      "family outside the representation fragment")
  raise newException(CgUnsupported, "type outside the representation fragment")

proc nimReprType*(rt: ReprType): NimNode =
  ## The Nim type AST for one representation-typed signature position.
  case rt.kind
  of repInt: ident"int"
  of repSeq: newTree(nnkBracketExpr, ident"seq", ident"int")
  of repOption: newTree(nnkBracketExpr, ident"Option", ident"int")

proc reprTypeName*(rt: ReprType): string =
  ## The Nim type name for the wrapper identity-boundary check
  ## (issue #330 v3): `int`, `seq[int]`, or `Option[int]`.
  case rt.kind
  of repInt: "int"
  of repSeq: "seq[int]"
  of repOption: "Option[int]"

proc reprSig(ctx: CodegenCtx, d: ElabDef): seq[ReprType] =
  ## Representation types of the def's Pi-binder domains (outermost
  ## first), followed by the result type. Quantity-0 binders are erased
  ## from the host signature. Raises CgUnsupported when anything else is
  ## outside the fragment.
  var t = d.tyTm
  while t != nil and t.kind == tPi:
    if t.qty != q0:
      # Issue #386: a binder domain outside the representation fragment
      # keeps the established "non-atomic binder domain" diagnostic.
      try: result.add(ctx.reprTypeOf(t.dom))
      except CgUnsupported:
        raise newException(CgUnsupported, "non-atomic binder domain")
    t = t.scope.bdy
  result.add(ctx.reprTypeOf(t))

proc cgRepr(ctx: var CodegenCtx, t: Term, env: seq[NimNode]): NimNode  # forward
proc cgReprElim(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                env: seq[NimNode]): NimNode  # forward
proc cgReprCtor(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                env: seq[NimNode]): NimNode  # forward

proc cgReprApp(ctx: var CodegenCtx, t: Term, env: seq[NimNode]): NimNode =
  ## Compile a `tApp` chain in the repr tier. Primitive Int ops become direct
  ## Nim arithmetic (the interpreter fires them as `x + y` etc. on machine
  ## ints, so this is exactly sound); immediately-applied lambdas are
  ## beta-reduced to let-bindings (the fragment's lambdas never escape —
  ## see below); anything else is a direct call of a compiled head.
  var argTerms: seq[Term] = @[]
  var head = t
  while head.kind == tApp:
    argTerms.add(head.arg)
    head = head.fn
  var appArgs: seq[Term] = @[]
  for i in countdown(argTerms.high, 0):
    appArgs.add(argTerms[i])
  if head.kind == tPrim:
    # A repr-tier body only ever applies primops to ints (the signature
    # check admits only int-typed binders), so direct arithmetic is sound.
    if appArgs.len != 2:
      raise newException(CgUnsupported,
        "primitive op applied to " & $appArgs.len & " args, needs 2")
    let a = cgRepr(ctx, appArgs[0], env)
    let b = cgRepr(ctx, appArgs[1], env)
    let op = case head.primOp
      of opAdd: "+"
      of opSub: "-"
      of opMul: "*"
    return newTree(nnkInfix, ident(op), a, b)
  if head.kind == tR and head.refId in ctx.refs:
    let rh = ctx.refs[head.refId]
    if rh.kind == cgkElim:
      return cgReprElim(ctx, rh, appArgs, env)
    if rh.kind == cgkCtor:
      return cgReprCtor(ctx, rh, appArgs, env)
    if rh.kind == cgkDefn and head.refId in ctx.reprProcs:
      var args: seq[NimNode] = @[]
      var argIdx = 0
      for qty in rh.piQuantities:
        if argIdx >= appArgs.len: break
        if qty != q0:
          args.add(cgRepr(ctx, appArgs[argIdx], env))
        inc argIdx
      if argIdx != appArgs.len:
        raise newException(CgUnsupported,
          "compiled repr call to '" & rh.name & "' has mismatched arity")
      var call = newCall(ident(ctx.reprProcs[head.refId].name))
      for arg in args: call.add(arg)
      return call
  # Beta-reduce immediately-applied lambdas. A lambda in this fragment has
  # an int type only when fully applied (a bare lambda has a Pi type, which
  # the signature check rejects, and the only int-typed positions are
  # applied ones), so running out of binders or arguments is a hard error
  # that falls back to the Phase 1 backend. Arguments sit outside the
  # lambdas' scope, so each compiles under the original environment; only
  # the final body sees the bound parameters.
  var curEnv = env
  var argIdx = 0
  var preStmts = newStmtList()
  while head.kind == tLam:
    if argIdx >= appArgs.len:
      raise newException(CgUnsupported, "unapplied lambda in repr body")
    if head.qty == q0:
      curEnv = @[newLit(0)] & curEnv
    else:
      if head.dom.isNil:
        raise newException(CgUnsupported, "nil lambda domain")
      # The binder must denote a representation in the fragment; the
      # let-bound symbol's Nim type is inferred from the argument.
      # (Issue #386: the fallback report keeps the established
      # diagnostic for a non-representable binder domain.)
      try: discard ctx.reprTypeOf(head.dom)
      except CgUnsupported:
        raise newException(CgUnsupported, "non-atomic binder domain")
      let psym = genSym(nskLet, "cgReprBeta")
      preStmts.add(newLetStmt(psym, cgRepr(ctx, appArgs[argIdx], env)))
      curEnv = @[psym] & curEnv
    head = head.scope.bdy
    inc argIdx
  if argIdx > 0 and argIdx < appArgs.len and head.kind != tR:
    # The beta-reduced head is a first-order value, yet arguments remain:
    # over-applied. (A tR head is a defn reference and stays callable.)
    # Unreachable in well-typed bodies; falls back to the Phase 1 backend.
    raise newException(CgUnsupported, "over-applied lambda in repr body")
  let h = cgRepr(ctx, head, curEnv)
  var final: NimNode
  if argIdx < appArgs.len:
    var call = newCall(h)
    for i in argIdx ..< appArgs.len:
      call.add(cgRepr(ctx, appArgs[i], curEnv))
    final = call
  else:
    # All arguments were consumed by beta-reduced lambdas: the head is the
    # value. (argIdx > 0 here — cgReprApp only runs on tApp chains.)
    final = h
  if preStmts.len == 0:
    return final
  # Left-to-right evaluation order, matching the interpreter's head-then-
  # args application order: each argument is bound before the body runs.
  preStmts.add(final)
  var blk = newNimNode(nnkBlockStmt)
  blk.add(newEmptyNode())
  blk.add(preStmts)
  blk

proc checkElimCases(r: CgRef, elimName: string, arities: openArray[int],
                    nParams = 0) =
  ## Structural sanity for a match-compiled eliminator: the registered
  ## cases must be exactly the expected constructor arities (as a
  ## multiset), with the expected number of family parameters (index
  ## parameters excluded from the arities, as the Phase-1 backend does).
  ## Guards the name-based dispatch below against a same-named eliminator
  ## with a different shape.
  if r.nParams != nParams:
    raise newException(CgUnsupported, "eliminator '" & elimName &
      "' has " & $r.nParams & " parameters, expected " & $nParams)
  if r.cases.len != arities.len:
    raise newException(CgUnsupported, "eliminator '" & elimName &
      "' has " & $r.cases.len & " cases, expected " & $arities.len)
  var remaining = @arities
  for _, cs in r.cases.pairs:
    let i = remaining.find(cs.ctorArity)
    if i < 0:
      raise newException(CgUnsupported, "eliminator '" & elimName &
        "' has unexpected case arity " & $cs.ctorArity)
    remaining.del(i)

proc checkSeqElemArg(ctx: CodegenCtx, appArgs: seq[Term], elimName: string) =
  ## v3: the eliminator's family-parameter argument must be an int-mapped
  ## element type. It is never evaluated (a type argument), but the check
  ## pins the compiled loop to `seq[int]`/`Option[int]`.
  if appArgs.len == 0 or appArgs[0].isNil or appArgs[0].kind != tR or
      ctx.reprKindOf(appArgs[0].refId) != repInt:
    raise newException(CgUnsupported, "eliminator '" & elimName &
      "' element type outside the int fragment")

proc motiveCodomain(motive: Term): Term =
  ## Peel the motive's lambdas to its codomain type. A non-lambda motive
  ## falls back to the Phase-1 backend (the codomain kind cannot be
  ## established structurally).
  result = motive
  while not result.isNil and result.kind == tLam:
    result = result.scope.bdy

proc checkMotiveKind(ctx: CodegenCtx, r: CgRef, appArgs: seq[Term],
                     motiveIdx: int) =
  ## The eliminator's result must denote a representation in the fragment:
  ## establish it structurally from the motive's codomain, mirroring
  ## reprSig's result-type check on definitions.
  let cod = motiveCodomain(appArgs[motiveIdx])
  if cod.isNil:
    raise newException(CgUnsupported, "eliminator '" & r.name &
      "' has no motive codomain")
  discard ctx.reprTypeOf(cod)

proc termUsesInnerBinder(t: Term, nInner: int, depth: int = 0): bool =
  ## Scope-aware variable check for the #331 destination-passing fold:
  ## true iff `t` mentions a variable bound by one of the `nInner`
  ## innermost binders of `t`'s own scope (de Bruijn index, adjusted for
  ## binders traversed inside `t`, in `0 ..< nInner`).
  if t.isNil: return false
  case t.kind
  of tV:
    let rel = t.idx - depth
    return rel >= 0 and rel < nInner
  of tPi, tSi, tLam:
    return termUsesInnerBinder(t.dom, nInner, depth) or
           termUsesInnerBinder(t.scope.bdy, nInner, depth + 1)
  of tPair:
    return termUsesInnerBinder(t.pFst, nInner, depth) or
           termUsesInnerBinder(t.pSnd, nInner, depth) or
           termUsesInnerBinder(t.pScope.bdy, nInner, depth + 1)
  of tApp:
    return termUsesInnerBinder(t.fn, nInner, depth) or
           termUsesInnerBinder(t.arg, nInner, depth)
  of tFst, tSnd, tAbsurd:
    return termUsesInnerBinder(t.sub, nInner, depth)
  of tLet:
    return termUsesInnerBinder(t.letVal, nInner, depth) or
           termUsesInnerBinder(t.letTy, nInner, depth) or
           termUsesInnerBinder(t.letScope.bdy, nInner, depth + 1)
  of tMeta:
    for s in t.metaSpine:
      if termUsesInnerBinder(s, nInner, depth): return true
    return false
  of tPrim:
    return termUsesInnerBinder(t.primTy, nInner, depth)
  else:
    return false

proc dpsRebuildHead(ctx: CodegenCtx, body: Term, isVec: bool): Term =
  ## #331: recognize the cons-rebuild shape `cons A idx xHead ih` (Vec)
  ## or `cons A xHead ih` (List), where the tail is exactly the fold
  ## accumulator (`ih`, de Bruijn 0 in the cons-case scope) and the head
  ## mentions neither the accumulator nor the materialized tail (`tl`,
  ## de Bruijn 1). Returns the head term, or nil when the shape does not
  ## apply (the caller keeps the allocating fold).
  ##
  ## Soundness note: the destination-passing emission is valid for any
  ## `ih` quantity — the destination is freshly allocated and the initial
  ## accumulator is only read, never mutated — so, unlike the in-place
  ## refinements (#331 follow-up), this step is not gated on linearity.
  var fn = body
  var revArgs: seq[Term] = @[]
  while fn.kind == tApp:
    revArgs.add(fn.arg)
    fn = fn.fn
  if fn.kind != tR or fn.refId notin ctx.refs:
    return nil
  let rh = ctx.refs[fn.refId]
  if rh.kind != cgkCtor or rh.name != "cons" or
      rh.famRefId notin ctx.reps:
    return nil
  let m = ctx.reps[rh.famRefId]
  if isVec and not m.isRuntimeVector: return nil
  if not isVec and not m.isRuntimeList: return nil
  var appArgs: seq[Term] = @[]
  for i in countdown(revArgs.high, 0):
    appArgs.add(revArgs[i])
  let (xHead, tail) =
    if isVec:
      if appArgs.len != 4: return nil
      (appArgs[2], appArgs[3])
    else:
      if appArgs.len != 3: return nil
      (appArgs[1], appArgs[2])
  if tail.isNil or tail.kind != tV or tail.idx != 0:
    return nil
  if termUsesInnerBinder(xHead, 2):
    return nil
  xHead

proc cgDpsFoldBlock(xsCode, nilCode, headCode: NimNode,
                    kSym, xSym, iSym: NimNode): NimNode =
  ## #331 destination-passing fold over `xsCode` (a `seq[int]` expression):
  ## allocate one destination of `xs.len + acc0.len`, copy the initial
  ## accumulator into its tail, then fill positions `k` — right-to-left in
  ## time, left-to-right in space — with `headCode`. `headCode` may mention
  ## `xSym` (bound per iteration to `xs[k]`) and, for Vec, `iSym` (bound to
  ## `len-1-k`); `iSym` is nil for List. One allocation and O(n) element
  ## writes replace the per-step `@[x] & acc` allocation of the plain fold.
  let xsSym = genSym(nskLet, "cgDpsXs")
  let acc0Sym = genSym(nskLet, "cgDpsAcc0")
  let mSym = genSym(nskLet, "cgDpsM")
  let dstSym = genSym(nskVar, "cgDpsDst")
  let jSym = genSym(nskForVar, "cgDpsJ")
  var stmts = newStmtList()
  stmts.add(newLetStmt(xsSym, xsCode))
  stmts.add(newLetStmt(acc0Sym, nilCode))
  stmts.add(newLetStmt(mSym, newCall(bindSym"len", xsSym)))
  stmts.add(newVarStmt(dstSym,
    newTree(nnkCall,
      newTree(nnkBracketExpr, ident"newSeq", ident"int"),
      newTree(nnkInfix, ident"+", mSym,
        newCall(bindSym"len", acc0Sym)))))
  var copyBody = newStmtList()
  copyBody.add(newTree(nnkAsgn,
    newTree(nnkBracketExpr, dstSym,
      newTree(nnkInfix, ident"+", mSym, jSym)),
    newTree(nnkBracketExpr, acc0Sym, jSym)))
  stmts.add(newTree(nnkForStmt, jSym,
    newTree(nnkInfix, ident"..<",
      newLit(0), newCall(bindSym"len", acc0Sym)),
    copyBody))
  var loopBody = newStmtList()
  if not iSym.isNil:
    loopBody.add(newLetStmt(iSym,
      newTree(nnkInfix, ident"-",
        newTree(nnkInfix, ident"-", mSym, kSym),
        newLit(1))))
  loopBody.add(newLetStmt(xSym,
    newTree(nnkBracketExpr, xsSym, kSym)))
  loopBody.add(newTree(nnkAsgn,
    newTree(nnkBracketExpr, dstSym, kSym), headCode))
  stmts.add(newTree(nnkForStmt, kSym,
    newCall(ident"countdown",
      newTree(nnkInfix, ident"-", mSym, newLit(1)),
      newLit(0)),
    loopBody))
  stmts.add(dstSym)
  var blk = newNimNode(nnkBlockStmt)
  blk.add(newEmptyNode())
  blk.add(stmts)
  blk

proc cgReprListElim(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                    env: seq[NimNode]): NimNode =
  ## `listElim A motive nilC consC xs` over the `seq[int]` representation,
  ## compiled to a right-to-left fold:
  ##   var acc = nilC
  ##   for k in countdown(xs.len-1, 0):
  ##     acc = consC(xs[k], xs[k+1..^1], acc)
  ##   acc
  ## Right-to-left: `listElim` is a right fold
  ## (`consC x0 tl0 (consC x1 tl1 ...)`), so a left-to-right loop would
  ## build the list backwards; this also matches the interpreter's
  ## inside-out evaluation order (deepest consC application first).
  ## The cons case must be a syntactic triple lambda
  ## `lam (x). lam (tl). lam (ih). body` with an int-representable element
  ## domain; the body is compiled with `x`, `tl`, `ih` bound to the head,
  ## the materialized tail, and the accumulator. The motive (appArgs[1])
  ## is a type family: skipped, as for `natElim`. The tail slice is O(n)
  ## per step; the #19-framed benchmark against Phase 1 says whether the
  ## unused-binder optimization is needed.
  ##
  ## #331 destination-passing: when the cons-case body is the cons-rebuild
  ## shape `cons A xHead ih` with the accumulator as the tail and the head
  ## not mentioning `ih`/`tl` (see `dpsRebuildHead`), the fold compiles to
  ## a single preallocated destination — one `newSeq`, O(n) writes —
  ## instead of per-step `@[x] & acc` allocation. The destination is fresh
  ## and the initial accumulator is only read, so the transform is sound
  ## for any `ih` quantity (not gated on linearity).
  checkElimCases(r, "listElim", [0, 2], nParams = 1)
  ctx.checkSeqElemArg(appArgs, "listElim")
  ctx.checkMotiveKind(r, appArgs, 1)
  let consLam = appArgs[3]
  if consLam.kind != tLam or consLam.scope.bdy.kind != tLam or
      consLam.scope.bdy.scope.bdy.kind != tLam:
    raise newException(CgUnsupported,
      "listElim cons case is not a syntactic triple lambda")
  let tlLam = consLam.scope.bdy
  let ihLam = tlLam.scope.bdy
  if consLam.dom.isNil or consLam.dom.kind != tR or
      ctx.reprKindOf(consLam.dom.refId) != repInt:
    raise newException(CgUnsupported,
      "listElim element domain outside the int fragment")
  let nilCode = cgRepr(ctx, appArgs[2], env)
  let xsCode = cgRepr(ctx, appArgs[4], env)
  let xsSym = genSym(nskLet, "cgListXs")
  let accSym = genSym(nskVar, "cgListAcc")
  let kSym = genSym(nskForVar, "cgListK")
  let xSym = genSym(nskLet, "cgListX")
  let tlSym = genSym(nskLet, "cgListTl")
  let dpsHead = dpsRebuildHead(ctx, ihLam.scope.bdy, isVec = false)
  if dpsHead.isNil:
    # de Bruijn: V0 = ih (innermost), V1 = tl, V2 = x; env innermost-first.
    let bodyCode = cgRepr(ctx, ihLam.scope.bdy,
      @[accSym, tlSym, xSym] & env)
    var stmts = newStmtList()
    stmts.add(newLetStmt(xsSym, xsCode))
    stmts.add(newVarStmt(accSym, nilCode))
    var loopBody = newStmtList()
    loopBody.add(newLetStmt(xSym,
      newTree(nnkBracketExpr, xsSym, kSym)))
    loopBody.add(newLetStmt(tlSym,
      newTree(nnkBracketExpr, xsSym,
        newTree(nnkInfix, ident"..^", newTree(nnkInfix, ident"+", kSym,
          newLit(1)), newLit(1)))))
    loopBody.add(newTree(nnkAsgn, accSym, bodyCode))
    stmts.add(newTree(nnkForStmt, kSym,
      newCall(ident"countdown",
        newTree(nnkInfix, ident"-", newCall(bindSym"len", xsSym), newLit(1)),
        newLit(0)),
      loopBody))
    stmts.add(accSym)
    var blk = newNimNode(nnkBlockStmt)
    blk.add(newEmptyNode())
    blk.add(stmts)
    blk
  else:
    # #331 destination-passing fold: de Bruijn V0 = ih, V1 = tl are absent
    # by the shape check (the empty nodes are never referenced), V2 = x.
    let headCode = cgRepr(ctx, dpsHead,
      @[newEmptyNode(), newEmptyNode(), xSym] & env)
    cgDpsFoldBlock(xsCode, nilCode, headCode, kSym, xSym, nil)

proc cgReprVecElim(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                   env: seq[NimNode]): NimNode =
  ## `vecElim A motive nilC consC n xs` over the `seq[int]`
  ## representation, compiled to a right-to-left fold:
  ##   var acc = nilC
  ##   for k in countdown(xs.len-1, 0):
  ##     acc = consC(xs.len-1-k, xs[k], xs[k+1..^1], acc)
  ##   acc
  ## The cons case must be a syntactic quadruple lambda
  ## `lam (i). lam (x). lam (xs2). lam (ih). body` with int-representable
  ## index and element domains; the `i` binder (tail length) is computed
  ## as `xs.len-1-k`, not passed. Right-to-left matches the interpreter's
  ## inside-out evaluation order (deepest consC application first). The
  ## motive (appArgs[1]) is skipped, as for `natElim`; the length index
  ## (appArgs[4]) is not evaluated (an index: type-level, author's
  ## problem if divergent, as with motives).
  ##
  ## #331 destination-passing: when the cons-case body is the cons-rebuild
  ## shape `cons A idx xHead ih` with the accumulator as the tail and the
  ## head not mentioning `ih`/`xs2` (see `dpsRebuildHead`), the fold
  ## compiles to a single preallocated destination — one `newSeq`, O(n)
  ## writes — instead of per-step `@[x] & acc` allocation. The destination
  ## is fresh and the initial accumulator is only read, so the transform
  ## is sound for any `ih` quantity (not gated on linearity).
  checkElimCases(r, "vecElim", [0, 3], nParams = 1)
  ctx.checkSeqElemArg(appArgs, "vecElim")
  ctx.checkMotiveKind(r, appArgs, 1)
  let consLam = appArgs[3]
  if consLam.kind != tLam or consLam.scope.bdy.kind != tLam or
      consLam.scope.bdy.scope.bdy.kind != tLam or
      consLam.scope.bdy.scope.bdy.scope.bdy.kind != tLam:
    raise newException(CgUnsupported,
      "vecElim cons case is not a syntactic quadruple lambda")
  let xLam = consLam.scope.bdy
  let xsLam = xLam.scope.bdy
  let ihLam = xsLam.scope.bdy
  for (lam, what) in [(consLam, "index"), (xLam, "element")]:
    if lam.dom.isNil or lam.dom.kind != tR or
        ctx.reprKindOf(lam.dom.refId) != repInt:
      raise newException(CgUnsupported,
        "vecElim " & what & " domain outside the int fragment")
  let nilCode = cgRepr(ctx, appArgs[2], env)
  let xsCode = cgRepr(ctx, appArgs[5], env)
  let xsSym = genSym(nskLet, "cgVecXs")
  let accSym = genSym(nskVar, "cgVecAcc")
  let kSym = genSym(nskForVar, "cgVecK")
  let iSym = genSym(nskLet, "cgVecI")
  let xSym = genSym(nskLet, "cgVecX")
  let tlSym = genSym(nskLet, "cgVecTl")
  let dpsHead = dpsRebuildHead(ctx, ihLam.scope.bdy, isVec = true)
  if dpsHead.isNil:
    # de Bruijn: V0 = ih, V1 = xs2, V2 = x, V3 = i; env innermost-first.
    let bodyCode = cgRepr(ctx, ihLam.scope.bdy,
      @[accSym, tlSym, xSym, iSym] & env)
    var stmts = newStmtList()
    stmts.add(newLetStmt(xsSym, xsCode))
    stmts.add(newVarStmt(accSym, nilCode))
    var loopBody = newStmtList()
    loopBody.add(newLetStmt(iSym,
      newTree(nnkInfix, ident"-",
        newTree(nnkInfix, ident"-", newCall(bindSym"len", xsSym), kSym),
        newLit(1))))
    loopBody.add(newLetStmt(xSym,
      newTree(nnkBracketExpr, xsSym, kSym)))
    loopBody.add(newLetStmt(tlSym,
      newTree(nnkBracketExpr, xsSym,
        newTree(nnkInfix, ident"..^", newTree(nnkInfix, ident"+", kSym,
          newLit(1)), newLit(1)))))
    loopBody.add(newTree(nnkAsgn, accSym, bodyCode))
    stmts.add(newTree(nnkForStmt, kSym,
      newCall(ident"countdown",
        newTree(nnkInfix, ident"-", newCall(bindSym"len", xsSym), newLit(1)),
        newLit(0)),
      loopBody))
    stmts.add(accSym)
    var blk = newNimNode(nnkBlockStmt)
    blk.add(newEmptyNode())
    blk.add(stmts)
    blk
  else:
    # #331 destination-passing fold: de Bruijn V0 = ih, V1 = xs2 are
    # absent by the shape check (the empty nodes are never referenced),
    # V2 = x, V3 = i.
    let headCode = cgRepr(ctx, dpsHead,
      @[newEmptyNode(), newEmptyNode(), xSym, iSym] & env)
    cgDpsFoldBlock(xsCode, nilCode, headCode, kSym, xSym, iSym)

proc cgReprOptionElim(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                      env: seq[NimNode]): NimNode =
  ## `optionElim A motive noneC someC o` over the `Option[int]`
  ## representation: `if o.isSome: someC(o.get) else: noneC`. The some
  ## case must be a syntactic single lambda `lam (v). body` with an
  ## int-representable domain. `noneC` is evaluated before the test,
  ## matching the interpreter's strict argument evaluation (a diverging
  ## none-branch diverges the eliminator on both sides); the motive is
  ## skipped, as for `boolElim`.
  checkElimCases(r, "optionElim", [0, 1], nParams = 1)
  ctx.checkSeqElemArg(appArgs, "optionElim")
  ctx.checkMotiveKind(r, appArgs, 1)
  let someLam = appArgs[3]
  if someLam.kind != tLam:
    raise newException(CgUnsupported,
      "optionElim some case is not a syntactic lambda")
  if someLam.dom.isNil or someLam.dom.kind != tR or
      ctx.reprKindOf(someLam.dom.refId) != repInt:
    raise newException(CgUnsupported,
      "optionElim value domain outside the int fragment")
  let noneCode = cgRepr(ctx, appArgs[2], env)
  let oCode = cgRepr(ctx, appArgs[4], env)
  let noneSym = genSym(nskLet, "cgOptNone")
  let oSym = genSym(nskLet, "cgOptO")
  let vSym = genSym(nskLet, "cgOptV")
  let someCode = cgRepr(ctx, someLam.scope.bdy, @[vSym] & env)
  var stmts = newStmtList()
  stmts.add(newLetStmt(noneSym, noneCode))
  stmts.add(newLetStmt(oSym, oCode))
  var thenBranch = newStmtList()
  thenBranch.add(newLetStmt(vSym,
    newTree(nnkDotExpr, oSym, ident"get")))
  thenBranch.add(someCode)
  stmts.add(newTree(nnkIfStmt,
    newTree(nnkElifBranch,
      newTree(nnkDotExpr, oSym, ident"isSome"), thenBranch),
    newTree(nnkElse, noneSym)))
  var blk = newNimNode(nnkBlockStmt)
  blk.add(newEmptyNode())
  blk.add(stmts)
  blk

proc cgReprNatElim(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                   env: seq[NimNode]): NimNode =
  ## `natElim motive z s n` over the int representation, compiled to an
  ## iterative fold:
  ##   var acc = z; var k = 0; while k < n: acc = s(k, acc); inc k; acc
  ## The step case must be a syntactic double lambda `lam (p). lam (ih).
  ## body` with an int-representable predecessor domain; the body is
  ## compiled with `p` and `ih` bound to the loop variables. This computes
  ## exactly the interpreter's recursion `s k (fold k)` (each iteration
  ## extends the fold by one successor step) but in constant stack space.
  ## The motive (appArgs[0]) is a type family: it is not evaluated. The
  ## interpreter evaluates it only to a closure value that reduction never
  ## uses, so skipping it is observably identical for every terminating
  ## motive; a diverging type-level motive is the author's problem, as
  ## with all type-level computation in Eponym. Evaluation order of the
  ## remaining args (z, then the scrutinee) matches the interpreter's
  ## strict left-to-right application.
  checkElimCases(r, "natElim", [0, 1])
  let sArg = appArgs[2]
  let nArg = appArgs[3]
  if sArg.kind != tLam or sArg.scope.bdy.kind != tLam:
    raise newException(CgUnsupported,
      "natElim step case is not a syntactic double lambda")
  let ihLam = sArg.scope.bdy
  if sArg.dom.isNil or sArg.dom.kind != tR or
      ctx.reprKindOf(sArg.dom.refId) != repInt:
    raise newException(CgUnsupported,
      "natElim predecessor domain outside the int fragment")
  # The ih domain is `motive p` (not atomic); ih is bound at int and the
  # body must denote an int computation — cgRepr enforces that, so the
  # induction below stays within the fragment by construction.
  let zCode = cgRepr(ctx, appArgs[1], env)
  let nCode = cgRepr(ctx, nArg, env)
  let zSym = genSym(nskLet, "cgNatZ")
  let nSym = genSym(nskLet, "cgNatN")
  let accSym = genSym(nskVar, "cgNatAcc")
  let kSym = genSym(nskVar, "cgNatK")
  # de Bruijn: V0 = ih (innermost), V1 = p; env is innermost-first.
  let bodyCode = cgRepr(ctx, ihLam.scope.bdy, @[accSym, kSym] & env)
  var stmts = newStmtList()
  stmts.add(newLetStmt(zSym, zCode))
  stmts.add(newLetStmt(nSym, nCode))
  stmts.add(newVarStmt(accSym, zSym))
  stmts.add(newVarStmt(kSym, newLit(0)))
  var loopBody = newStmtList()
  # `acc = body`: the right-hand side is evaluated before the assignment,
  # so the step body may mention the accumulator (as `ih`) soundly.
  loopBody.add(newTree(nnkAsgn, accSym, bodyCode))
  loopBody.add(newCall(ident"inc", kSym))
  stmts.add(newTree(nnkWhileStmt,
    newTree(nnkInfix, ident"<", kSym, nSym), loopBody))
  stmts.add(accSym)
  var blk = newNimNode(nnkBlockStmt)
  blk.add(newEmptyNode())
  blk.add(stmts)
  blk

proc cgReprBoolElim(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                    env: seq[NimNode]): NimNode =
  ## `boolElim motive t f b` over the int representation (`true` = 1,
  ## `false` = 0): `if b != 0: t else: f`. Both branches are evaluated
  ## before the test, matching the interpreter's strict argument
  ## evaluation (a diverging branch diverges the eliminator on both
  ## sides). The motive is skipped, as for `natElim`.
  checkElimCases(r, "boolElim", [0, 0])
  let tCode = cgRepr(ctx, appArgs[1], env)
  let fCode = cgRepr(ctx, appArgs[2], env)
  let bCode = cgRepr(ctx, appArgs[3], env)
  let tSym = genSym(nskLet, "cgBoolT")
  let fSym = genSym(nskLet, "cgBoolF")
  let bSym = genSym(nskLet, "cgBoolB")
  var stmts = newStmtList()
  stmts.add(newLetStmt(tSym, tCode))
  stmts.add(newLetStmt(fSym, fCode))
  stmts.add(newLetStmt(bSym, bCode))
  stmts.add(newTree(nnkIfStmt,
    newTree(nnkElifBranch,
      newTree(nnkInfix, ident"!=", bSym, newLit(0)), tSym),
    newTree(nnkElse, fSym)))
  var blk = newNimNode(nnkBlockStmt)
  blk.add(newEmptyNode())
  blk.add(stmts)
  blk

proc cgReprElim(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                env: seq[NimNode]): NimNode =
  ## Match-compile an eliminator application in the repr tier. Only the
  ## canonical eliminators of int-mapped families are supported; anything
  ## else (including partial application) falls back to the Phase 1
  ## backend via CgUnsupported.
  if appArgs.len != r.nargs:
    raise newException(CgUnsupported, "eliminator '" & r.name &
      "' applied to " & $appArgs.len & " args, needs " & $r.nargs &
      " (partial application falls back)")
  case r.name
  of "natElim": cgReprNatElim(ctx, r, appArgs, env)
  of "boolElim": cgReprBoolElim(ctx, r, appArgs, env)
  of "vecElim": cgReprVecElim(ctx, r, appArgs, env)
  of "listElim": cgReprListElim(ctx, r, appArgs, env)
  of "optionElim": cgReprOptionElim(ctx, r, appArgs, env)
  else:
    raise newException(CgUnsupported, "eliminator '" & r.name &
      "' outside the representation fragment")

proc cgReprCtor(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                env: seq[NimNode]): NimNode =
  ## Compile a constructor application in the repr tier.
  ##
  ## Int-mapped families (`Nat`/`Bool`): the canonical constructors get
  ## literal treatment (`zero` = 0, `suc x` = x + 1, `true` = 1,
  ## `false` = 0).
  ##
  ## `Vec`/`List` families: `nil` (applied to the family parameter) is
  ## the empty `seq[int]`; `cons` prepends (`@[x] & xs`). The family
  ## parameter and — for `Vec` — the length index are not evaluated: the
  ## former is a type argument, the latter an index (type-level;
  ## divergent indices are the author's problem, as with motives).
  ##
  ## `Option`: `none` is `none(int)`; `some v` is `some(v)`.
  ##
  ## Constructors of any other family, or non-canonical arities, are
  ## outside the fragment.
  if r.famRefId notin ctx.reps:
    raise newException(CgUnsupported, "constructor '" & r.name &
      "' of a type without a runtime representation mapping")
  let m = ctx.reps[r.famRefId]
  if m.isPlainIntMapping:
    let famName = m.eponymName
    case famName
    of "Nat":
      case r.name
      of "zero":
        if appArgs.len != 0:
          raise newException(CgUnsupported,
            "zero applied to " & $appArgs.len & " args")
        newLit(0)
      of "suc":
        if appArgs.len != 1:
          raise newException(CgUnsupported,
            "suc applied to " & $appArgs.len & " args, needs 1")
        let a = cgRepr(ctx, appArgs[0], env)
        # Issue #380: Nat is a bounded host int; the successor checks for
        # overflow instead of wrapping silently.
        newCall(bindSym"checkedNatSucc", a)
      else:
        raise newException(CgUnsupported, "Nat constructor '" & r.name &
          "' outside the representation fragment")
    of "Bool":
      case r.name
      of "true":
        if appArgs.len != 0:
          raise newException(CgUnsupported,
            "true applied to " & $appArgs.len & " args")
        newLit(1)
      of "false":
        if appArgs.len != 0:
          raise newException(CgUnsupported,
            "false applied to " & $appArgs.len & " args")
        newLit(0)
      else:
        raise newException(CgUnsupported, "Bool constructor '" & r.name &
          "' outside the representation fragment")
    else:
      raise newException(CgUnsupported, "constructor '" & r.name &
        "' of '" & famName & "' outside the representation fragment")
  elif m.isRuntimeVector or m.isRuntimeList:
    # `Vec` and `List` share the `nil`/`cons` names; the mapping (not the
    # family name) disambiguates the constructor arities.
    case r.name
    of "nil":
      if appArgs.len != 1:
        raise newException(CgUnsupported,
          "nil applied to " & $appArgs.len & " args, needs 1")
      newTree(nnkCall,
        newTree(nnkBracketExpr, ident"newSeq", ident"int"))
    of "cons":
      let (xArg, xsArg) =
        if m.isRuntimeVector:
          if appArgs.len != 4:
            raise newException(CgUnsupported,
              "Vec cons applied to " & $appArgs.len & " args, needs 4")
          (appArgs[2], appArgs[3])
        else:
          if appArgs.len != 3:
            raise newException(CgUnsupported,
              "List cons applied to " & $appArgs.len & " args, needs 3")
          (appArgs[1], appArgs[2])
      let xCode = cgRepr(ctx, xArg, env)
      let xsCode = cgRepr(ctx, xsArg, env)
      newTree(nnkInfix, ident"&", bracketOf(@[xCode]), xsCode)
    else:
      raise newException(CgUnsupported, "constructor '" & r.name &
        "' of '" & m.eponymName & "' outside the representation fragment")
  elif m.isRuntimeOption:
    case r.name
    of "none":
      if appArgs.len != 1:
        raise newException(CgUnsupported,
          "none applied to " & $appArgs.len & " args, needs 1")
      newCall(ident"none", ident"int")
    of "some":
      if appArgs.len != 2:
        raise newException(CgUnsupported,
          "some applied to " & $appArgs.len & " args, needs 2")
      newCall(ident"some", cgRepr(ctx, appArgs[1], env))
    else:
      raise newException(CgUnsupported, "constructor '" & r.name &
        "' of '" & m.eponymName & "' outside the representation fragment")
  else:
    raise newException(CgUnsupported, "constructor '" & r.name &
      "' of '" & m.eponymName & "' outside the representation fragment")

proc cgRepr(ctx: var CodegenCtx, t: Term, env: seq[NimNode]): NimNode =
  if t.isNil:
    raise newException(CgUnsupported, "nil term")
  case t.kind
  of tV:
    if t.idx < 0 or t.idx >= env.len:
      raise newException(CgUnsupported,
        "de Bruijn index " & $t.idx & " out of range")
    env[t.idx]
  of tR:
    if t.refId notin ctx.refs:
      raise newException(CgUnsupported,
        "reference id " & $t.refId & " not in codegen scope")
    let r = ctx.refs[t.refId]
    if r.kind == cgkDefn and t.refId in ctx.reprProcs:
      let rp = ctx.reprProcs[t.refId]
      if rp.arity == 0:
        newCall(ident(rp.name))
      else:
        # Applied at the enclosing tApp, which emits the direct call.
        ident(rp.name)
    elif r.kind == cgkCtor:
      # Bare constructor reference: only nullary int-mapped constructors
      # (`zero`, `true`, `false`) denote ints; anything else (e.g. a bare
      # `suc`, a function value) is outside the fragment.
      cgReprCtor(ctx, r, @[], env)
    else:
      raise newException(CgUnsupported,
        "reference '" & r.name & "' outside the representation fragment")
  of tInt:
    newLit(t.intVal)
  of tNatLit:
    # Issue #93: Nat literals are definitionally suc^n(zero); on the int
    # representation they are just int literals.
    newLit(t.natLitVal)
  of tLet:
    let vsym = genSym(nskLet, "cgReprLet")
    let vcode = cgRepr(ctx, t.letVal, env)
    let bcode = cgRepr(ctx, t.letScope.bdy, @[vsym] & env)
    var blk = newNimNode(nnkBlockStmt)
    blk.add(newEmptyNode())
    var stmts = newStmtList()
    stmts.add(newLetStmt(vsym, vcode))
    stmts.add(bcode)
    blk.add(stmts)
    blk
  of tApp:
    cgReprApp(ctx, t, env)
  else:
    raise newException(CgUnsupported,
      "term kind outside the representation fragment")

proc collectTVarIndices(t: Term, acc: var Table[int, bool]) =
  ## Collect every `tV` de Bruijn index occurring in `t` (through binders;
  ## indices are relative to `t`'s own scope).
  if t.isNil: return
  case t.kind
  of tV:
    acc[t.idx] = true
  of tPi, tSi, tLam:
    collectTVarIndices(t.dom, acc)
    collectTVarIndices(t.scope.bdy, acc)
  of tPair:
    collectTVarIndices(t.pFst, acc)
    collectTVarIndices(t.pSnd, acc)
  of tApp:
    collectTVarIndices(t.fn, acc)
    collectTVarIndices(t.arg, acc)
  of tFst, tSnd, tAbsurd:
    collectTVarIndices(t.sub, acc)
  of tLet:
    collectTVarIndices(t.letVal, acc)
    collectTVarIndices(t.letTy, acc)
    collectTVarIndices(t.letScope.bdy, acc)
  of tPrim:
    collectTVarIndices(t.primTy, acc)
  else: discard

proc compileDefProcRepr(d: ElabDef, ctx: var CodegenCtx,
                        locFile: string, locLine: int,
                        failureReason: var string): NimNode =
  ## Compile one definition to
  ## `proc eponymCompiledRepr_<name>(p1: int, ..., pn: seq[int]): ...`.
  ## Returns nil when the definition is outside the representation fragment
  ## (caller keeps the Phase 1 backend). q0 binders have environment
  ## placeholders but no Nim formal parameters.
  ##
  ## Each `Vec A n` parameter gets an entry length check: the interpreter
  ## codec (`seqToVecValue`) raises `ValueError` on `len != n`, and the
  ## repr proc preserves the loud failure (`if xs.len != n: raise`).
  ## A length index mentioning a q0-erased binder has no runtime
  ## denotation: the definition falls back to Phase 1 instead of checking
  ## against a placeholder.
  if d.tmTm.isNil or d.tyTm.isNil:
    failureReason = "definition has no checked body or type"
    return nil
  let sig =
    try: ctx.reprSig(d)
    except CgUnsupported as e:
      failureReason = e.msg
      return nil
  let erased =
    try: eraseQ0Arguments(d.tmTm)
    except ValueError as e:
      failureReason = "quantity erasure failed: " & e.msg
      return nil
  var body = erased
  var params: seq[NimNode] = @[]
  var paramTypes: seq[NimNode] = @[]
  var envOuterToInner: seq[NimNode] = @[]
  var qtyOuterToInner: seq[Quantity] = @[]
  # (paramSym, indexTerm, preceding binder quantities innermost-first,
  # preceding binder env innermost-first) for Vec entry checks.
  var vecChecks: seq[tuple[psym: NimNode, index: Term,
                           preQtys: seq[Quantity],
                           preEnv: seq[NimNode]]] = @[]
  var sigIdx = 0
  var ty = d.tyTm
  while ty != nil and ty.kind == tPi:
    if body.isNil or body.kind != tLam or body.qty != ty.qty:
      failureReason = "checked lambda structure does not match its Pi type"
      return nil
    if ty.qty == q0:
      envOuterToInner.add(newLit(0))
      qtyOuterToInner.add(q0)
    else:
      if sigIdx >= sig.len - 1:
        failureReason = "Phase 2 requires atomic mapped representation domains"
        return nil
      let rt = sig[sigIdx]
      inc sigIdx
      let psym = genSym(nskParam, "cgReprArg" & $params.len)
      params.add(psym)
      paramTypes.add(nimReprType(rt))
      if rt.kind == repSeq and rt.isVector:
        var preQtys: seq[Quantity] = @[]
        var preEnv: seq[NimNode] = @[]
        for i in countdown(qtyOuterToInner.high, 0):
          preQtys.add(qtyOuterToInner[i])
          preEnv.add(envOuterToInner[i])
        vecChecks.add((psym, rt.index, preQtys, preEnv))
      envOuterToInner.add(psym)
      qtyOuterToInner.add(ty.qty)
    body = body.scope.bdy
    ty = ty.scope.bdy
  if sigIdx != sig.len - 1:
    return nil
  if body.isNil or body.kind == tLam:
    failureReason = "definition body retains a lambda after its Pi binders"
    return nil
  var env: seq[NimNode] = @[]
  for i in countdown(envOuterToInner.high, 0):
    env.add(envOuterToInner[i])
  var prologue = newStmtList()
  for vc in vecChecks:
    var idxVars = initTable[int, bool]()
    collectTVarIndices(vc.index, idxVars)
    for j in idxVars.keys:
      if j < 0 or j >= vc.preQtys.len:
        failureReason = "Vec length index outside the representation fragment"
        return nil
      if vc.preQtys[j] == q0:
        # The length index mentions an erased binder: no runtime
        # denotation to check against. Fall back to Phase 1 rather than
        # compare against the q0 placeholder.
        failureReason = "Vec length index mentions an erased binder"
        return nil
    let nCode =
      try: cgRepr(ctx, vc.index, vc.preEnv)
      except CgUnsupported:
        failureReason = "Vec length index outside the representation fragment"
        return nil
    let nSym = genSym(nskLet, "cgVecLen")
    prologue.add(newLetStmt(nSym, nCode))
    let msg = newTree(nnkInfix, ident"&",
      newTree(nnkInfix, ident"&",
        newLit("repr Vec length mismatch: expected "),
        newCall(ident"$", nSym)),
      newTree(nnkInfix, ident"&",
        newLit(", got "),
        newCall(ident"$", newCall(bindSym"len", vc.psym))))
    prologue.add(newTree(nnkIfStmt,
      newTree(nnkElifBranch,
        newTree(nnkInfix, ident"!=", newCall(bindSym"len", vc.psym), nSym),
        newStmtList(newTree(nnkRaiseStmt,
          newCall(ident"newException", ident"ValueError", msg))))))
  let bodyCode =
    try: cgRepr(ctx, body, env)
    except CgUnsupported as e:
      failureReason = e.msg
      return nil
  var formal = newNimNode(nnkFormalParams)
  formal.add(nimReprType(sig[^1]))
  for i, psym in params:
    formal.add(newIdentDefs(psym, paramTypes[i], newEmptyNode()))
  var procNode = newNimNode(nnkProcDef)
  procNode.add(newTree(nnkPostfix, ident"*", ident(cgReprName(d.name))))
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  procNode.add(formal)
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  # Source positions (issue #329 acceptance, inherited by #330): runtime
  # errors raised while evaluating compiled code report the definition's
  # source location.
  procNode.setLineInfo(LineInfo(filename: locFile, line: locLine, column: 0))
  var bodyStmts = newStmtList()
  for s in prologue:
    bodyStmts.add(s)
  bodyStmts.add(bodyCode)
  procNode.add(bodyStmts)
  procNode

proc compileBlockProcs*(defs: seq[ElabDef], globals: Globals,
                        baseDir, src, locFile: string,
                        userLines: Table[string, int],
                        runtimeTypes: seq[HostRuntimeType] = @[]):
    tuple[procs: seq[NimNode], compiled: Table[string, string],
          compiledRepr: Table[string, string],
          reprTypes: Table[string, seq[string]],
          report: Table[string, CodegenReportEntry]] =
  ## Compile every eligible block-local definition, in dependency order.
  ## Returns the emitted procs, the def-name -> Phase-1 proc-name table for
  ## wrapper rerouting, the def-name -> repr-tier proc-name table, the
  ## def-name -> repr-tier Nim type names (params then result, e.g.
  ## `@["int", "seq[int]", "seq[int]"]`) for the wrapper identity-boundary
  ## check (issue #330 v3), and the per-definition codegen report
  ## (emitted tier + why the next tier was unavailable, issue #386).
  ## Emission order: eliminator forward declarations, Phase-1 definition
  ## bodies (callees first), repr-tier bodies (callees first, same order),
  ## eliminator bodies.
  ## `runtimeTypes` is the block's codec mapping (issue #330 representation
  ## spec); the emitter consults it to compile bodies against host
  ## representations. Definitions outside any representation keep the
  ## Phase 1 Value backend.
  var ctx = buildCodegenCtx(globals, baseDir, src, runtimeTypes)
  var bakedIds = initTable[int, string]()
  for refId, cgRef in ctx.refs.pairs:
    bakedIds[refId] = cgRef.name
    if cgRef.kind == cgkElim:
      for ctorId in cgRef.cases.keys:
        let ctorName = ctx.refs.getOrDefault(ctorId).name
        bakedIds[ctorId] = ctorName
  validateBakedRefIds(globals, bakedIds)
  result = (procs: @[], compiled: initTable[string, string](),
            compiledRepr: initTable[string, string](),
            reprTypes: initTable[string, seq[string]](),
            report: initTable[string, CodegenReportEntry]())
  detectBadElims(ctx)
  var defRefIds = initTable[string, int]()
  for d in defs:
    if d.name in globals and globals[d.name].tm != nil and
        globals[d.name].tm.kind == tR:
      defRefIds[d.name] = globals[d.name].tm.refId
  # Erase first: erasure failures are not compilable.
  var erasedTerms = initTable[string, Term]()
  var phase1Failures = initTable[string, string]()
  for d in defs:
    if d.tmTm.isNil:
      phase1Failures[d.name] = "definition has no checked body"
      continue
    try:
      erasedTerms[d.name] = eraseQ0Arguments(d.tmTm)
    except ValueError as e:
      phase1Failures[d.name] = "quantity erasure failed: " & e.msg
  # Dependency graph over block-local defs (self-edges excluded).
  var deps = initTable[string, Table[int, bool]]()
  for d in defs:
    if d.name notin erasedTerms: continue
    let selfId = defRefIds.getOrDefault(d.name, -1)
    var acc = initTable[int, bool]()
    var ids = initTable[int, bool]()
    collectRefIds(erasedTerms[d.name], ids)
    for id in ids.keys:
      if id == selfId: continue
      for _, depId in defRefIds.pairs:
        if depId == id:
          acc[id] = true
          break
    deps[d.name] = acc
  # Kahn's algorithm, callees first; leftovers are cycles -> interpreter.
  var order: seq[string] = @[]
  var emitted = initTable[string, bool]()
  var progress = true
  while progress:
    progress = false
    for d in defs:
      if d.name notin erasedTerms or emitted.getOrDefault(d.name, false):
        continue
      var ready = true
      for refId in deps[d.name].keys:
        var owner = ""
        for name, id in defRefIds.pairs:
          if id == refId: owner = name
        if owner.len > 0 and owner in erasedTerms and
            not emitted.getOrDefault(owner, false):
          ready = false
          break
      if ready:
        order.add(d.name)
        emitted[d.name] = true
        progress = true
  # Compile in dependency order. A callee that fails keeps compiledProc ""
  # so callers use the slow path for it — no cascade needed.
  var defBodies: seq[NimNode] = @[]
  for d in defs:
    if d.name notin erasedTerms and d.name notin phase1Failures:
      phase1Failures[d.name] = "definition could not be erased for Phase 1"
  for d in defs:
    if d.name in erasedTerms and not emitted.getOrDefault(d.name, false):
      phase1Failures[d.name] = "recursive dependency cycle prevents Phase 1 compilation"
  for name in order:
    var d: ElabDef
    for cand in defs:
      if cand.name == name: d = cand
    let refId = defRefIds.getOrDefault(name, -1)
    if refId in ctx.refs:
      var r = ctx.refs[refId]
      r.compiledProc = cgName(name)  # pre-assign: self-recursion
      ctx.refs[refId] = r
    var failureReason = ""
    let procNode = compileDefProcWithReason(d, ctx, locFile,
      userLines.getOrDefault(name, 1), failureReason)
    if procNode.isNil:
      phase1Failures[name] = failureReason
      if refId in ctx.refs:
        var r = ctx.refs[refId]
        r.compiledProc = ""
        ctx.refs[refId] = r
    else:
      defBodies.add(procNode)
      result.compiled[name] = cgName(name)
  # Repr tier (issue #330): second pass over the same dependency order, so
  # callees' repr procs exist before callers reference them. A callee that
  # fails the fragment keeps no repr entry, so callers referencing it fall
  # back to the Phase 1 backend — no cascade needed. Pre-assignment is per
  # definition (not all-at-once) so a later failure can never strand an
  # already-emitted caller referencing a missing proc.
  var reprBodies: seq[NimNode] = @[]
  var reprFailures = initTable[string, string]()
  for name in order:
    var d: ElabDef
    for cand in defs:
      if cand.name == name: d = cand
    let refId = defRefIds.getOrDefault(name, -1)
    if refId < 0:
      continue
    var sig: seq[ReprType]
    try:
      sig = ctx.reprSig(d)
    except CgUnsupported as e:
      reprFailures[name] = e.msg
      continue
    ctx.reprProcs[refId] = (name: cgReprName(name), arity: sig.len - 1)
    var failureReason = ""
    let procNode = compileDefProcRepr(d, ctx, locFile,
      userLines.getOrDefault(name, 1), failureReason)
    if procNode.isNil:
      reprFailures[name] = failureReason
      ctx.reprProcs.del(refId)
    else:
      reprBodies.add(procNode)
      result.compiledRepr[name] = cgReprName(name)
      var typeNames: seq[string] = @[]
      for rt in sig:
        typeNames.add(reprTypeName(rt))
      result.reprTypes[name] = typeNames
  # Summarize the best emitted tier and why the next tier was unavailable.
  for d in defs:
    var entry = CodegenReportEntry(tier: cgtInterpreter,
      reason: "Phase 1 unavailable: " &
        phase1Failures.getOrDefault(d.name, "definition was not compiled"),
      slowPaths: @[])
    if d.name in result.compiled:
      entry.tier = cgtValue
      entry.reason = "Phase 2 unavailable: " &
        reprFailures.getOrDefault(d.name, "definition was not considered")
    if d.name in result.compiledRepr:
      entry.tier = cgtRepr
      entry.reason = "Phase 2 representation code emitted"
    if d.name in erasedTerms:
      var ids = initTable[int, bool]()
      collectRefIds(erasedTerms[d.name], ids)
      var seenSlowPaths = initTable[string, bool]()
      for refId in ids.keys:
        if refId in ctx.refs and ctx.refs[refId].kind == cgkDefn and
            ctx.refs[refId].compiledProc.len == 0:
          let slowName = ctx.refs[refId].name
          if not seenSlowPaths.getOrDefault(slowName, false):
            entry.slowPaths.add(slowName)
            seenSlowPaths[slowName] = true
      entry.slowPaths.sort()
    result.report[d.name] = entry
  # Emit eliminator procs for every used eliminator. The fixpoint handles
  # templates that reference further eliminators; detectBadElims already
  # guaranteed templates compile.
  var elimBodies: seq[NimNode] = @[]
  var doneElims = initTable[int, bool]()
  while true:
    var pending: seq[int] = @[]
    for e in ctx.usedElims.keys:
      if not doneElims.getOrDefault(e, false): pending.add(e)
    if pending.len == 0: break
    for e in pending:
      doneElims[e] = true
      elimBodies.add(compileElimProc(ctx, e))
  var elimFwds: seq[NimNode] = @[]
  for e in doneElims.keys:
    var fwd = newNimNode(nnkProcDef)
    fwd.add(newTree(nnkPostfix, ident"*", ident(elimProcName(ctx.refs[e].name))))
    fwd.add(newEmptyNode())
    fwd.add(newEmptyNode())
    var fwdFormal = newNimNode(nnkFormalParams)
    fwdFormal.add(bindSym"Value")
    fwdFormal.add(newIdentDefs(ident"cgProcArgs",
      newTree(nnkBracketExpr, ident"seq", bindSym"Value"), newEmptyNode()))
    fwdFormal.add(newIdentDefs(ident"cgProcBindings",
      bindSym"RuntimeBindings", newEmptyNode()))
    fwd.add(fwdFormal)
    fwd.add(newEmptyNode())
    fwd.add(newEmptyNode())
    fwd.add(newEmptyNode())  # forward declaration: empty body
    elimFwds.add(fwd)
  result.procs = elimFwds & defBodies & reprBodies & elimBodies
