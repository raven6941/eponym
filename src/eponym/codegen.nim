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
## Supported fragment (anything else -> interpreter fallback):
## - all term forms except `tMeta` (rejected already by erasure)
## - `tR` to postulates / data constructors: neutral value or bindings lookup
## - `tR` to definitions compiled in the same block: direct recursive call
## - `tR` to other definitions: slow path through `callValueFuncDir`
## - eliminators (`wRed`): only fully applied, via a generated
##   `eponymElim_<name>` proc holding the static case dispatch over the
##   registered reduction rules; partially-applied or bare eliminator
##   references fall back to the interpreter
## - `tPrim`: primitive Int ops via the existing `vPrim` accumulation
##
## Deliberate deviations from the interpreter (all unreachable in checked
## code, documented here):
## - `syn` fields are approximate (never nil, but not substituted): semantics
##   live in `whnf`; `syn` is only a fallback for runtime type inference.
## - an eliminator scrutinee whose spine length is not exactly
##   `nParams + ctorArity` yields a stuck neutral instead of proceeding with
##   a short environment (the interpreter would raise `IndexDefect` there).
## - refIds are baked in as integer literals. They are stable across
##   elaborations of the same source (sequential `freshId`, deterministic
##   elaborator); the differential tests pin this.
## - reduction-rule contractum templates are compiled as written (unerased):
##   erasure is a closed-term pass and templates are open. This matches the
##   interpreter, which fires `fireRed` on the unerased template.

import std/[tables, macros]
import eponym_init   # Term, Value, WhnfKind, smart constructors
import preterm       # Quantity
import elab          # ElabDef, Globals, GEntry
import erasure       # eraseQ0Arguments
import eponym_embed  # callValueFuncDir, initRuntimeBindings (bindSym targets)

type
  CgUnsupported* = object of CatchableError
    ## Raised when a term is outside the compilable fragment. Caught at the
    ## definition boundary; the definition keeps its interpreter wrapper.

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

proc cgName*(defName: string): string =
  ## The emitted proc name for a compiled definition.
  "eponymCompiled_" & defName

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

proc buildCodegenCtx*(globals: Globals, baseDir, src: string,
                     runtimeTypes: seq[HostRuntimeType] = @[]): CodegenCtx =
  ## Resolve every global reference to its codegen treatment. `runtimeTypes`
  ## is the block's codec mapping (issue #330 representation spec); each
  ## named Eponym type/family resolves to its refId for emitter lookup.
  result = CodegenCtx(refs: initTable[int, CgRef](), baseDir: baseDir,
    src: src, badElims: initTable[int, bool](),
    usedElims: initTable[int, bool](),
    reps: initTable[int, HostRuntimeType]())
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
      result.refs[refId] = CgRef(name: name, kind: cgkCtor)
    elif e.tm.refIsDefn:
      result.refs[refId] = CgRef(name: name, kind: cgkDefn, compiledProc: "")
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

proc cgAppChain(ctx: var CodegenCtx, t: Term, env: seq[NimNode],
                bnd: NimNode): NimNode =
  ## Compile `tApp` chains. Everything folds through `vAppWithBindings`
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
    acc = newCall(bindSym"vAppWithBindings", acc, cg(ctx, a, env, bnd), bnd)
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
        badElims: ctx.badElims, usedElims: initTable[int, bool]())
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
  procNode

proc compileDefProc*(d: ElabDef, ctx: var CodegenCtx,
                     locFile: string, locLine: int): NimNode =
  ## Compile one definition to `proc eponymCompiled_<name>(args: seq[Value],
  ## bindings: RuntimeBindings): Value`. Returns nil when the definition is
  ## outside the supported fragment (caller keeps the interpreter wrapper).
  ##
  ## The emitted proc computes the definition's value with direct code, then
  ## applies `args` left to right — the same two phases as
  ## `callDefValueWithBindings`, minus the term walk.
  if d.tmTm.isNil:
    return nil
  let erased =
    try: eraseQ0Arguments(d.tmTm)
    except ValueError:
      return nil
  let argsSym = ident"cgProcArgs"
  let bndSym = ident"cgProcBindings"
  var formal = newNimNode(nnkFormalParams)
  formal.add(bindSym"Value")
  formal.add(newIdentDefs(argsSym,
    newTree(nnkBracketExpr, ident"seq", bindSym"Value"), newEmptyNode()))
  formal.add(newIdentDefs(bndSym, bindSym"RuntimeBindings", newEmptyNode()))
  var procNode = newNimNode(nnkProcDef)
  procNode.add(newTree(nnkPostfix, ident"*", ident(cgName(d.name))))
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  procNode.add(formal)
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  let accSym = genSym(nskVar, "cgAcc")
  let aSym = genSym(nskForVar, "cgArg")
  let bodyCode =
    try: cg(ctx, erased, @[], bndSym)
    except CgUnsupported:
      return nil
  var inner = newStmtList()
  inner.add(newVarStmt(accSym, bodyCode))
  inner.add(newTree(nnkForStmt, aSym, argsSym,
    newStmtList(newAssignment(accSym,
      newCall(bindSym"vAppWithBindings", accSym, aSym, bndSym)))))
  inner.add(accSym)
  # Source positions (issue #329 acceptance): runtime errors raised while
  # evaluating compiled code report the definition's source location.
  # locLine is the definition's line in the user's file (not the
  # elaborator's string-relative loc).
  procNode.setLineInfo(LineInfo(filename: locFile, line: locLine, column: 0))
  procNode.add(inner)
  procNode

proc compileBlockProcs*(defs: seq[ElabDef], globals: Globals,
                        baseDir, src, locFile: string,
                        userLines: Table[string, int],
                        runtimeTypes: seq[HostRuntimeType] = @[]):
    tuple[procs: seq[NimNode], compiled: Table[string, string]] =
  ## Compile every eligible block-local definition, in dependency order.
  ## Returns the emitted procs and the def-name -> proc-name table for
  ## wrapper rerouting. Emission order: eliminator forward declarations,
  ## definition bodies (callees first), eliminator bodies.
  ## `runtimeTypes` is the block's codec mapping (issue #330 representation
  ## spec); the emitter will consult it to compile bodies against host
  ## representations. Definitions outside any representation keep the
  ## Phase 1 Value backend.
  var ctx = buildCodegenCtx(globals, baseDir, src, runtimeTypes)
  result = (procs: @[], compiled: initTable[string, string]())
  detectBadElims(ctx)
  var defRefIds = initTable[string, int]()
  for d in defs:
    if d.name in globals and globals[d.name].tm != nil and
        globals[d.name].tm.kind == tR:
      defRefIds[d.name] = globals[d.name].tm.refId
  # Erase first: erasure failures are not compilable.
  var erasedTerms = initTable[string, Term]()
  for d in defs:
    if d.tmTm.isNil: continue
    try:
      erasedTerms[d.name] = eraseQ0Arguments(d.tmTm)
    except ValueError:
      discard
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
  for name in order:
    var d: ElabDef
    for cand in defs:
      if cand.name == name: d = cand
    let refId = defRefIds.getOrDefault(name, -1)
    if refId in ctx.refs:
      var r = ctx.refs[refId]
      r.compiledProc = cgName(name)  # pre-assign: self-recursion
      ctx.refs[refId] = r
    let procNode = compileDefProc(d, ctx, locFile,
      userLines.getOrDefault(name, 1))
    if procNode.isNil:
      if refId in ctx.refs:
        var r = ctx.refs[refId]
        r.compiledProc = ""
        ctx.refs[refId] = r
    else:
      defBodies.add(procNode)
      result.compiled[name] = cgName(name)
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
  result.procs = elimFwds & defBodies & elimBodies
