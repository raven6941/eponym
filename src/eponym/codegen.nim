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
## - `tR` to other definitions: a cross-block direct call when the callee
##   was exported by an earlier block in the same compilation (issue #408),
##   else the slow path through `callValueFuncDir`
## - eliminators (`wRed`): fully applied via a generated
##   `eponymElim_<name>` proc holding the static case dispatch over the
##   registered reduction rules; emitted constructor labels are validated
##   against that table before code is returned; partially-applied or bare
##   eliminator references eta-expand into nested `vHostFunc` closures
##   over the missing arguments (issue #407)
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

import std/[tables, macros, algorithm, sequtils, strutils, sets]
import eponym_init   # Term, Value, WhnfKind, smart constructors
import preterm       # Quantity
import elab          # ElabDef, Globals, GEntry
import erasure       # eraseQ0Arguments
import eponym_embed  # callValueFuncDir, initRuntimeBindings (bindSym targets)
import usage_check  # countVarUses for the #413 chain-lift linearity check

type
  ReprKind* = enum
    repInt  # Eponym type mapped to Nim `int` via plain runtimeType
    repSeq  # `Vec`/`List` family mapped to Nim `seq[int]`
    repOption  # `Option` family mapped to Nim `Option[int]`
    repOpaque  # Issue #401: any other concrete `runtimeType` mapping is an
      # identity representation over its declared host type. Covers atomic
      # postulated types (`Promise` -> `PaxosPromise`) and applied families
      # declared at the family level (`Chan s` -> `PaxosChannel` for every
      # session index `s`): family indices are dropped from the host
      # signature, exactly as `Vec A n` maps to one `seq[int]`. Declaring
      # one host type for a whole family asserts the host layout is
      # index-independent; the checker cannot verify host layout, so this
      # is trusted (see docs/trust-model.md).
    repSigma  # Issue #401: a dependent `Sig` over representation
      # components maps to the host tuple of the components. The second
      # component's representation is selected with its index-dependence
      # on the first component erased: sound precisely when the component
      # mappings are index-independent (e.g. an opaque family), and
      # honestly rejected when a live index (a `Vec` length) would mention
      # the bound value.
    repFunc  # Issue #407 slice 3: a function type maps to a `{.closure.}`
      # Nim proc type over the representation types, flattened across
      # curried binders (`Pi x:A. Pi y:B. C` is `proc (x: reprA, y: reprB):
      # reprC {.closure.}`, matching both the multi-parameter closures
      # `cgReprElimClosure` emits and the uncurried compiled defs, which
      # Nim converts implicitly). Lets closure values (partially-applied
      # eliminators) cross definition boundaries as ordinary proc values.
      # Dependency of the codomain on the bound value is erased exactly as
      # for `repSigma`: honestly rejected in live index positions.

  ReprType* = object
    ## The host representation of one signature position (a non-q0
    ## binder domain or the result type).
    kind*: ReprKind
    isVector*: bool  # for repSeq: from runtimeVector (length-indexed)
    index*: Term  # for repSeq+isVector: the length index term
    hostType*: NimNode  # for repOpaque: the declared Nim type AST
    sigmaFields*: seq[ReprType]  # for repSigma: the component reprs
    funcDom*: ref ReprType  # for repFunc: the domain representation
    funcCod*: ref ReprType  # for repFunc: the codomain representation

proc boxRepr*(rt: ReprType): ref ReprType =
  ## Box a representation type for a `repFunc` field.
  new(result)
  result[] = rt

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
    crossBlockFrom*: string
      ## Issue #408: non-empty when this definition reuses a proc emitted
      ## by an earlier eponymBlock in the same compilation, of the form
      ## "<proc> from <origin>"; empty for locally compiled definitions.

  CrossBlockExport* = object
    ## Issue #408: one entry of the compile-time cross-block export
    ## registry. An earlier eponymBlock in the same Nim module published
    ## the emitted proc names of an import-origin definition; a later
    ## block reuses them via direct calls instead of re-emitting (which
    ## would be a redefinition error, since emitted proc names are
    ## deterministic in the definition name). Registry key:
    ## `loc.source & "\x00" & name`.
    valueProc*: string  ## "" when the def was not value-compiled
    reprProc*: string   ## "" when the def was not repr-compiled
    sigSummary*: string ## repr signature agreement token (reprSigSummary)

  CrossBlockExportInfo* = object
    ## Issue #408: what one compileBlockProcs invocation publishes about
    ## an import-origin definition it compiled, for the macro to register
    ## into the cross-block registry.
    origin*: string     ## the def's loc.source (the .ep file it came from)
    valueProc*: string
    reprProc*: string
    sigSummary*: string
    postulatesUsed*: seq[string]
      ## Names of postulates in the definition's transitive runtime
      ## closure, for the repr-tier bound-postulate exclusion rule.

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

  RawValueAdapterSpec* = object
    ## Issue #409: one statically-known instantiation of a
    ## `bindPostulateValue`-bound postulate, as collected by the
    ## `eponymBlock` macro's instantiation scan. `typeArgNames` are the
    ## canonical type names in Pi-spine order; `key` is the full
    ## `postulateName@k1;k2` key; `implementation` is the user's
    ## `(args: seq[Value], globals: Globals): Value` Nim proc; `procName`
    ## is the macro-assigned (block-unique) adapter proc name.
    postulateName*: string
    typeArgNames*: seq[string]
    key*: string
    implementation*: NimNode
    procName*: string
    reprProcName*: string
      ## Issue #409 slice 3: macro-assigned (block-unique) name for the
      ## repr-tier adapter proc of this instantiation (the `int -> int`
      ## style forwarder that encodes its arguments, calls the Value-tier
      ## adapter, and decodes the result).

  PostulateAdapter* = object
    ## Issue #409: an emitted typed adapter, registered on CodegenCtx by
    ## postulate refId. `isTypeBinder` classifies the postulate's Pi spine
    ## (outermost first): type-binder positions carry baked type witnesses
    ## in the adapter body, the rest become the adapter's Value parameters
    ## in spine order. `typeKey` is `typeArgNames.join(";")`.
    key*: string
    typeKey*: string
    procName*: string
    isTypeBinder*: seq[bool]

  ReprPostulateAdapter* = object
    ## Issue #409 slice 3: an emitted repr-tier adapter, registered on
    ## CodegenCtx by postulate refId, one per statically-known
    ## instantiation of a `bindPostulateValue`-bound postulate whose value
    ## binders and result all denote the int representation. `isTypeBinder`
    ## classifies the postulate's Pi spine (outermost first) exactly like
    ## `PostulateAdapter`: type-binder positions are erased (their
    ## witnesses are baked into the Value-tier adapter this one calls),
    ## value positions become the adapter's `int` formals in spine order.
    ## `typeKey` is `typeArgNames.join(";")`. `cgReprApp` reroutes
    ## fully-applied call sites whose type arguments match to a direct
    ## call; codecs run only on the adapter's value boundary.
    key*: string
    typeKey*: string
    procName*: string
    isTypeBinder*: seq[bool]

  CodegenCtx* = object
    refs*: Table[int, CgRef]
    inlineGenericDefs*: Table[int, ElabDef]
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
    reprProcs*: Table[int, tuple[name: string, arity: int,
                                 sig: seq[ReprType]]]
      ## Issue #330 repr tier: def refId -> (emitted proc name, int arity)
      ## for definitions compiled against host representations directly.
      ## Pre-assigned before compiling a body so recursion resolves.
      ## Issue #401: also holds postulate forwarders (see
      ## `compilePostulateProcRepr`), so in-body calls to bound postulates
      ## become direct calls.
    reprPostulateQtys*: Table[int, seq[Quantity]]
      ## Issue #401: postulate refId -> Pi-binder quantities for postulate
      ## forwarders, so call sites skip q0 arguments exactly like the
      ## `cgkDefn` path skips them via `piQuantities`.
    postulateAdapters*: Table[int, seq[PostulateAdapter]]
      ## Issue #409: postulate refId -> emitted typed adapters, one per
      ## statically-known instantiation of a `bindPostulateValue`-bound
      ## postulate. `cgAppChain` reroutes fully-applied call sites whose
      ## type arguments match an adapter's key to a direct call.
    postulateReprAdapters*: Table[int, seq[ReprPostulateAdapter]]
      ## Issue #409 slice 3: postulate refId -> emitted repr-tier
      ## adapters, one per statically-known instantiation whose value
      ## binders and result all denote the int representation.
      ## `cgReprApp` reroutes fully-applied call sites whose type
      ## arguments match an adapter's key to a direct call of the repr
      ## forwarder (codecs only on the value boundary).

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
  ## #330 v3: `nil : Pi(A: Univ, Vec A zero)` and
  ## `none : Pi(A: Univ, Option A)` have application-headed results.)
  var t = ctorTy
  while t != nil and t.kind == tPi:
    t = t.scope.bdy
  while t != nil and t.kind == tApp:
    t = t.fn
  if t != nil and t.kind == tR: t.refId else: -1

proc isInlineGenericDef(ctx: CodegenCtx, d: ElabDef): bool =
  ## A universe binder is a compile-time type parameter. Definitions
  ## with one are specialized by beta-reducing their body at compiled call
  ## sites, so they need no standalone runtime representation or wrapper.
  var ty = d.tyTm
  var body = d.tmTm
  while not ty.isNil and ty.kind == tPi and not body.isNil and
      body.kind == tLam:
    if not ty.dom.isNil and (ty.dom.kind == tType or
        (ty.dom.kind == tR and ty.dom.refId in ctx.refs and
         ctx.refs[ty.dom.refId].name == "Univ")):
      return true
    ty = ty.scope.bdy
    body = body.scope.bdy

proc buildCodegenCtx*(globals: Globals, baseDir, src: string,
                     runtimeTypes: seq[HostRuntimeType] = @[],
                     definitions: seq[ElabDef] = @[]): CodegenCtx =
  ## Resolve every global reference to its codegen treatment. `runtimeTypes`
  ## is the block's codec mapping (issue #330 representation spec); each
  ## named Eponym type/family resolves to its refId for emitter lookup.
  result = CodegenCtx(refs: initTable[int, CgRef](), baseDir: baseDir,
    src: src, badElims: initTable[int, bool](),
    inlineGenericDefs: initTable[int, ElabDef](),
    usedElims: initTable[int, bool](),
    reps: initTable[int, HostRuntimeType](),
    reprProcs: initTable[int, tuple[name: string, arity: int, sig: seq[ReprType]]](),
    reprPostulateQtys: initTable[int, seq[Quantity]](),
    postulateAdapters: initTable[int, seq[PostulateAdapter]](),
    postulateReprAdapters: initTable[int, seq[ReprPostulateAdapter]]())
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
  for d in definitions:
    if d.name in globals and not globals[d.name].tm.isNil and
        globals[d.name].tm.kind == tR and result.isInlineGenericDef(d):
      result.inlineGenericDefs[globals[d.name].tm.refId] = d

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

proc cgElimClosure(ctx: var CodegenCtx, r: CgRef, elimRefId: int,
                   provided: seq[Term], env: seq[NimNode],
                   bnd: NimNode): NimNode =
  ## Eta-expand a partially-applied (or bare) eliminator into nested host
  ## closures (issue #407). The provided arguments are evaluated
  ## left-to-right at the creation site — matching the interpreter's strict
  ## application order — and each missing argument becomes one
  ## `proc (Value): Value` parameter; the innermost body is the saturated
  ## `eponymElim_<name>` dispatch call. The result is an ordinary
  ## `vHostFunc` closure value: it can be stored, passed to compiled
  ## definitions, returned, and applied later with `vAppWithBindings`.
  ## Like every other Value-backend closure, the missing parameters are
  ## plain `Value`s, so quantity-0 binders and type-level positions (the
  ## motive) need no special treatment here.
  ctx.usedElims[elimRefId] = true
  let missing = r.nargs - provided.len
  var preStmts = newStmtList()
  var argSyms: seq[NimNode] = @[]
  for a in provided:
    let s = genSym(nskLet, "cgElimPart")
    preStmts.add(newLetStmt(s, cg(ctx, a, env, bnd)))
    argSyms.add(s)
  var paramSyms: seq[NimNode] = @[]
  for i in 0 ..< missing:
    paramSyms.add(genSym(nskParam, "cgElimMiss"))
  var body = newCall(ident(elimProcName(r.name)),
    bracketOf(argSyms & paramSyms), bnd)
  for i in countdown(paramSyms.high, 0):
    body = newCall(bindSym"vHostFunc", cgLambda(paramSyms[i], body))
  if preStmts.len == 0:
    return body
  preStmts.add(body)
  var blk = newNimNode(nnkBlockStmt)
  blk.add(newEmptyNode())
  blk.add(preStmts)
  blk

proc postulateTypeArgKey409(ctx: CodegenCtx, term: Term): string =
  ## Issue #409: canonical key for a postulate type argument at a codegen
  ## call site, mirroring the macro scan's `staticTypeArgKey409`. A bare
  ## type reference with a runtime codec (or a primitive) yields its type
  ## name; anything else yields "" (no adapter match, keep the fold).
  if term.isNil: return ""
  if term.kind == tR and term.refId in ctx.refs:
    let tname = ctx.refs[term.refId].name
    if tname in ["Int", "Nat", "Bool"]: return tname
    if term.refId in ctx.reps: return tname
  ""

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
      if appArgs.len < r.nargs:
        # Issue #407: a partially-applied eliminator eta-expands into a
        # closure over the missing arguments (an ordinary vHostFunc value).
        return cgElimClosure(ctx, r, head.refId, appArgs, env, bnd)
      if appArgs.len > r.nargs:
        raise newException(CgUnsupported,
          "eliminator '" & r.name & "' applied to " & $appArgs.len &
          " args, needs " & $r.nargs & " (over-application is outside the fragment)")
      ctx.usedElims[head.refId] = true
      var argCodes: seq[NimNode] = @[]
      for a in appArgs:
        argCodes.add(cg(ctx, a, env, bnd))
      return newCall(ident(elimProcName(r.name)), bracketOf(argCodes), bnd)
  if head.kind == tR and head.refId in ctx.postulateAdapters:
    # Issue #409: a fully-applied call to a `bindPostulateValue`-bound
    # postulate whose type arguments match an emitted typed adapter becomes
    # a direct call, skipping the `postulateValue` bindings-table lookup
    # and the per-argument `vCompiledAppWithBindings` fold. Anything else
    # (partial application, non-static type argument — the macro scan
    # rejects those, but eliminator contractums are unscanned) keeps the
    # uniform fold below.
    for adapter in ctx.postulateAdapters[head.refId]:
      if appArgs.len != adapter.isTypeBinder.len: continue
      var keys: seq[string] = @[]
      var ok = true
      for i in 0 ..< appArgs.len:
        if adapter.isTypeBinder[i]:
          let k = postulateTypeArgKey409(ctx, appArgs[i])
          if k.len == 0:
            ok = false
            break
          keys.add(k)
      if not ok: continue
      if keys.join(";") != adapter.typeKey: continue
      var call = newCall(ident(adapter.procName), bnd)
      for i in 0 ..< appArgs.len:
        if not adapter.isTypeBinder[i]:
          call.add(cg(ctx, appArgs[i], env, bnd))
      return call
  # Uniform fold: evaluate the head, then each argument left to right,
  # applying as we go — exactly the interpreter's order.
  # Issue #479 (pre-existing; surfaced by #478's sheds_demo migration):
  # a compiled def proc consumes its q0 Pi binders internally (unit
  # witnesses from q0Args), so a caller folding onto it must NOT pass
  # those arguments again: double consumption shifts every later
  # argument and sticks the application (a generic identity called at
  # a type argument applied the type as the value, then stuck applying
  # the value as a function). The slow path is different: the
  # interpreter closure keeps all binders, so its fold passes every
  # argument.
  # Only the LEADING q0 run is skipped, not every q0 position: the
  # proc is called with empty args here, and its Pi loop applies q0
  # witnesses only while canBind holds — i.e. until the first ω
  # binder, which sets canBind false. A non-leading q0 binder is never
  # consumed by the proc, so the fold must still pass it; skipping it
  # misbinds every later argument (regression caught by
  # convex_opt_vec, whose callees interleave runtime and q0 binders).
  var skipQ0: seq[bool] = @[]
  if head.kind == tR and head.refId in ctx.refs:
    let r = ctx.refs[head.refId]
    if r.kind == cgkDefn and r.compiledProc.len > 0:
      var leading = true
      for i in 0 ..< appArgs.len:
        let isQ0 = i < r.piQuantities.len and r.piQuantities[i] == q0
        skipQ0.add(leading and isQ0)
        if not isQ0: leading = false
  var acc = cg(ctx, head, env, bnd)
  for i, a in appArgs:
    if i < skipQ0.len and skipQ0[i]: continue
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
      # Issue #407: a bare eliminator reference is the fully-eta-expanded
      # closure (every argument missing).
      if t.refId in ctx.badElims:
        raise newException(CgUnsupported,
          "eliminator '" & r.name & "' is not compilable")
      return cgElimClosure(ctx, r, t.refId, @[], env, bnd)
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

proc collectRuntimeRefIds(t: Term, acc: var Table[int, bool]) =
  ## Collect every `tR` refId occurring in a *runtime term position* of an
  ## erased term. Binder domains, `let` types, pair type annotations, and
  ## primop types are type positions and skipped; quantity-0 arguments are
  ## already unit after erasure. A `tPi`/`tSi` occurring as a term (a type
  ## passed as an explicit `Univ` argument) is walked conservatively.
  if t.isNil: return
  case t.kind
  of tR:
    acc[t.refId] = true
  of tPi, tSi:
    collectRuntimeRefIds(t.dom, acc)
    collectRuntimeRefIds(t.scope.bdy, acc)
  of tLam:
    collectRuntimeRefIds(t.scope.bdy, acc)
  of tPair:
    collectRuntimeRefIds(t.pFst, acc)
    collectRuntimeRefIds(t.pSnd, acc)
  of tApp:
    collectRuntimeRefIds(t.fn, acc)
    collectRuntimeRefIds(t.arg, acc)
  of tFst, tSnd, tAbsurd:
    collectRuntimeRefIds(t.sub, acc)
  of tLet:
    collectRuntimeRefIds(t.letVal, acc)
    collectRuntimeRefIds(t.letScope.bdy, acc)
  of tMeta:
    for arg in t.metaSpine: collectRuntimeRefIds(arg, acc)
  else: discard

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
        reprProcs: initTable[int, tuple[name: string, arity: int, sig: seq[ReprType]]]())
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

proc isPlainIntMapping*(m: HostRuntimeType): bool =
  ## True when the mapping is a plain `runtimeType ... -> int` (not a
  ## vector/list/option/variant/codec mapping): the host representation
  ## is exactly Nim `int` with the identity boundary conversion.
  not m.isRuntimeVector and not m.isRuntimeList and
    not m.isRuntimeOption and not m.isRuntimeVariant and
    not m.isRuntimeCodec and
    m.nimType.kind in {nnkIdent, nnkSym} and $m.nimType == "int"

proc isTypeVariableMapping*(m: HostRuntimeType): bool =
  ## True for `runtimeType(T, T)`-style mappings whose host type is a bare
  ## type variable rather than a concrete host type: there is no identity
  ## representation to compile against.
  m.nimType.kind in {nnkIdent, nnkSym} and $m.nimType == m.eponymName

proc isOpaqueIdentityMapping*(m: HostRuntimeType): bool =
  ## True when the mapping declares a concrete host type used as-is, with
  ## no conversion: a plain `runtimeType` that is not an int mapping, not a
  ## vector/list/option/variant/codec mapping, not a type variable, and not
  ## carrying a trusted record codec (the codec defines the boundary
  ## semantics, including dependent-index checks, so the mapping is not an
  ## identity representation). Issue #401: these become the `repOpaque`
  ## representation kind.
  not m.isRuntimeVector and not m.isRuntimeList and
    not m.isRuntimeOption and not m.isRuntimeVariant and
    not m.isRuntimeCodec and not m.isPlainIntMapping and
    not m.isTypeVariableMapping and not m.hasRecordCodec

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
  if m.isOpaqueIdentityMapping:
    return repOpaque
  raise newException(CgUnsupported,
    "runtime representation outside the fragment")

proc checkIntElem(ctx: CodegenCtx, t: Term) =
  ## v3 scope: collection element types must be in the int fragment.
  if t.isNil or t.kind != tR or ctx.reprKindOf(t.refId) != repInt:
    raise newException(CgUnsupported,
      "collection element type outside the int fragment")

proc reprTypeMentionsMarker(t: Term, markerRefId: int): bool =
  ## Does the marker reference survive anywhere in `t`? Used to detect a
  ## Sigma codomain whose live index positions mention the bound value.
  if t.isNil: return false
  case t.kind
  of tR: t.refId == markerRefId
  of tV: false
  of tPi, tSi, tLam:
    reprTypeMentionsMarker(t.dom, markerRefId) or
      reprTypeMentionsMarker(t.scope.bdy, markerRefId)
  of tPair:
    reprTypeMentionsMarker(t.pFst, markerRefId) or
      reprTypeMentionsMarker(t.pSnd, markerRefId) or
      reprTypeMentionsMarker(t.pScope.bdy, markerRefId)
  of tApp:
    reprTypeMentionsMarker(t.fn, markerRefId) or
      reprTypeMentionsMarker(t.arg, markerRefId)
  of tFst, tSnd, tAbsurd:
    reprTypeMentionsMarker(t.sub, markerRefId)
  of tLet:
    reprTypeMentionsMarker(t.letVal, markerRefId) or
      reprTypeMentionsMarker(t.letTy, markerRefId) or
      reprTypeMentionsMarker(t.letScope.bdy, markerRefId)
  of tMeta:
    t.metaSpine.anyIt(reprTypeMentionsMarker(it, markerRefId))
  of tPrim:
    reprTypeMentionsMarker(t.primTy, markerRefId)
  else: false

proc reprTypeLiveMentionsMarker(rt: ReprType, markerRefId: int): bool =
  ## Does the marker survive in a *live* position of the representation?
  ## Opaque families drop their indices, so mentions there are harmless;
  ## only `Vec` length indices (checked at the boundary) are live.
  case rt.kind
  of repSeq:
    rt.isVector and reprTypeMentionsMarker(rt.index, markerRefId)
  of repSigma:
    rt.sigmaFields.anyIt(reprTypeLiveMentionsMarker(it, markerRefId))
  of repFunc:
    reprTypeLiveMentionsMarker(rt.funcDom[], markerRefId) or
      reprTypeLiveMentionsMarker(rt.funcCod[], markerRefId)
  else: false

const sigmaMarkerRefId = -401
  ## Impossible refId used as the Sigma-bound-variable marker when opening
  ## a `tSi` codomain for representation selection (issue #401). `subst`
  ## leaves `tR` nodes alone, so the marker is never shifted or dropped.

proc reprTypeOf(ctx: CodegenCtx, t: Term): ReprType =
  ## The host representation of a binder domain or result type: an atomic
  ## `tR` in the int fragment, a fully-applied `Vec`/`List`/`Option`
  ## family over int elements, a concrete `runtimeType` mapping used as an
  ## identity representation (applied families drop their indices), or a
  ## dependent `Sig` over representable components (the host tuple).
  ## Raises CgUnsupported otherwise. The check is structural only:
  ## length-index terms are validated when compiled (entry check), never
  ## here.
  if t.isNil:
    raise newException(CgUnsupported, "nil type")
  if t.kind == tR:
    let k = ctx.reprKindOf(t.refId)
    if k == repOpaque:
      return ReprType(kind: repOpaque,
                      hostType: copyNimTree(ctx.reps[t.refId].nimType))
    if k != repInt:
      raise newException(CgUnsupported,
        "unapplied family outside the representation fragment")
    return ReprType(kind: repInt)
  if t.kind == tSi:
    # Issue #401: `Sig(x: A, B)` maps to the host tuple of the component
    # representations. The codomain is opened with the bound variable
    # replaced by a marker; the marker may survive only in dropped index
    # positions (opaque families) — a live index (a `Vec` length) mentioning
    # the bound value has no host denotation without a runtime check the
    # tuple boundary cannot express, so it is honestly rejected.
    let first = ctx.reprTypeOf(t.dom)
    let marker = Term(kind: tR, refId: sigmaMarkerRefId)
    let opened = subst(t.scope.bdy, 0, marker)
    let second = ctx.reprTypeOf(opened)
    if reprTypeLiveMentionsMarker(second, sigmaMarkerRefId):
      raise newException(CgUnsupported,
        "Sigma codomain mentions the bound value in a live index position")
    return ReprType(kind: repSigma, sigmaFields: @[first, second])
  if t.kind == tPi:
    # Issue #407 slice 3: a function type denotes a `{.closure.}` proc
    # type. A quantity-0 binder has no host denotation inside a function
    # type (its argument is erased at every call site), so it is honestly
    # rejected rather than silently dropped from the proc type. The
    # codomain's dependence on the bound value is erased exactly as for
    # `Sig`: a live index position mentioning it has no host denotation
    # and is honestly rejected.
    if t.qty == q0:
      raise newException(CgUnsupported,
        "quantity-0 function domain has no host representation")
    let domRt = ctx.reprTypeOf(t.dom)
    let marker = Term(kind: tR, refId: sigmaMarkerRefId)
    let opened = subst(t.scope.bdy, 0, marker)
    let codRt = ctx.reprTypeOf(opened)
    if reprTypeLiveMentionsMarker(codRt, sigmaMarkerRefId):
      raise newException(CgUnsupported,
        "function codomain mentions the bound value in a live index position")
    return ReprType(kind: repFunc, funcDom: boxRepr(domRt),
                      funcCod: boxRepr(codRt))
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
    if m.isOpaqueIdentityMapping:
      # Issue #401: an applied family with a concrete `runtimeType`
      # mapping denotes the declared host type for every index tuple —
      # `Chan s` is `PaxosChannel` for all `s`. The indices are dropped
      # from the host signature; the mapping itself is the trust anchor
      # (docs/trust-model.md). Arity is guaranteed by the checked term.
      return ReprType(kind: repOpaque,
                      hostType: copyNimTree(m.nimType))
    raise newException(CgUnsupported,
      "family outside the representation fragment")
  raise newException(CgUnsupported, "type outside the representation fragment")

proc nimReprType*(rt: ReprType): NimNode =
  ## The Nim type AST for one representation-typed signature position.
  case rt.kind
  of repInt: ident"int"
  of repSeq: newTree(nnkBracketExpr, ident"seq", ident"int")
  of repOption: newTree(nnkBracketExpr, ident"Option", ident"int")
  of repOpaque: copyNimTree(rt.hostType)
  of repSigma:
    # The host tuple of the component representations. `nnkTupleConstr`
    # matches what the wrapper layer's `runtimeNimType` produces for `Sig`,
    # so the identity-boundary check compares like with like.
    var tup = newNimNode(nnkTupleConstr)
    for f in rt.sigmaFields: tup.add(nimReprType(f))
    tup
  of repFunc:
    # Issue #407 slice 3: flatten curried binders into one multi-parameter
    # `{.closure.}` proc type. This matches both the closures
    # `cgReprElimClosure` emits (one parameter per missing argument) and
    # the uncurried compiled defs (Nim converts a `nimcall` proc to a
    # `{.closure.}` proc type of the same shape implicitly).
    var doms: seq[ReprType] = @[]
    var cur = rt
    while cur.kind == repFunc:
      doms.add(cur.funcDom[])
      cur = cur.funcCod[]
    var formal = newNimNode(nnkFormalParams)
    formal.add(nimReprType(cur))
    for i, d in doms:
      formal.add(newIdentDefs(genSym(nskParam, "repFnArg" & $i),
                             nimReprType(d), newEmptyNode()))
    var pragmas = newNimNode(nnkPragma)
    pragmas.add(ident"closure")
    newTree(nnkProcTy, formal, pragmas)

proc nimTypeName*(n: NimNode): string =
  ## Best-effort rendering of a type AST for the tier report. `$` on a raw
  ## macro node fails for composite kinds (e.g. `nnkBracketExpr` like
  ## `TransportResult[int]`), so render the common shapes structurally.
  if n.isNil: return "?"
  case n.kind
  of nnkIdent, nnkSym: $n
  of nnkBracketExpr:
    if n.len == 0: return "?"
    nimTypeName(n[0]) & "[" &
      n[1 .. ^1].mapIt(nimTypeName(it)).join(", ") & "]"
  of nnkTupleTy:
    "(" & toSeq(n.children).mapIt(
      if it.kind == nnkIdentDefs and it.len >= 2:
        toSeq(it[0 ..< it.len - 2]).mapIt(nimTypeName(it)).join("/") &
          ": " & nimTypeName(it[^2])
      else:
        nimTypeName(it)).join(", ") & ")"
  else:
    try: $n
    except: "?"

proc reprTypeName*(rt: ReprType): string =
  ## The Nim type name for the tier report (issue #386): `int`, `seq[int]`,
  ## `Option[int]`, the declared host type, or the parenthesized host
  ## tuple.
  case rt.kind
  of repInt: "int"
  of repSeq: "seq[int]"
  of repOption: "Option[int]"
  of repOpaque: nimTypeName(rt.hostType)
  of repSigma: "(" & rt.sigmaFields.mapIt(reprTypeName(it)).join(", ") & ")"
  of repFunc:
    var doms: seq[string] = @[]
    var cur = rt
    while cur.kind == repFunc:
      doms.add(reprTypeName(cur.funcDom[]))
      cur = cur.funcCod[]
    "(" & doms.join(", ") & ") -> " & reprTypeName(cur) & " {.closure.}"

proc reprSigSummary*(sig: seq[ReprType]): string =
  ## One-line signature summary for the codegen tier report (issue #401):
  ## names the representation kind at every signature position, e.g.
  ## `(int, PaxosChannel (opaque)) -> (PaxosPromise, PaxosChannel) (dependent Sigma)`.
  proc posName(rt: ReprType): string =
    let base = reprTypeName(rt)
    case rt.kind
    of repOpaque: base & " (opaque)"
    of repSigma: base & " (dependent Sigma)"
    of repFunc: base & " (function)"
    else: base
  if sig.len == 0: return "()"
  "(" & sig[0 ..< ^1].mapIt(posName(it)).join(", ") & ") -> " &
    posName(sig[^1])

proc sameNimTypeName(a, b: NimNode): bool =
  ## Structural equality of two Nim type ASTs for the wrapper
  ## identity-boundary check: kinds must agree (`nnkIdent`/`nnkSym` are
  ## interchangeable when they spell the same name), children recurse.
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind in {nnkIdent, nnkSym} and b.kind in {nnkIdent, nnkSym}:
    return $a == $b
  if a.kind != b.kind or a.len != b.len: return false
  if a.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
      nnkInt64Lit, nnkUIntLit..nnkUInt64Lit}:
    return a.intVal == b.intVal
  if a.kind == nnkStrLit: return a.strVal == b.strVal
  for i in 0 ..< a.len:
    if not sameNimTypeName(a[i], b[i]): return false
  true

proc nimTypeMatchesRepr*(n: NimNode, rt: ReprType): bool

proc sigmaFieldsMatch(n: NimNode, fields: seq[ReprType]): bool =
  for i in 0 ..< n.len:
    let field = if n.kind == nnkTupleTy and n[i].kind == nnkIdentDefs:
      n[i][^2] else: n[i]
    if not nimTypeMatchesRepr(field, fields[i]): return false
  true

proc nimTypeMatchesRepr*(n: NimNode, rt: ReprType): bool =
  ## Does the surface Nim type AST denote the repr-tier representation?
  ## Structural match (issue #330 v3, extended by #401): the wrapper
  ## identity-boundary check compares the declared formals/result against
  ## the repr signature threaded through `compileBlockProcs`, so a wrapper
  ## whose surface types disagree with the compiled repr proc keeps the
  ## Value path instead of mis-calling it.
  case rt.kind
  of repInt:
    n.kind in {nnkIdent, nnkSym} and $n == "int"
  of repSeq:
    n.kind == nnkBracketExpr and n.len == 2 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "seq" and
      n[1].kind in {nnkIdent, nnkSym} and $n[1] == "int"
  of repOption:
    n.kind == nnkBracketExpr and n.len == 2 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "Option" and
      n[1].kind in {nnkIdent, nnkSym} and $n[1] == "int"
  of repOpaque:
    sameNimTypeName(n, rt.hostType)
  of repSigma:
    # The wrapper layer renders `Sig` as an `nnkTupleConstr`; named-field
    # `nnkTupleTy` spellings of the same tuple also match structurally.
    (n.kind == nnkTupleConstr or n.kind == nnkTupleTy) and
      n.len == rt.sigmaFields.len and sigmaFieldsMatch(n, rt.sigmaFields)
  of repFunc:
    # Issue #407 slice 3: a surface `proc (d1: T1, ..., dn: Tn): TR
    # {.closure.}` denotes the flattened function representation. The
    # closure pragma is required so a plain `nimcall` surface type does
    # not silently match.
    if n.kind != nnkProcTy or n.len != 2: return false
    var doms: seq[ReprType] = @[]
    var cur = rt
    while cur.kind == repFunc:
      doms.add(cur.funcDom[])
      cur = cur.funcCod[]
    let formal = n[0]
    if formal.kind != nnkFormalParams or formal.len != doms.len + 1:
      return false
    if not nimTypeMatchesRepr(formal[0], cur): return false
    for i, d in doms:
      let idef = formal[i + 1]
      if idef.kind != nnkIdentDefs or idef.len != 3: return false
      if not nimTypeMatchesRepr(idef[1], d): return false
    let pragmas = n[1]
    if pragmas.kind != nnkPragma: return false
    for p in pragmas:
      if p.kind in {nnkIdent, nnkSym} and $p == "closure": return true
    false

proc reprSigOfType*(ctx: CodegenCtx, ty: Term): seq[ReprType] =
  ## Representation types of a Pi telescope's binder domains (outermost
  ## first), followed by the result type. Quantity-0 binders are erased
  ## from the host signature. Raises CgUnsupported when anything else is
  ## outside the fragment.
  var t = ty
  while t != nil and t.kind == tPi:
    if t.qty != q0:
      # Issue #386: a binder domain outside the representation fragment
      # keeps the established "non-atomic binder domain" diagnostic.
      # Issue #401: chain the underlying reason instead of discarding it,
      # so the report names the real cause.
      try: result.add(ctx.reprTypeOf(t.dom))
      except CgUnsupported as e:
        raise newException(CgUnsupported,
          "non-atomic binder domain (" & e.msg & ")")
    t = t.scope.bdy
  result.add(ctx.reprTypeOf(t))

proc reprSig(ctx: CodegenCtx, d: ElabDef): seq[ReprType] =
  ## Representation types of the def's Pi-binder domains (outermost
  ## first), followed by the result type. Quantity-0 binders are erased
  ## from the host signature. Raises CgUnsupported when anything else is
  ## outside the fragment.
  ctx.reprSigOfType(d.tyTm)

proc classifyRuntimeClosure*(ctx: CodegenCtx, localDefs, allDefs: seq[ElabDef],
                             globals: Globals,
                             explicitCompileTimeOnly: HashSet[string]):
    tuple[runtimeDefs: seq[ElabDef],
          compileTimeOnly: Table[string, string]] =
  ## Issue #401: split the `requireCompiled` definition closure into the
  ## runtime closure (definitions whose code may execute, or which
  ## `requireCompiled` must honestly reject) and compile-time-only
  ## definitions (type-level computation never evaluated at runtime, e.g.
  ## the `Session`-valued protocol constructors).
  ##
  ## A local definition is compile-time-only when its type is
  ## outside the representation fragment AND it is actually referenced
  ## AND every reference is type-level: from a type position (a binder
  ## domain, result type, or `let` annotation of some definition) or from
  ## the body of a type-level definition (a definition whose own type is
  ## unrepresentable, e.g. a `Session`-building body). In particular an
  ## unrepresentable definition referenced from nowhere — or from a
  ## runtime term position — is NOT automatically compile-time-only: it
  ## stays in the runtime closure so strict codegen rejects it with the real
  ## `CgUnsupported` reason instead of silently excluding it. An explicit
  ## `compileTimeOnly` marker is a checked opt-out, but runtime callers are
  ## rejected.
  ##
  ## The runtime closure seeds from local definitions with representable
  ## types — only those can a runtime caller (compiled code or a Nim
  ## wrapper) invoke — plus the honestly-rejected unrepresentable ones,
  ## and follows runtime references through erased bodies, skipping type
  ## positions. Erasure failures fall back to the unerased body
  ## (conservative: every reference counts as a runtime reference).
  # With no block-local definitions there is no runtime root and no local
  # definition to mark compile-time-only. The closure is empty regardless of
  # the imported definitions, so avoid erasing every imported body just to
  # discover that fact (large proof-heavy libraries make this especially
  # expensive).
  if localDefs.len == 0 and explicitCompileTimeOnly.len == 0:
    return (runtimeDefs: @[], compileTimeOnly: initTable[string, string]())
  var defsByRefId = initTable[int, ElabDef]()
  for d in allDefs:
    if d.name in globals and not globals[d.name].tm.isNil and
        globals[d.name].tm.kind == tR and globals[d.name].tm.refIsDefn:
      defsByRefId[globals[d.name].tm.refId] = d
  # Representability of each definition's type.
  var typeUnrep = initTable[string, string]()  # def name -> reason
  for d in localDefs:
    if d.name in globals and not globals[d.name].tm.isNil and
        globals[d.name].tm.kind == tR and globals[d.name].tm.refIsDefn:
      try:
        discard ctx.reprSigOfType(d.tyTm)
      except CgUnsupported as e:
        typeUnrep[d.name] = e.msg
  # Reference census: for every referenced refId, the (referencer name,
  # fromType) pairs, where fromType=true means the reference occurs in the
  # referencer's declared type (a type position).
  var referencers = initTable[int, seq[tuple[name: string, fromType: bool]]]()
  for d in allDefs:
    if d.name notin globals or globals[d.name].tm.isNil or
        globals[d.name].tm.kind != tR or not globals[d.name].tm.refIsDefn:
      continue
    if not d.tyTm.isNil:
      for refId in collectReferencedRefIds(d.tyTm):
        referencers.mgetOrPut(refId, @[]).add((d.name, true))
    if d.tmTm.isNil: continue
    var body: Term
    try: body = eraseQ0Arguments(d.tmTm)
    except ValueError: body = d.tmTm
    var acc = initTable[int, bool]()
    collectRuntimeRefIds(body, acc)
    for refId in acc.keys:
      referencers.mgetOrPut(refId, @[]).add((d.name, false))
  var compileTimeOnly = initTable[string, string]()
  for d in localDefs:
    if d.name in explicitCompileTimeOnly:
      compileTimeOnly[d.name] = "explicitly marked compileTimeOnly"
  for name in explicitCompileTimeOnly:
    if name notin globals or globals[name].tm.isNil or
        globals[name].tm.kind != tR:
      raise newException(CgUnsupported,
        "compileTimeOnly names no checked definition: " & name)
  for d in localDefs:
    if d.name in explicitCompileTimeOnly: continue
    if ctx.isInlineGenericDef(d):
      # An abstract generic helper can disappear only when a representable
      # caller gives the compiler a concrete call site to specialize. An
      # unused/unreferenced generic definition remains a strict-mode error.
      let refId = globals[d.name].tm.refId
      let refs = referencers.getOrDefault(refId, @[])
      var hasRuntimeCaller = false
      for (rName, fromType) in refs:
        if not fromType and rName != d.name and
            not typeUnrep.hasKey(rName):
          hasRuntimeCaller = true
          break
      if hasRuntimeCaller:
        compileTimeOnly[d.name] =
          "generic helper is specialized at compiled call sites"
        continue
    let reason = typeUnrep.getOrDefault(d.name, "")
    if reason == "": continue  # representable: a runtime seed candidate
    let refId = globals[d.name].tm.refId
    let refs = referencers.getOrDefault(refId, @[])
    if refs.len == 0: continue  # referenced from nowhere: honestly reject
    var allTypeLevel = true
    for (rName, fromType) in refs:
      if fromType: continue
      if typeUnrep.hasKey(rName): continue  # body of a type-level def
      allTypeLevel = false
      break
    if allTypeLevel:
      compileTimeOnly[d.name] = reason
  # An explicit opt-out may be referenced by another type-only definition,
  # but never by a definition whose body belongs to the runtime closure.
  for name in explicitCompileTimeOnly:
    let refId = globals[name].tm.refId
    for (referencer, fromType) in referencers.getOrDefault(refId, @[]):
      if fromType or referencer in compileTimeOnly:
        continue
      raise newException(CgUnsupported,
        "compileTimeOnly definition '" & name &
        "' is referenced by runtime definition '" & referencer & "'")
  var included = initTable[int, bool]()
  var pending: seq[int] = @[]
  for d in localDefs:
    if d.name in globals and not globals[d.name].tm.isNil and
        globals[d.name].tm.kind == tR and globals[d.name].tm.refIsDefn:
      let refId = globals[d.name].tm.refId
      # Representable definitions are runtime seeds; unrepresentable
      # non-compile-time-only definitions are included so `requireCompiled`
      # rejects them with the real reason instead of dropping them.
      if d.name notin compileTimeOnly:
        if not included.getOrDefault(refId, false):
          included[refId] = true
          pending.add(refId)
  var cursor = 0
  while cursor < pending.len:
    let refId = pending[cursor]
    inc cursor
    if refId notin defsByRefId: continue
    let d = defsByRefId[refId]
    if d.tmTm.isNil: continue
    var body: Term
    try: body = eraseQ0Arguments(d.tmTm)
    except ValueError: body = d.tmTm
    var acc = initTable[int, bool]()
    collectRuntimeRefIds(body, acc)
    for dependencyId in acc.keys:
      if dependencyId in defsByRefId and
          defsByRefId[dependencyId].name notin compileTimeOnly and
          not included.getOrDefault(dependencyId, false):
        included[dependencyId] = true
        pending.add(dependencyId)
  var runtimeDefs: seq[ElabDef] = @[]
  for d in allDefs:
    if d.name in globals and not globals[d.name].tm.isNil and
        globals[d.name].tm.kind == tR and
        included.getOrDefault(globals[d.name].tm.refId, false):
      runtimeDefs.add(d)
  (runtimeDefs, compileTimeOnly)


proc cgRepr(ctx: var CodegenCtx, t: Term, env: seq[NimNode]): NimNode  # forward
proc cgReprElim(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                env: seq[NimNode]): NimNode  # forward
proc cgReprElimClosure(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                       env: seq[NimNode]): NimNode  # forward
proc cgReprCtor(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                env: seq[NimNode]): NimNode  # forward

proc sameReprType(a, b: ReprType): bool =
  ## Structural equality of two representation types: same host Nim type.
  ## Vector length indices are runtime values, not part of the host type,
  ## so only the vector flag is compared.
  if a.kind != b.kind: return false
  case a.kind
  of repInt: true
  of repSeq: a.isVector == b.isVector
  of repOption: true
  of repOpaque: sameNimTypeName(a.hostType, b.hostType)
  of repSigma:
    a.sigmaFields.len == b.sigmaFields.len and
      toSeq(0 ..< a.sigmaFields.len).allIt(
        sameReprType(a.sigmaFields[it], b.sigmaFields[it]))
  of repFunc:
    sameReprType(a.funcDom[], b.funcDom[]) and
      sameReprType(a.funcCod[], b.funcCod[])

proc flattenFuncType(rt: ReprType): tuple[doms: seq[ReprType], cod: ReprType] =
  ## The flattened reading of a (possibly curried) function representation:
  ## `repFunc(d1, repFunc(d2, R))` is `proc (d1, d2): R {.closure.}`.
  result.doms = @[]
  var cur = rt
  while cur.kind == repFunc:
    result.doms.add(cur.funcDom[])
    cur = cur.funcCod[]
  result.cod = cur

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
      if appArgs.len < rh.nargs:
        # Issue #407 slice 2: a partially-applied eliminator eta-expands
        # into a typed closure proc instead of falling back.
        return cgReprElimClosure(ctx, rh, appArgs, env)
      return cgReprElim(ctx, rh, appArgs, env)
    if rh.kind == cgkCtor:
      return cgReprCtor(ctx, rh, appArgs, env)
    if rh.kind == cgkPostulate and head.refId in ctx.postulateReprAdapters:
      # Issue #409 slice 3: a fully-applied call to a
      # `bindPostulateValue`-bound postulate whose type arguments match an
      # emitted repr-tier adapter becomes a direct call of the repr
      # forwarder. Value arguments compile in the repr tier; codecs run
      # only on the adapter's value boundary (type binders are erased,
      # their witnesses baked into the Value-tier adapter it calls).
      # Anything else (partial application, non-matching instantiation)
      # falls through to the existing paths below.
      for adapter in ctx.postulateReprAdapters[head.refId]:
        if appArgs.len != adapter.isTypeBinder.len: continue
        var keys: seq[string] = @[]
        var ok = true
        for i in 0 ..< appArgs.len:
          if adapter.isTypeBinder[i]:
            let k = postulateTypeArgKey409(ctx, appArgs[i])
            if k.len == 0:
              ok = false
              break
            keys.add(k)
        if not ok: continue
        if keys.join(";") != adapter.typeKey: continue
        var call = newCall(ident(adapter.procName))
        for i in 0 ..< appArgs.len:
          if not adapter.isTypeBinder[i]:
            call.add(cgRepr(ctx, appArgs[i], env))
        return call
    if rh.kind in {cgkDefn, cgkPostulate} and head.refId in ctx.reprProcs:
      # Issue #401: a bound postulate with an emitted forwarder (see
      # `compilePostulateProcRepr`) is called directly, like a compiled
      # definition. A postulate without a forwarder stays outside the
      # fragment (the caller falls back to the Phase 1 backend).
      let qtys = if rh.kind == cgkPostulate:
        ctx.reprPostulateQtys.getOrDefault(head.refId, @[])
      else: rh.piQuantities
      let calleeSig = ctx.reprProcs[head.refId].sig
      var args: seq[NimNode] = @[]
      var argIdx = 0
      var sigPos = 0
      for qty in qtys:
        if argIdx >= appArgs.len: break
        if qty != q0:
          if sigPos < calleeSig.len - 1:
            let formalRt = calleeSig[sigPos]
            let argTm = appArgs[argIdx]
            if formalRt.kind == repFunc and argTm.kind == tR and
                argTm.refId in ctx.reprProcs:
              # Issue #407 slice 3: a bare compiled definition at a
              # function-typed formal. The emitted proc is uncurried; the
              # formal is the flattened closure type. Nim converts a
              # `nimcall` proc to the `{.closure.}` type implicitly only
              # when the shapes agree — anything else would be a hard Nim
              # type error for the whole block, so it is an honest named
              # fallback instead (eta-expansion of def references is future
              # work).
              let aSig = ctx.reprProcs[argTm.refId].sig
              let (doms, cod) = flattenFuncType(formalRt)
              var ok = aSig.len - 1 == doms.len and
                sameReprType(aSig[^1], cod)
              if ok:
                for i in 0 ..< doms.len:
                  if not sameReprType(aSig[i], doms[i]):
                    ok = false
                    break
              if not ok:
                raise newException(CgUnsupported,
                  "passing compiled definition '" &
                  ctx.refs[argTm.refId].name &
                  "' as a function value needs eta-expansion (outside the " &
                  "representation fragment)")
          args.add(cgRepr(ctx, appArgs[argIdx], env))
          inc sigPos
        inc argIdx
      if argIdx != appArgs.len:
        raise newException(CgUnsupported,
          "compiled repr call to '" & rh.name & "' has mismatched arity")
      var call = newCall(ident(ctx.reprProcs[head.refId].name))
      for arg in args: call.add(arg)
      return call
    if rh.kind == cgkDefn and head.refId in ctx.inlineGenericDefs:
      # Specialize leading universe binders with the static type arguments,
      # then beta-reduce the remaining lambda spine in the caller's repr.
      let genericDef = ctx.inlineGenericDefs[head.refId]
      var genericTy = genericDef.tyTm
      var genericBody = genericDef.tmTm
      var specializedArgs = appArgs
      while not genericTy.isNil and genericTy.kind == tPi and
          not genericTy.dom.isNil and
          (genericTy.dom.kind == tType or
           (genericTy.dom.kind == tR and
            genericTy.dom.refId in ctx.refs and
            ctx.refs[genericTy.dom.refId].name == "Univ")):
        if genericBody.isNil or genericBody.kind != tLam or
            specializedArgs.len == 0:
          raise newException(CgUnsupported,
            "generic helper '" & rh.name & "' has an incomplete type application")
        genericBody = subst(genericBody.scope.bdy, 0, specializedArgs[0])
        specializedArgs.delete(0)
        genericTy = genericTy.scope.bdy
      try:
        head = eraseQ0Arguments(genericBody)
      except ValueError as e:
        raise newException(CgUnsupported,
          "generic helper '" & rh.name & "' cannot be inlined: " & e.msg)
      appArgs = specializedArgs
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

proc dpsRebuildHead(ctx: CodegenCtx, body: Term): Term =
  ## #331: recognize the cons-rebuild shape `cons A [n] xHead ih`, where
  ## the tail is exactly the fold accumulator (`ih`, de Bruijn 0 in the
  ## cons-case scope) and the head mentions neither the accumulator nor
  ## the materialized tail (`tl`/`xs2`, de Bruijn 1). The vector/list
  ## distinction follows the cons's own family (read off the constructor),
  ## not the enclosing eliminator. Returns the head term, or nil when the
  ## shape does not apply (the caller keeps the allocating fold).
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
  if not (m.isRuntimeVector or m.isRuntimeList):
    return nil
  let consIsVec = m.isRuntimeVector
  var appArgs: seq[Term] = @[]
  for i in countdown(revArgs.high, 0):
    appArgs.add(revArgs[i])
  let (xHead, tail) =
    if consIsVec:
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

proc dpsFilterShape(ctx: CodegenCtx, body: Term):
    tuple[cond, head: Term] =
  ## #331: recognize the conditional-cons (filter) shape
  ##   `boolElim motive (cons A [i] xHead ih) ih cond`
  ## in the cons-case body, where the true branch is the cons-rebuild shape
  ## (`dpsRebuildHead`), the false branch is exactly the accumulator
  ## (`ih`, de Bruijn 0), and the condition mentions neither the
  ## accumulator nor the materialized tail (`termUsesInnerBinder(cond, 2)`
  ## is false; it may mention the head `x` and, for Vec, the index `i`).
  ## Returns (cond, head), or (nil, nil) when the shape does not apply
  ## (the caller keeps the allocating fold).
  ##
  ## Soundness note: as with the unconditional rebuild, the destination is
  ## freshly allocated and the initial accumulator is only read, so the
  ## transform is valid for any `ih` quantity — not gated on linearity.
  result = (nil, nil)
  var fn = body
  var revArgs: seq[Term] = @[]
  while fn.kind == tApp:
    revArgs.add(fn.arg)
    fn = fn.fn
  if fn.kind != tR or fn.refId notin ctx.refs:
    return
  let rh = ctx.refs[fn.refId]
  if rh.kind != cgkElim or rh.name != "boolElim":
    return
  var appArgs: seq[Term] = @[]
  for i in countdown(revArgs.high, 0):
    appArgs.add(revArgs[i])
  # `boolElim motive t f b`: true-branch, false-branch, scrutinee.
  if appArgs.len != 4:
    return
  let tBranch = appArgs[1]
  let fBranch = appArgs[2]
  let cond = appArgs[3]
  if fBranch.isNil or fBranch.kind != tV or fBranch.idx != 0:
    return
  let head = dpsRebuildHead(ctx, tBranch)
  if head.isNil:
    return
  if termUsesInnerBinder(cond, 2):
    return
  result = (cond, head)

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

proc cgDpsFilterBlock(xsCode, nilCode, condCode, headCode: NimNode,
                      kSym, xSym, iSym: NimNode): NimNode =
  ## #331 destination-passing fold for the conditional-cons (filter) shape:
  ## the result length is not known statically, so the destination is
  ## allocated with capacity `xs.len + acc0.len` and a write pointer `w`
  ## tracks the kept prefix. Per iteration the condition is tested; on
  ## true the head is written at `w` and `w` advances, on false the write
  ## is skipped. Afterwards the initial accumulator is copied at offset
  ## `w` and the destination is truncated to `w + acc0.len`. One
  ## allocation and O(n) element writes replace the per-step `@[x] & acc`
  ## allocation of the plain fold.
  ##
  ## Iteration runs left-to-right (`0 ..< m`), unlike the unconditional
  ## `cgDpsFoldBlock`'s right-to-left order: the write pointer needs the
  ## kept elements in source order. The order difference is unobservable —
  ## the representation fragment is pure and total (primitive arithmetic,
  ## structural eliminator folds over finite data, constructors), so
  ## neither divergence nor effects can distinguish the orders, and the
  ## interpreter/Phase-1 twins agree on values either way.
  let xsSym = genSym(nskLet, "cgDpsFXs")
  let acc0Sym = genSym(nskLet, "cgDpsFAcc0")
  let mSym = genSym(nskLet, "cgDpsFM")
  let dstSym = genSym(nskVar, "cgDpsFDst")
  let wSym = genSym(nskVar, "cgDpsFW")
  let jSym = genSym(nskForVar, "cgDpsFJ")
  var stmts = newStmtList()
  stmts.add(newLetStmt(xsSym, xsCode))
  stmts.add(newLetStmt(acc0Sym, nilCode))
  stmts.add(newLetStmt(mSym, newCall(bindSym"len", xsSym)))
  stmts.add(newVarStmt(dstSym,
    newTree(nnkCall,
      newTree(nnkBracketExpr, ident"newSeq", ident"int"),
      newTree(nnkInfix, ident"+", mSym,
        newCall(bindSym"len", acc0Sym)))))
  stmts.add(newVarStmt(wSym, newLit(0)))
  var loopBody = newStmtList()
  if not iSym.isNil:
    loopBody.add(newLetStmt(iSym,
      newTree(nnkInfix, ident"-",
        newTree(nnkInfix, ident"-", mSym, kSym),
        newLit(1))))
  loopBody.add(newLetStmt(xSym,
    newTree(nnkBracketExpr, xsSym, kSym)))
  var thenBody = newStmtList()
  thenBody.add(newTree(nnkAsgn,
    newTree(nnkBracketExpr, dstSym, wSym), headCode))
  thenBody.add(newCall(ident"inc", wSym))
  loopBody.add(newTree(nnkIfStmt,
    newTree(nnkElifBranch,
      newTree(nnkInfix, ident"!=", condCode, newLit(0)), thenBody)))
  stmts.add(newTree(nnkForStmt, kSym,
    newTree(nnkInfix, ident"..<",
      newLit(0), mSym),
    loopBody))
  var copyBody = newStmtList()
  copyBody.add(newTree(nnkAsgn,
    newTree(nnkBracketExpr, dstSym,
      newTree(nnkInfix, ident"+", wSym, jSym)),
    newTree(nnkBracketExpr, acc0Sym, jSym)))
  stmts.add(newTree(nnkForStmt, jSym,
    newTree(nnkInfix, ident"..<",
      newLit(0), newCall(bindSym"len", acc0Sym)),
    copyBody))
  stmts.add(newCall(
    newTree(nnkDotExpr, dstSym, ident"setLen"),
    newTree(nnkInfix, ident"+", wSym,
      newCall(bindSym"len", acc0Sym))))
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
  ## instead of per-step `@[x] & acc` allocation. The conditional-cons
  ## (filter) shape `boolElim motive (cons A xHead ih) ih cond` (see
  ## `dpsFilterShape`) compiles to the same destination with a write
  ## pointer: the condition is tested per iteration and only kept heads
  ## are written. The destination is fresh and the initial accumulator is
  ## only read, so both transforms are sound for any `ih` quantity (not
  ## gated on linearity).
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
  let dpsHead = dpsRebuildHead(ctx, ihLam.scope.bdy)
  if not dpsHead.isNil:
    # #331 destination-passing fold: de Bruijn V0 = ih, V1 = tl are absent
    # by the shape check (the empty nodes are never referenced), V2 = x.
    let headCode = cgRepr(ctx, dpsHead,
      @[newEmptyNode(), newEmptyNode(), xSym] & env)
    cgDpsFoldBlock(xsCode, nilCode, headCode, kSym, xSym, nil)
  else:
    let (filtCond, filtHead) = dpsFilterShape(ctx, ihLam.scope.bdy)
    if not filtHead.isNil:
      # #331 destination-passing filter: cond and head may mention only x
      # (V2); V0 = ih, V1 = tl are absent by the shape check.
      let condCode = cgRepr(ctx, filtCond,
        @[newEmptyNode(), newEmptyNode(), xSym] & env)
      let headCode = cgRepr(ctx, filtHead,
        @[newEmptyNode(), newEmptyNode(), xSym] & env)
      cgDpsFilterBlock(xsCode, nilCode, condCode, headCode, kSym, xSym, nil)
    else:
      # de Bruijn: V0 = ih (innermost), V1 = tl, V2 = x; env
      # innermost-first.
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
  ## writes — instead of per-step `@[x] & acc` allocation. The
  ## conditional-cons (filter) shape
  ## `boolElim motive (cons A idx xHead ih) ih cond` (see `dpsFilterShape`)
  ## compiles to the same destination with a write pointer: the condition
  ## is tested per iteration and only kept heads are written. The
  ## destination is fresh and the initial accumulator is only read, so both
  ## transforms are sound for any `ih` quantity (not gated on linearity).
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
  let dpsHead = dpsRebuildHead(ctx, ihLam.scope.bdy)
  if not dpsHead.isNil:
    # #331 destination-passing fold: de Bruijn V0 = ih, V1 = xs2 are
    # absent by the shape check (the empty nodes are never referenced),
    # V2 = x, V3 = i.
    let headCode = cgRepr(ctx, dpsHead,
      @[newEmptyNode(), newEmptyNode(), xSym, iSym] & env)
    cgDpsFoldBlock(xsCode, nilCode, headCode, kSym, xSym, iSym)
  else:
    let (filtCond, filtHead) = dpsFilterShape(ctx, ihLam.scope.bdy)
    if not filtHead.isNil:
      # #331 destination-passing filter: cond and head may mention only x
      # (V2) and i (V3); V0 = ih, V1 = xs2 are absent by the shape check.
      let condCode = cgRepr(ctx, filtCond,
        @[newEmptyNode(), newEmptyNode(), xSym, iSym] & env)
      let headCode = cgRepr(ctx, filtHead,
        @[newEmptyNode(), newEmptyNode(), xSym, iSym] & env)
      cgDpsFilterBlock(xsCode, nilCode, condCode, headCode, kSym, xSym, iSym)
    else:
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
  ## else falls back to the Phase 1 backend via CgUnsupported.
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

proc cgReprElimClosure(ctx: var CodegenCtx, r: CgRef, appArgs: seq[Term],
                       env: seq[NimNode]): NimNode =
  ## Eta-expand a partially-applied eliminator in the repr tier (issue
  ## #407, slice 2): generate a typed `{.closure.}` Nim proc whose
  ## parameters are the missing arguments at representation-backend types
  ## and whose body is the saturated eliminator compiled by the existing
  ## match compilers. Provided value arguments are evaluated left-to-right
  ## at the creation site and captured; motive, family-parameter, and
  ## length-index positions are skipped (type-level, never evaluated — as
  ## in the saturated path). Case arguments (the step/cons/some-case
  ## lambdas) are inlined by the match compilers, never passed as values,
  ## so a partial application missing one is honestly rejected with a
  ## named reason instead of silently tiering down.
  ##
  ## Per-eliminator closure schema (positions are argument indices;
  ## application is always a prefix, so the missing arguments are a
  ## suffix):
  ##   natElim:    [motive, z: int, s: double-lambda, n: int]
  ##   boolElim:   [motive, t: int, f: int, b: int]
  ##   optionElim: [A, motive, noneC: int, someC: single-lambda, o: Option[int]]
  ##   listElim:   [A, motive, nilC: seq[int], consC: triple-lambda, xs: seq[int]]
  ##   vecElim:    [A, motive, nilC: seq[int], consC: quad-lambda, n: index, xs: seq[int]]
  var skipIdx: set[uint8]
  var synIdx: set[uint8]
  var paramTypes = initTable[int, NimNode]()
  var motiveIdx = 0
  var minProvided = 0
  var missingCaseName = ""
  let seqIntT = newTree(nnkBracketExpr, ident"seq", ident"int")
  let optIntT = newTree(nnkBracketExpr, ident"Option", ident"int")
  case r.name
  of "natElim":
    skipIdx = {0u8}; synIdx = {2u8}; motiveIdx = 0; minProvided = 3
    missingCaseName = "step case"
    paramTypes[1] = ident"int"; paramTypes[3] = ident"int"
  of "boolElim":
    skipIdx = {0u8}; synIdx = {}; motiveIdx = 0; minProvided = 1
    paramTypes[1] = ident"int"; paramTypes[2] = ident"int"
    paramTypes[3] = ident"int"
  of "optionElim":
    skipIdx = {0u8, 1u8}; synIdx = {3u8}; motiveIdx = 1; minProvided = 4
    missingCaseName = "some case"
    paramTypes[2] = ident"int"; paramTypes[4] = optIntT
  of "listElim":
    skipIdx = {0u8, 1u8}; synIdx = {3u8}; motiveIdx = 1; minProvided = 4
    missingCaseName = "cons case"
    paramTypes[2] = seqIntT; paramTypes[4] = seqIntT
  of "vecElim":
    skipIdx = {0u8, 1u8, 4u8}; synIdx = {3u8}; motiveIdx = 1; minProvided = 4
    missingCaseName = "cons case"
    paramTypes[2] = seqIntT; paramTypes[5] = seqIntT
  else:
    raise newException(CgUnsupported, "eliminator '" & r.name &
      "' has no representation-tier closure schema (falls back)")
  if appArgs.len < minProvided:
    raise newException(CgUnsupported, "eliminator '" & r.name &
      "' partially applied without its " & missingCaseName &
      ": representation-tier closures inline case bodies, so a missing " &
      missingCaseName & " is outside the fragment (falls back)")
  # The closure result representation comes from the motive's codomain,
  # exactly as checkMotiveKind establishes it for the saturated path.
  let resRt =
    try: ctx.reprTypeOf(motiveCodomain(appArgs[motiveIdx]))
    except CgUnsupported as e:
      raise newException(CgUnsupported, "eliminator '" & r.name &
        "' closure result outside the representation fragment: " & e.msg)
  # Missing non-skipped positions become proc parameters (arg order);
  # provided value positions are let-bound at creation (arg order).
  var missingPos: seq[int] = @[]
  for i in appArgs.len ..< r.nargs:
    if uint8(i) notin skipIdx: missingPos.add(i)
  var valPos: seq[int] = @[]
  for i in 0 ..< appArgs.len:
    if uint8(i) notin skipIdx and uint8(i) notin synIdx: valPos.add(i)
  let k = missingPos.len
  let v = valPos.len
  var preStmts = newStmtList()
  var letSyms = initTable[int, NimNode]()
  for i in valPos:
    let s = genSym(nskLet, "cgReprElimPart")
    preStmts.add(newLetStmt(s, cgRepr(ctx, appArgs[i], env)))
    letSyms[i] = s
  var paramSyms: seq[NimNode] = @[]
  for pos in missingPos:
    paramSyms.add(genSym(nskParam, "cgReprElimMiss"))
  # env2: innermost-first. Closure parameters are the innermost binders
  # (last missing position innermost), then the creation-site let
  # bindings, then the original environment.
  var env2 = env
  for j in 0 ..< k:
    env2 = @[paramSyms[j]] & env2
  for m in 0 ..< v:
    env2 = @[letSyms[valPos[m]]] & env2
  # fullArgs for the match compiler: provided value positions become
  # references to the creation-site bindings; provided case lambdas are
  # weakened under the new binders; missing positions become parameter
  # references; missing skipped positions get a dummy (never read).
  var fullArgs = newSeq[Term](r.nargs)
  for i in 0 ..< appArgs.len:
    if uint8(i) in skipIdx:
      fullArgs[i] = appArgs[i]
    elif uint8(i) in synIdx:
      fullArgs[i] = shiftN(appArgs[i], k + v)
    else:
      let m = valPos.find(i)
      fullArgs[i] = vv(v - 1 - m)
  for j, pos in missingPos:
    fullArgs[pos] = vv(v + (k - 1 - j))
  for i in appArgs.len ..< r.nargs:
    if uint8(i) in skipIdx:
      fullArgs[i] = tmInt(0)
  let bodyCode =
    case r.name
    of "natElim": cgReprNatElim(ctx, r, fullArgs, env2)
    of "boolElim": cgReprBoolElim(ctx, r, fullArgs, env2)
    of "optionElim": cgReprOptionElim(ctx, r, fullArgs, env2)
    of "listElim": cgReprListElim(ctx, r, fullArgs, env2)
    of "vecElim": cgReprVecElim(ctx, r, fullArgs, env2)
    else: raise newException(CgUnsupported, "unreachable")
  var lam = quote do:
    proc {.closure.} = `bodyCode`
  var formal = newNimNode(nnkFormalParams)
  formal.add(nimReprType(resRt))
  for j, pos in missingPos:
    formal.add(newIdentDefs(paramSyms[j], paramTypes[pos], newEmptyNode()))
  lam[3] = formal
  if preStmts.len == 0:
    return lam
  preStmts.add(lam)
  var blk = newNimNode(nnkBlockStmt)
  blk.add(newEmptyNode())
  blk.add(preStmts)
  blk

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

type ChainNotLiftable = object of CatchableError
  ## tryChainLift raises this when a `tLet` spine is not a liftable linear
  ## chain; the caller falls back to ordinary let emission. Distinct from
  ## CgUnsupported so a fragment failure inside a liftable chain still
  ## falls back to the Phase 1 backend.

proc isAliasHead(t: Term): bool =
  ## True when the term (through `fst`/`snd` projections) is a bare
  ## variable: its value aliases an outer buffer rather than being freshly
  ## produced, so taking ownership of it could leak mutation to whoever
  ## retains that buffer.
  var u = t
  while not u.isNil and u.kind in {tFst, tSnd}:
    u = u.sub
  not u.isNil and u.kind == tV

proc varOccursUnderBinder(t: Term): bool =
  ## True when de Bruijn index 0 occurs anywhere under a closure-forming
  ## binder in `t` (a lambda/Pi/Sigma body or pair scope). Such a use is a
  ## capture, not a straight-line consumption: the closure may be invoked
  ## zero or many times, so a single syntactic occurrence is not an
  ## exactly-once runtime use, and the chain lift must not claim it.
  ## `let` scopes propagate the flag unchanged — a let is sequencing, not
  ## capture.
  proc go(u: Term, depth: int, under: bool): bool =
    if u.isNil:
      return false
    case u.kind
    of tV:
      u.idx == depth and under
    of tLam, tSi:
      go(u.scope.bdy, depth + 1, true)
    of tPi:
      go(u.dom, depth, under) or go(u.scope.bdy, depth + 1, true)
    of tApp:
      go(u.fn, depth, under) or go(u.arg, depth, under)
    of tPair:
      go(u.pFst, depth, under) or go(u.pSnd, depth, under) or
        go(u.pScope.bdy, depth + 1, true)
    of tFst, tSnd, tAbsurd:
      go(u.sub, depth, under)
    of tLet:
      go(u.letVal, depth, under) or go(u.letScope.bdy, depth + 1, under)
    else:
      false
  go(t, 0, false)

type ChainMode = enum
  cmSeq  # every binding is a non-vector `seq` repr: move the buffer
  cmInt  # every binding is a plain `int` repr: reassign the accumulator

proc tryChainLift(ctx: var CodegenCtx, t: Term,
                  env: seq[NimNode]): NimNode =
  ## Issue #413: compile a straight-line chain of linear `let` bindings to
  ## a single Nim `var` that each step updates, instead of one fresh
  ## immutable binding per step.
  ##
  ## Two homogeneous modes. `cmSeq`: bindings over `seq[int]` (List)
  ## representations — each step moves the buffer through one `var`
  ## (`move` at the step sites); a `Vec` length index would be falsified
  ## by in-place length changes, so vectors never qualify. `cmInt`:
  ## bindings over plain `int` — one `var acc: int` reassigned per step
  ## (Aaron's 2026-10-22 scope clarification: the same transform at scalar
  ## type, for non-fold chains threaded through separately compiled
  ## definitions). Mixed or other representations fall back to ordinary
  ## lets.
  ##
  ## A binding joins the chain when: its variable is used exactly once in
  ## the remainder of the spine (the quantity-1 guarantee, checked
  ## syntactically with countVarUses — type/index positions count,
  ## conservatively); every non-head step consumes the previous variable
  ## in straight-line position (a use under a closure-forming binder is a
  ## capture, not a consumption — the closure could run any number of
  ## times); and, in `cmSeq` only, the head value is not a bare
  ## variable/projection, i.e. the buffer is freshly produced and uniquely
  ## owned, never an alias of a caller-retained buffer (the
  ## wrapper-boundary ownership rule). In `cmInt` an alias head is a free
  ## value copy and cannot leak a buffer, so it qualifies.
  ##
  ## Emission: `var cv = <head>`; each step `cv = <step with the previous
  ## variable replaced>` — `move(cv)` in `cmSeq`, plain `cv` in `cmInt`
  ## (ints are values; assignment is a register copy). The move is sound
  ## because the old buffer is dead after the step (exactly-once,
  ## straight-line use) and the step's result — a fresh `seq[int]` value
  ## — is immediately rebound. Spines that do not qualify raise
  ## ChainNotLiftable and the caller emits ordinary lets.
  var vals: seq[Term] = @[]
  var tys: seq[Term] = @[]
  var rests: seq[Term] = @[]
  var cur = t
  while not cur.isNil and cur.kind == tLet:
    vals.add(cur.letVal)
    tys.add(cur.letTy)
    rests.add(cur.letScope.bdy)
    cur = cur.letScope.bdy
  if vals.len == 0:
    raise newException(ChainNotLiftable, "not a let spine")
  var mode = cmSeq
  try:
    let rt0 = ctx.reprTypeOf(tys[0])
    if rt0.kind == repInt:
      mode = cmInt
    elif not (rt0.kind == repSeq and not rt0.isVector):
      raise newException(ChainNotLiftable,
        "binding 0 is not a liftable repr")
    for i in 1 ..< vals.len:
      let rt = ctx.reprTypeOf(tys[i])
      let ok = case mode
        of cmSeq: rt.kind == repSeq and not rt.isVector
        of cmInt: rt.kind == repInt
      if not ok:
        raise newException(ChainNotLiftable,
          "binding " & $i & " changes representation: chain ends")
  except CgUnsupported as e:
    raise newException(ChainNotLiftable,
      "representation outside fragment: " & e.msg)
  var k = 0
  for i in 0 ..< vals.len:
    if i == 0:
      if mode == cmSeq and isAliasHead(vals[0]):
        raise newException(ChainNotLiftable, "chain head aliases a variable")
    elif countVarUses(vals[i]) < 1 or varOccursUnderBinder(vals[i]):
      raise newException(ChainNotLiftable,
        "step " & $i & " does not consume the previous variable " &
        "in straight-line position")
    if countVarUses(rests[i]) != 1:
      raise newException(ChainNotLiftable,
        "binding " & $i & " is not used exactly once")
    inc k
  if k < 1:
    raise newException(ChainNotLiftable, "no liftable binding")
  let cv = genSym(nskVar, "cgChainVar")
  var stmts = newStmtList()
  stmts.add(newVarStmt(cv, cgRepr(ctx, vals[0], env)))
  # In `cmSeq` the step moves the dead buffer; in `cmInt` the previous
  # accumulator is a plain value copy.
  let prevVar = case mode
    of cmSeq: newCall(bindSym"move", cv)
    of cmInt: cv
  for i in 1 ..< k:
    stmts.add(newTree(nnkAsgn, cv, cgRepr(ctx, vals[i], @[prevVar] & env)))
  # The remainder was elaborated under all k chain binders; every one of
  # them denotes the single buffer now (the dead ones, x_0..x_{k-2}, never
  # occur — each was consumed exactly once by its step — so aliasing them
  # to cv is unobservable), and outer indices stay aligned.
  var restEnv = newSeq[NimNode](k)
  for i in 0 ..< k: restEnv[i] = cv
  stmts.add(cgRepr(ctx, rests[k-1], restEnv & env))
  var blk = newNimNode(nnkBlockStmt)
  blk.add(newEmptyNode())
  blk.add(stmts)
  blk

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
    if r.kind in {cgkDefn, cgkPostulate} and t.refId in ctx.reprProcs:
      # Issue #401: postulates with an emitted forwarder resolve like
      # compiled definitions; the enclosing `tApp` emits the direct call.
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
    elif r.kind == cgkElim:
      # Issue #407 slice 2: a bare eliminator reference. With no arguments
      # at all the motive is absent, so the closure result representation
      # cannot be established — a named diagnostic rather than the generic
      # fallback (the Phase-1 backend eta-expands it instead).
      raise newException(CgUnsupported, "bare eliminator '" & r.name &
        "' outside the representation fragment (no motive: the closure " &
        "result type cannot be established)")
    else:
      raise newException(CgUnsupported,
        "reference '" & r.name & "' outside the representation fragment")
  of tInt:
    newLit(t.intVal)
  of tNatLit:
    # Issue #93: Nat literals are definitionally suc^n(zero); on the int
    # representation they are just int literals.
    newLit(t.natLitVal)
  of tPair:
    # Issue #493: Sigma values over representation-supported components are
    # host tuples. `fst`/`snd` already project those tuples; compile the
    # matching pair constructor so Eponym Vec folds can accumulate tuples.
    let first = cgRepr(ctx, t.pFst, env)
    let second = cgRepr(ctx, t.pSnd, env)
    newTree(nnkTupleConstr, first, second)
  of tLet:
    # Issue #413: a straight-line chain of linear lets over seq or int
    # reprs becomes one mutable buffer/accumulator; anything else keeps
    # ordinary lets.
    try:
      return tryChainLift(ctx, t, env)
    except ChainNotLiftable:
      discard
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
  of tFst:
    # Issue #401: a `Sig` value is the host tuple of its components, so
    # `fst`/`snd` are tuple projections.
    let sub = cgRepr(ctx, t.sub, env)
    newTree(nnkBracketExpr, sub, newLit(0))
  of tSnd:
    let sub = cgRepr(ctx, t.sub, env)
    newTree(nnkBracketExpr, sub, newLit(1))
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

proc reprTypeHasLiveVector(rt: ReprType): bool =
  ## Does the representation contain a length-checked `Vec` anywhere,
  ## including inside a `Sig`? The entry length check is emitted only for
  ## top-level `Vec` parameters; a `Vec` nested in a tuple parameter has
  ## no check site, so it is honestly rejected (issue #401).
  case rt.kind
  of repSeq: rt.isVector
  of repSigma: rt.sigmaFields.anyIt(reprTypeHasLiveVector(it))
  of repFunc:
    reprTypeHasLiveVector(rt.funcDom[]) or reprTypeHasLiveVector(rt.funcCod[])
  else: false

proc reprTupleFieldCount(n: NimNode): int =
  if n.kind != nnkTupleTy: return -1
  for field in n:
    if field.kind == nnkIdentDefs:
      result += field.len - 2
    else:
      inc result

proc cgReprRecordTuple(ctx: var CodegenCtx, t: Term, env: seq[NimNode],
                       expected: ReprType): NimNode =
  ## Record declarations lower to an iterated Sigma ending in unit, while
  ## an explicit runtimeType mapping may expose the record as a flat Nim
  ## tuple. Flatten only that canonical pair chain at the mapped record
  ## constructor boundary; ordinary Sigma values keep their nested form.
  if expected.kind != repOpaque or expected.hostType.kind != nnkTupleTy or
      t.kind != tPair:
    return nil
  var fields: seq[Term] = @[]
  var tail = t
  while tail.kind == tPair:
    fields.add(tail.pFst)
    tail = tail.pSnd
  if tail.kind != tC or tail.c != cVoid or
      fields.len != reprTupleFieldCount(expected.hostType):
    return nil
  var tupleNode = newNimNode(nnkTupleConstr)
  for field in fields:
    tupleNode.add(cgRepr(ctx, field, env))
  tupleNode

proc cgReprRecordProjection(defName: string, env: seq[NimNode],
                            sig: seq[ReprType]): NimNode =
  ## A named record projection over a flat tuple mapping must use its
  ## declared field position, since the elaborated Sigma projections are
  ## nested while the mapped host tuple is flat.
  if sig.len != 2 or sig[0].kind != repOpaque or
      sig[0].hostType.kind != nnkTupleTy:
    return nil
  let dot = defName.rfind('.')
  if dot <= 0 or dot == defName.high: return nil
  let fieldName = defName[dot + 1 .. ^1]
  var fieldIndex = 0
  for field in sig[0].hostType:
    if field.kind == nnkIdentDefs:
      for i in 0 ..< field.len - 2:
        if $field[i] == fieldName:
          return newTree(nnkBracketExpr, env[0], newLit(fieldIndex + i))
      fieldIndex += field.len - 2
    else:
      if $field == fieldName:
        return newTree(nnkBracketExpr, env[0], newLit(fieldIndex))
      inc fieldIndex
  nil

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
    try:
      var preserveQ0Apps = initHashSet[int]()
      for refId in ctx.inlineGenericDefs.keys:
        preserveQ0Apps.incl(refId)
      eraseQ0ArgumentsPreserving(d.tmTm, preserveQ0Apps)
    except ValueError as e:
      failureReason = "quantity erasure failed: " & e.msg
      return nil
  var body = erased
  var params: seq[NimNode] = @[]
  var paramTypes: seq[NimNode] = @[]
  var paramQtys: seq[Quantity] = @[]
  var paramRts: seq[ReprType] = @[]
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
      if (rt.kind == repSigma or rt.kind == repFunc) and
          reprTypeHasLiveVector(rt):
        # A `Vec` nested in a tuple or function-typed parameter has no
        # entry-check site (checks are emitted per top-level `Vec`
        # parameter only); reject honestly rather than skip the
        # interpreter's length validation.
        failureReason =
          "Vec length inside a composite parameter has no entry check site"
        return nil
      let psym = genSym(nskParam, "cgReprArg" & $params.len)
      params.add(psym)
      paramTypes.add(nimReprType(rt))
      paramQtys.add(ty.qty)
      paramRts.add(rt)
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
    try:
      let recordProjection = cgReprRecordProjection(d.name, env, sig)
      if not recordProjection.isNil:
        recordProjection
      else:
        let recordTuple = cgReprRecordTuple(ctx, body, env, sig[^1])
        if recordTuple.isNil: cgRepr(ctx, body, env) else: recordTuple
    except CgUnsupported as e:
      failureReason = e.msg
      return nil
  var formal = newNimNode(nnkFormalParams)
  formal.add(nimReprType(sig[^1]))
  for i, psym in params:
    # Issue #413: a quantity-1 seq parameter takes ownership of its
    # argument buffer (`sink`): the caller moves the buffer in instead of
    # sharing it. `sink` is a move hint only — value semantics are
    # unchanged, and an lvalue argument is still copied by the caller, so
    # the boundary never aliases a caller-retained buffer.
    if paramQtys[i] == q1 and paramRts[i].kind == repSeq:
      formal.add(newIdentDefs(psym,
        newTree(nnkCommand, ident"sink", paramTypes[i]), newEmptyNode()))
    else:
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

proc compilePostulateProcRepr(postulateName: string, ty: Term,
                              binding: PostulateReprBinding,
                              ctx: var CodegenCtx,
                              locFile: string, locLine: int,
                              failureReason: var string): NimNode =
  ## Emit a representation-tier forwarder for a host-bound postulate:
  ## `proc eponymCompiledRepr_<name>*(p1: T1, ...): R = hostImpl(p1, ...)`.
  ## The boundary is the identity (issue #401): every formal and the
  ## result are already the host representations, so the host procedure is
  ## called directly with no `Value` allocated and no codec run. A `Sig`
  ## result is the host tuple the bound procedure returns.
  ##
  ## Returns nil when the postulate's type is outside the representation
  ## fragment, or when the representable arity disagrees with the binding's
  ## declared argument count (callers then keep the Phase 1 backend).
  ## Quantity-0 binders have no Nim formal parameters.
  let sig =
    try: ctx.reprSigOfType(ty)
    except CgUnsupported as e:
      failureReason = e.msg
      return nil
  if sig.len - 1 != binding.argCount:
    failureReason = "postulate '" & postulateName & "' has " &
      $(sig.len - 1) & " representable arguments but its host binding " &
      "declares " & $binding.argCount
    return nil
  var formal = newNimNode(nnkFormalParams)
  formal.add(nimReprType(sig[^1]))
  var argSyms: seq[NimNode] = @[]
  # Issue #413: quantities of the non-erased binders, outermost first,
  # aligned with the sig positions (reprSigOfType drops q0 binders).
  let argQtys = piQuantities(ty).filterIt(it != q0)
  for i, rt in sig[0 ..< sig.len - 1]:
    let psym = genSym(nskParam, "cgReprPostArg" & $argSyms.len)
    let rtNim = nimReprType(rt)
    # A quantity-1 seq parameter takes ownership of its argument buffer.
    let ftype = if i < argQtys.len and argQtys[i] == q1 and
        rt.kind == repSeq:
      newTree(nnkCommand, ident"sink", rtNim)
    else: rtNim
    formal.add(newIdentDefs(psym, ftype, newEmptyNode()))
    argSyms.add(psym)
  var call = newCall(copyNimTree(binding.implementation))
  for s in argSyms: call.add(s)
  var procNode = newNimNode(nnkProcDef)
  procNode.add(newTree(nnkPostfix, ident"*", ident(cgReprName(postulateName))))
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  procNode.add(formal)
  procNode.add(newEmptyNode())
  procNode.add(newEmptyNode())
  procNode.setLineInfo(LineInfo(filename: locFile, line: locLine, column: 0))
  procNode.add(call)
  procNode

proc substTypeBinders409(ty: Term, typeArgNames: seq[string],
                         globals: Globals,
                         valueDomains: var seq[Term],
                         isTypeBinder: var seq[bool]): Term =
  ## Issue #409 slice 3: walk a postulate's Pi spine outermost-first,
  ## substituting each type-binder position (domain is a universe) with
  ## the corresponding concrete type from `typeArgNames` (Pi-spine order)
  ## and dropping the binder; value-binder domains are collected fully
  ## substituted. Returns the substituted result type. Raises
  ## CgUnsupported when the spine and the instantiation disagree or a
  ## type name has no global term. `subst` (eponym_init) drops the
  ## substituted binder and shifts the rest, so kept value binders stay
  ## correctly indexed.
  var rest = ty
  var typeIdx = 0
  while not rest.isNil and rest.kind == tPi:
    let isTy = not rest.dom.isNil and rest.dom.kind == tType
    isTypeBinder.add(isTy)
    if isTy:
      if typeIdx >= typeArgNames.len:
        raise newException(CgUnsupported,
          "more type binders than instantiation type arguments")
      let tname = typeArgNames[typeIdx]
      if tname notin globals or globals[tname].tm.isNil:
        raise newException(CgUnsupported,
          "instantiation type '" & tname & "' has no global term")
      rest = subst(rest.scope.bdy, 0, globals[tname].tm)
      inc typeIdx
    else:
      valueDomains.add(rest.dom)
      rest = rest.scope.bdy
  if typeIdx != typeArgNames.len:
    raise newException(CgUnsupported,
      "fewer type binders than instantiation type arguments")
  rest

proc compileBlockProcs*(defs: seq[ElabDef], globals: Globals,
                        baseDir, src, locFile: string,
                        userLines: Table[string, int],
                        runtimeTypes: seq[HostRuntimeType] = @[],
                        postulateReprs: seq[PostulateReprBinding] = @[],
                        allDefs: seq[ElabDef] = @[],
                        rawValueAdapters: seq[RawValueAdapterSpec] = @[],
                        crossBlockImports:
                          Table[string, CrossBlockExport] =
                          initTable[string, CrossBlockExport]()):
    tuple[procs: seq[NimNode], compiled: Table[string, string],
          compiledRepr: Table[string, string],
          reprTypes: Table[string, seq[ReprType]],
          report: Table[string, CodegenReportEntry],
          exportInfo: Table[string, CrossBlockExportInfo]] =
  ## Compile every eligible block-local definition, in dependency order.
  ## Returns the emitted procs, the def-name -> Phase-1 proc-name table for
  ## wrapper rerouting, the def-name -> repr-tier proc-name table, the
  ## def-name -> repr-tier representations (params then result) for the
  ## wrapper identity-boundary check (issue #330 v3, extended by #401),
  ## the per-definition codegen report (emitted tier + why the next
  ## tier was unavailable, issue #386), and the cross-block export info
  ## (issue #408).
  ## Emission order: eliminator forward declarations, Phase-1 definition
  ## bodies, postulate forwarders, repr-tier bodies (callees first, same
  ## order), eliminator bodies.
  ## `runtimeTypes` is the block's codec mapping (issue #330 representation
  ## spec); the emitter consults it to compile bodies against host
  ## representations. Definitions outside any representation keep the
  ## Phase 1 Value backend.
  ## `postulateReprs` (issue #401) are the block's host-bound postulates;
  ## each representable one gets an `eponymCompiledRepr_<name>` forwarder
  ## calling the host procedure directly, so in-body calls from repr-tier
  ## definitions never touch the interpreter.
  ## `rawValueAdapters` (issue #409) are the statically-known
  ## instantiations of `bindPostulateValue`-bound postulates; each gets a
  ## typed adapter proc called directly by matching Value-tier call sites.
  ## `allDefs` (issue #408) is the full elaborated closure including
  ## imports; `crossBlockImports` is the compile-time registry of procs
  ## emitted by earlier eponymBlock invocations in the same compilation,
  ## keyed by `loc.source & "\x00" & name`. An import-origin definition
  ## with a registry hit is reused via direct calls — no local emission —
  ## and published in `exportInfo` for the macro to register.
  var ctx = buildCodegenCtx(globals, baseDir, src, runtimeTypes, allDefs)
  # Issue #408: resolve cross-block reuse before any emission. A registry
  # hit pre-assigns the emitted proc names on the callee's ref, so callers
  # compiled below emit direct calls; the definition itself is marked
  # emitted so the dependency order and both emission loops skip it
  # (re-emitting the deterministically-named procs would be a redefinition
  # error). An emitted proc is self-contained — it bakes its own block's
  # (baseDir, src) literals and refIds — so cross-block calls are sound.
  # The value tier reuses unconditionally (uniform
  # `eponymCompiled_<name>` convention; postulate refs resolve through the
  # *caller's* bindings, exactly like the slow path). The repr tier reuses
  # only on signature agreement with this block's representation mapping.
  var reused = initTable[string, string]()  # def name -> registry key
  var reusedReprNote = initTable[string, string]()  # def name -> repr skip note
  var reusedSig = initTable[string, seq[ReprType]]()  # def name -> agreed sig
  if crossBlockImports.len > 0:
    var defsByName = initTable[string, ElabDef]()
    for d in (if allDefs.len > 0: allDefs else: defs):
      defsByName[d.name] = d
    for refId, r in ctx.refs.pairs:
      if r.kind != cgkDefn or r.name notin defsByName: continue
      let d = defsByName[r.name]
      if d.loc.source.len == 0 or d.loc.source.startsWith("<eponymBlock>"):
        continue  # block-local: always compiled fresh
      let key = d.loc.source & "\x00" & d.name
      if key notin crossBlockImports: continue
      let e = crossBlockImports[key]
      if e.valueProc == "" and e.reprProc == "": continue
      let valueReused = e.valueProc != ""
      if valueReused:
        var rr = ctx.refs[refId]
        rr.compiledProc = e.valueProc
        ctx.refs[refId] = rr
      var reprReused = false
      if e.reprProc != "":
        var sig: seq[ReprType] = @[]
        var sigOk = true
        try: sig = ctx.reprSig(d)
        except CgUnsupported as ex:
          sigOk = false
          reusedReprNote[r.name] = "repr tier not reused: callee type not " &
            "representable in this block (" & ex.msg & ")"
        if sigOk:
          if reprSigSummary(sig) == e.sigSummary:
            ctx.reprProcs[refId] = (name: e.reprProc, arity: sig.len - 1,
                                    sig: sig)
            reusedSig[r.name] = sig
            reprReused = true
          else:
            reusedReprNote[r.name] = "repr tier not reused: signature " &
              "mismatch (this block " & reprSigSummary(sig) &
              " vs exported " & e.sigSummary & ")"
      # Only a hit that reuses at least one tier suppresses local emission.
      # A hit reusing nothing (e.g. a repr-only entry this block disagrees
      # with) falls through to normal local compilation.
      if valueReused or reprReused:
        reused[r.name] = key
  var bakedIds = initTable[int, string]()
  # Issue #409: emit one typed adapter per statically-known instantiation
  # of a `bindPostulateValue`-bound postulate. The adapter takes the
  # block's runtime bindings plus one `Value` parameter per non-type Pi
  # binder (spine order), and calls the user's
  # `(args: seq[Value], globals: Globals): Value` proc directly with the
  # baked type witnesses followed by the value arguments — no
  # `postulateValue` table lookup, no per-argument application fold. The
  # Value tier needs no codecs: values are already `Value`s. Globals come
  # from the cached `getGlobalsDir`, the same source the wrapper's
  # `bindHostValueNary` call uses.
  #
  # Slice 3 (below): a second adapter per instantiation gets the repr-tier
  # signature (`int -> int` for `debugEcho[Int]`). It encodes each
  # argument with the `intToValue`-family codecs, calls the Value-tier
  # adapter (type witnesses already baked there), and decodes the result —
  # codecs only on the value boundary. Only the int fragment is covered;
  # other representations keep the Value-tier adapter (repr-tier callers
  # fall back to Phase 1 exactly as before).
  var adapterBodies: seq[NimNode] = @[]
  for spec in rawValueAdapters:
    if spec.postulateName notin globals: continue
    let entry = globals[spec.postulateName]
    if entry.tm.isNil or entry.tm.kind != tR: continue
    let refId = entry.tm.refId
    var isTypeBinder: seq[bool] = @[]
    var sig = entry.ty
    while not sig.isNil and sig.kind == tPi:
      isTypeBinder.add(not sig.dom.isNil and sig.dom.kind == tType)
      sig = sig.scope.bdy
    var typeBinderCount = 0
    for isTy in isTypeBinder:
      if isTy: inc typeBinderCount
    if typeBinderCount != spec.typeArgNames.len: continue
    let bndSym = genSym(nskParam, "cgAdapterBindings")
    var witnessCodes: seq[NimNode] = @[]
    var witnessesOk = true
    for tname in spec.typeArgNames:
      if tname notin globals or globals[tname].tm.isNil:
        witnessesOk = false
        break
      try:
        witnessCodes.add(cg(ctx, globals[tname].tm, @[], bndSym))
      except CgUnsupported:
        witnessesOk = false
        break
    if not witnessesOk: continue
    var formal = newNimNode(nnkFormalParams)
    formal.add(bindSym"Value")
    formal.add(newIdentDefs(bndSym, bindSym"RuntimeBindings", newEmptyNode()))
    var boundaryDomains: seq[Term] = @[]
    var boundaryBinders: seq[bool] = @[]
    try:
      discard substTypeBinders409(entry.ty, spec.typeArgNames, globals,
        boundaryDomains, boundaryBinders)
    except CgUnsupported:
      boundaryDomains = @[]
    var valueParams: seq[NimNode] = @[]
    var paramIdx = 0
    for isTy in isTypeBinder:
      if not isTy:
        let psym = ident("cgAdapterArg" & $paramIdx)
        inc paramIdx
        formal.add(newIdentDefs(psym, bindSym"Value", newEmptyNode()))
        valueParams.add(psym)
    var argBracket = newNimNode(nnkBracket)
    for w in witnessCodes: argBracket.add(w)
    for vp in valueParams: argBracket.add(vp)
    let argsSeq = newTree(nnkPrefix, ident"@", argBracket)
    let globalsCall = newCall(bindSym"getGlobalsDir",
      newLit(baseDir), newLit(src))
    var adapterBody = newStmtList()
    var boundaryIndex = 0
    for i, domain in boundaryDomains:
      if i >= valueParams.len: break
      var shape = ""
      var functionExpected = false
      var hostType = ""
      if domain.kind == tPi:
        shape = "Pi"
        functionExpected = true
      elif domain.kind == tR:
        for gname, gentry in globals:
          if not gentry.tm.isNil and gentry.tm.kind == tR and
              gentry.tm.refId == domain.refId:
            shape = gname
            break
        if shape notin ["Int", "Nat", "Bool"]:
          for mapping in runtimeTypes:
            if mapping.eponymName == shape:
              hostType = mapping.nimType.repr
              break
      if shape.len > 0:
        adapterBody.add(newCall(bindSym"validatePostulateValueShape",
          valueParams[boundaryIndex], newLit(spec.postulateName),
          newLit(boundaryIndex), newLit(shape), newLit(functionExpected),
          newLit(hostType)))
      inc boundaryIndex
    adapterBody.add(newCall(copyNimTree(spec.implementation), argsSeq,
      globalsCall))
    var procNode = newNimNode(nnkProcDef)
    procNode.add(newTree(nnkPostfix, ident"*", ident(spec.procName)))
    procNode.add(newEmptyNode())
    procNode.add(newEmptyNode())
    procNode.add(formal)
    procNode.add(newEmptyNode())
    procNode.add(newEmptyNode())
    procNode.add(adapterBody)
    adapterBodies.add(procNode)
    var adapters = ctx.postulateAdapters.getOrDefault(refId, @[])
    adapters.add(PostulateAdapter(key: spec.key,
      typeKey: spec.typeArgNames.join(";"), procName: spec.procName,
      isTypeBinder: isTypeBinder))
    ctx.postulateAdapters[refId] = adapters
    echo "[eponym codegen] issue #409: typed adapter " & spec.procName &
      " for " & spec.postulateName & "[" & spec.typeArgNames.join(", ") & "]"
  # Issue #409 slice 3: one repr-tier adapter per statically-known
  # instantiation whose value binders and result all denote the int
  # representation. The adapter's signature is the representation
  # signature (`int -> int` for `debugEcho[Int]`): it encodes each
  # argument with the `intToValue`-family codecs, calls the Value-tier
  # typed adapter emitted above (type witnesses already baked there),
  # and decodes the result — codecs only on the value boundary, and no
  # `RuntimeValue` anywhere in the adapter's signature. Instantiations
  # outside the int fragment get no repr adapter: repr-tier callers fall
  # back to Phase 1 exactly as before (no behavior change).
  var reprAdapterBodies: seq[NimNode] = @[]
  for spec in rawValueAdapters:
    if spec.postulateName notin globals: continue
    let entry = globals[spec.postulateName]
    if entry.tm.isNil or entry.tm.kind != tR: continue
    let refId = entry.tm.refId
    var valueDomains: seq[Term] = @[]
    var isTypeBinder: seq[bool] = @[]
    var resultTy: Term
    try:
      resultTy = substTypeBinders409(entry.ty, spec.typeArgNames, globals,
        valueDomains, isTypeBinder)
      for d in valueDomains:
        if ctx.reprTypeOf(d).kind != repInt:
          raise newException(CgUnsupported, "non-int value binder")
      if ctx.reprTypeOf(resultTy).kind != repInt:
        raise newException(CgUnsupported, "non-int result type")
    except CgUnsupported as e:
      echo "[eponym codegen] issue #409: no repr adapter for " &
        spec.postulateName & "[" & spec.typeArgNames.join(", ") & "]: " & e.msg
      continue
    var formal = newNimNode(nnkFormalParams)
    formal.add(nimReprType(ReprType(kind: repInt)))
    var argSyms: seq[NimNode] = @[]
    for i in 0 ..< valueDomains.len:
      let vsym = ident("cgReprAdapterArg" & $i)
      formal.add(newIdentDefs(vsym, nimReprType(ReprType(kind: repInt)),
        newEmptyNode()))
      argSyms.add(vsym)
    var inner = newCall(ident(spec.procName),
      newCall(bindSym"initRuntimeBindings"))
    for vsym in argSyms:
      inner.add(newCall(bindSym"intToValue", vsym))
    var reprBody = newStmtList()
    reprBody.add(newCall(bindSym"valueToInt", inner))
    var reprProcNode = newNimNode(nnkProcDef)
    reprProcNode.add(newTree(nnkPostfix, ident"*", ident(spec.reprProcName)))
    reprProcNode.add(newEmptyNode())
    reprProcNode.add(newEmptyNode())
    reprProcNode.add(formal)
    reprProcNode.add(newEmptyNode())
    reprProcNode.add(newEmptyNode())
    reprProcNode.add(reprBody)
    reprAdapterBodies.add(reprProcNode)
    var reprAdapters = ctx.postulateReprAdapters.getOrDefault(refId, @[])
    reprAdapters.add(ReprPostulateAdapter(key: spec.key,
      typeKey: spec.typeArgNames.join(";"), procName: spec.reprProcName,
      isTypeBinder: isTypeBinder))
    ctx.postulateReprAdapters[refId] = reprAdapters
    echo "[eponym codegen] issue #409: repr adapter " & spec.reprProcName &
      " for " & spec.postulateName & "[" & spec.typeArgNames.join(", ") & "]"
  for refId, cgRef in ctx.refs.pairs:
    bakedIds[refId] = cgRef.name
    if cgRef.kind == cgkElim:
      for ctorId in cgRef.cases.keys:
        let ctorName = ctx.refs.getOrDefault(ctorId).name
        bakedIds[ctorId] = ctorName
  validateBakedRefIds(globals, bakedIds)
  result = (procs: @[], compiled: initTable[string, string](),
            compiledRepr: initTable[string, string](),
            reprTypes: initTable[string, seq[ReprType]](),
            report: initTable[string, CodegenReportEntry](),
            exportInfo: initTable[string, CrossBlockExportInfo]())
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
  # Issue #408: reused definitions need no local emission. Marking them
  # emitted up front keeps dependents schedulable and keeps both emission
  # loops (which iterate `order`) from re-emitting their procs.
  for name in reused.keys: emitted[name] = true
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
  #
  # Issue #401: postulate forwarders come first. A bound postulate whose
  # type is fully within the representation fragment gets an
  # `eponymCompiledRepr_<name>` forwarder calling the host procedure
  # directly; in-body calls from repr-tier definitions then avoid the
  # interpreter entirely. Postulates without a representable type (or
  # without a binding) keep the Phase 1 backend.
  var reprBodies: seq[NimNode] = @[]
  var reprFailures = initTable[string, string]()
  for binding in postulateReprs:
    if binding.postulateName notin globals: continue
    let entry = globals[binding.postulateName]
    if entry.tm.isNil or entry.tm.kind != tR: continue
    let refId = entry.tm.refId
    if refId notin ctx.refs or ctx.refs[refId].kind != cgkPostulate: continue
    var failureReason = ""
    let procNode = compilePostulateProcRepr(binding.postulateName, entry.ty,
      binding, ctx, locFile, userLines.getOrDefault(binding.postulateName, 1),
      failureReason)
    if procNode.isNil:
      result.report[binding.postulateName] = CodegenReportEntry(
        tier: cgtValue,
        reason: "Phase 2 unavailable: " & failureReason, slowPaths: @[])
    else:
      let fwdName = cgReprName(binding.postulateName)
      # The forwarder just succeeded, so the signature is representable.
      let sig = ctx.reprSigOfType(entry.ty)
      ctx.reprProcs[refId] = (name: fwdName, arity: sig.len - 1, sig: sig)
      ctx.reprPostulateQtys[refId] = piQuantities(entry.ty)
      reprBodies.add(procNode)
      result.report[binding.postulateName] = CodegenReportEntry(
        tier: cgtRepr,
        reason: "Phase 2 representation-tier host forwarder emitted (" &
          reprSigSummary(sig) & ")",
        slowPaths: @[])
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
    ctx.reprProcs[refId] = (name: cgReprName(name), arity: sig.len - 1,
                             sig: sig)
    var failureReason = ""
    let procNode = compileDefProcRepr(d, ctx, locFile,
      userLines.getOrDefault(name, 1), failureReason)
    if procNode.isNil:
      reprFailures[name] = failureReason
      ctx.reprProcs.del(refId)
    else:
      reprBodies.add(procNode)
      result.compiledRepr[name] = cgReprName(name)
      result.reprTypes[name] = sig
  # Summarize the best emitted tier and why the next tier was unavailable.
  for d in defs:
    if d.name in reused:
      # Issue #408: no local emission; the report names the reused proc
      # and the origin it was exported from. The def counts as compiled
      # at the reused tiers, so the requireCompiled gate and wrapper
      # rerouting see it as compiled.
      let e = crossBlockImports[reused[d.name]]
      let key = reused[d.name]
      let origin = key[0 ..< key.find("\x00")]
      var entry = CodegenReportEntry(tier: cgtValue, slowPaths: @[])
      var usedProc = e.valueProc
      let reprReused = e.reprProc != "" and
        reusedReprNote.getOrDefault(d.name, "") == ""
      if reprReused:
        entry.tier = cgtRepr
        usedProc = e.reprProc
      entry.reason = "cross-block reuse of '" & usedProc & "' from '" &
        origin & "'"
      let note = reusedReprNote.getOrDefault(d.name, "")
      if note != "": entry.reason &= " (" & note & ")"
      entry.crossBlockFrom = usedProc & " from " & origin
      result.report[d.name] = entry
      if e.valueProc != "": result.compiled[d.name] = e.valueProc
      if reprReused:
        result.compiledRepr[d.name] = e.reprProc
        result.reprTypes[d.name] = reusedSig[d.name]
      continue
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
      entry.reason = "Phase 2 representation code emitted (" &
        reprSigSummary(result.reprTypes[d.name]) & ")"
    if d.name in erasedTerms:
      # Issue #401: slow paths are runtime calls to uncompiled definitions;
      # references from type positions (binder domains, `let` types) are
      # never evaluated, so only runtime references count.
      # Issue #408: a repr-compiled caller reaches its callees through
      # ctx.reprProcs (cross-block reused procs included), so for such a
      # caller only a callee without a repr proc is a slow path; a
      # value-tier caller still needs compiledProc.
      var ids = initTable[int, bool]()
      collectRuntimeRefIds(erasedTerms[d.name], ids)
      var seenSlowPaths = initTable[string, bool]()
      for refId in ids.keys:
        if refId notin ctx.refs or ctx.refs[refId].kind != cgkDefn:
          continue
        if refId in ctx.inlineGenericDefs:
          continue  # direct call sites beta-reduce this helper into repr code
        let calleeSlow =
          if entry.tier == cgtRepr: refId notin ctx.reprProcs
          else: ctx.refs[refId].compiledProc.len == 0
        if calleeSlow:
          let slowName = ctx.refs[refId].name
          if not seenSlowPaths.getOrDefault(slowName, false):
            entry.slowPaths.add(slowName)
            seenSlowPaths[slowName] = true
      entry.slowPaths.sort()
    result.report[d.name] = entry
  # Issue #408: publish cross-block export info for import-origin defs
  # this block compiled (locally or by reuse — re-exporting a reused def
  # republishes the same proc names under the same key, so it is
  # idempotent). `postulatesUsed` is the transitive runtime closure's
  # postulate references, following cgkDefn refs through their erased
  # terms; the macro drops the repr tier when it intersects the block's
  # bound postulates, since a reusing block must not silently inherit
  # this block's host implementations.
  var refIdToDefName = initTable[int, string]()
  for name, refId in defRefIds.pairs:
    refIdToDefName[refId] = name
  for d in defs:
    if d.loc.source.len == 0 or d.loc.source.startsWith("<eponymBlock>"):
      continue
    let valueProc = result.compiled.getOrDefault(d.name, "")
    let reprProc = result.compiledRepr.getOrDefault(d.name, "")
    if valueProc == "" and reprProc == "": continue
    var postulatesUsed: seq[string] = @[]
    var seenPost = initHashSet[string]()
    var visited = initHashSet[string]()
    var stack = @[d.name]
    while stack.len > 0:
      let nm = stack.pop()
      if nm in visited: continue
      visited.incl(nm)
      if nm notin erasedTerms: continue
      var ids = initTable[int, bool]()
      collectRuntimeRefIds(erasedTerms[nm], ids)
      for refId in ids.keys:
        if refId notin ctx.refs: continue
        let r = ctx.refs[refId]
        if r.kind == cgkPostulate:
          if r.name notin seenPost:
            seenPost.incl(r.name)
            postulatesUsed.add(r.name)
        elif r.kind == cgkDefn:
          let callee = refIdToDefName.getOrDefault(refId, "")
          if callee != "" and callee notin visited:
            stack.add(callee)
    postulatesUsed.sort()
    result.exportInfo[d.name] = CrossBlockExportInfo(
      origin: d.loc.source, valueProc: valueProc, reprProc: reprProc,
      sigSummary: if reprProc != "" and d.name in result.reprTypes:
                    reprSigSummary(result.reprTypes[d.name])
                  else: "",
      postulatesUsed: postulatesUsed)
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
  result.procs = elimFwds & adapterBodies & reprAdapterBodies & defBodies &
    reprBodies & elimBodies
