## Production support for staged runtime type descriptors (issue #499).
##
## This module is intentionally independent of the evaluator.  The public
## descriptor has no Term/Value field and its constructors are private to this
## module; generated consumers use the small descriptor operations below.

import std/[macros, tables, sets, algorithm]
import eponym_init
import elab
import preterm

type
  TypeRepKind* = enum
    trNat, trString, trArrow

  TypeRep* = ref object
    ## Fields are private: a family-specific generated consumer should expose
    ## predicates/accessors, not Eponym's checked representation.
    kind: TypeRepKind
    domain, codomain: TypeRep

  StagedInjectError* = object of CatchableError

proc natRep*(): TypeRep = TypeRep(kind: trNat)
proc stringRep*(): TypeRep = TypeRep(kind: trString)
proc arrowRep*(domain, codomain: TypeRep): TypeRep =
  TypeRep(kind: trArrow, domain: domain, codomain: codomain)

proc kind*(rep: TypeRep): TypeRepKind = rep.kind
proc domain*(rep: TypeRep): TypeRep = rep.domain
proc codomain*(rep: TypeRep): TypeRep = rep.codomain

proc `==`*(a, b: TypeRep): bool =
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of trNat, trString: true
  of trArrow: a.domain == b.domain and a.codomain == b.codomain

proc `$`*(rep: TypeRep): string =
  if rep.isNil: return "<nil>"
  case rep.kind
  of trNat: "Nat"
  of trString: "String"
  of trArrow: "(" & $rep.domain & " -> " & $rep.codomain & ")"

proc stageStaticTerm*(term: Term, familyName = "runtimeType"): NimNode =
  ## Emit a descriptor for the static fragment of a checked term.  This is a
  ## deliberately small, closed v1 algebra: the only atoms are Nat and String
  ## and the only structural operation is Arrow.  Dynamic eliminators are not
  ## guessed here; callers must use the family-specific residual emitter.
  if term.isNil:
    raise newException(StagedInjectError,
      familyName & ": cannot residualize a nil checked term")
  case term.kind
  of tR:
    if term.refTyp.isNil:
      raise newException(StagedInjectError,
        familyName & ": unsupported reference refId=" & $term.refId)
    # Names are carried by the checked global table, so a bare Term cannot be
    # trusted to infer an atom.  The caller supplies atom terms through the
    # overload below; rejecting this case is preferable to an interpreter
    # fallback.
    raise newException(StagedInjectError,
      familyName & ": unresolved checked reference refId=" & $term.refId)
  of tPi:
    if term.scope.bdy.isNil:
      raise newException(StagedInjectError,
        familyName & ": malformed function descriptor")
    # The core uses Pi for arrows.  Its domain is handled by the named
    # overload, while this entry point remains strict about unresolved names.
    raise newException(StagedInjectError,
      familyName & ": Pi descriptor needs a family atom mapping")
  else:
    raise newException(StagedInjectError,
      familyName & ": unsupported static operation " & $term.kind)

proc emitAtomRep*(atomName: string, familyName = "runtimeType"): NimNode =
  ## Emit one closed descriptor atom.  This is used by family generators after
  ## resolving a checked reference through Globals; no unchecked Nim type AST
  ## enters the generated code.
  case atomName
  of "Nat": newCall(bindSym"natRep")
  of "String": newCall(bindSym"stringRep")
  else:
    raise newException(StagedInjectError,
      familyName & ": unsupported TypeRep atom '" & atomName & "'")

proc emitArrowRep*(domain, codomain: NimNode): NimNode =
  newCall(bindSym"arrowRep", domain, codomain)

type StageBinding = object
  ## A host parameter and its corresponding de Bruijn slot.  The public
  ## entry point deliberately takes the host declaration as Nim AST: Term
  ## contains no host representation information.
  name: NimNode
  hostType: NimNode

proc stageError(familyName, message: string, loc: Loc): ref StagedInjectError =
  let where = if loc.source.len > 0:
    " (" & loc.source & ":" & $loc.line & ":" & $loc.col & ")"
  else: ""
  newException(StagedInjectError, familyName & where & ": " & message)

proc refName(globals: Globals, id: int): string =
  for name, entry in globals:
    if not entry.tm.isNil and entry.tm.kind == tR and entry.tm.refId == id:
      return name
  ""

proc spine(t: Term): tuple[head: Term, args: seq[Term]] =
  var cur = t
  var args: seq[Term] = @[]
  while cur.kind == tApp:
    args.add(cur.arg)
    cur = cur.fn
  args.reverse()
  (cur, args)

proc stageFamily*(term: Term, globals: Globals, familyName: string,
                  params: openArray[(NimNode, NimNode)],
                  loc: Loc = noLoc): NimNode =
  ## Residualize a checked family.  `params` supplies host names/types for
  ## dynamic binders, since that information intentionally is not stored in
  ## the kernel Term.  The generated procedure only mentions TypeRep
  ## constructors and ordinary host control flow.
  ##
  ## v1 supports the descriptor algebra Nat/String/Arrow and complete Nat
  ## eliminators.  This is intentionally strict: a term outside this slice
  ## is a compile-time StagedInjectError, never a call into the evaluator.
  var hostParams: seq[StageBinding] = @[]
  for p in params:
    hostParams.add(StageBinding(name: p[0], hostType: p[1]))
  let procName = genSym(nskProc, familyName & "Residual")
  var activeDefs = initHashSet[int]()

  proc emit(t: Term, env: seq[NimNode]): NimNode

  proc emitRed(head: Term, args: seq[Term], env: seq[NimNode]): NimNode =
    let gname = refName(globals, head.refId)
    if gname.len == 0 or gname notin globals or not globals[gname].isElim:
      raise stageError(familyName, "unsupported application", loc)
    let rule = head.refVal
    if rule.isNil or rule.whnf.kind != wRed:
      raise stageError(familyName, "malformed eliminator '" & gname & "'", loc)
    let r = rule.whnf.rule
    if args.len < r.nargs:
      raise stageError(familyName, "partial eliminator '" & gname & "'", loc)
    let scrut = emit(args[r.nargs - 1], env)
    # Nat is the only dynamic representation in v1.  A zero/successor split
    # is the host representation of the corresponding constructor cases.
    var zeroId = -1
    var sucId = -1
    for ctorId, arity in r.caseArities:
      if arity == 0: zeroId = ctorId
      elif arity == 1: sucId = ctorId
    if zeroId < 0 or sucId < 0:
      raise stageError(familyName, "dynamic eliminator is not a Nat split", loc)
    let zeroBody = r.cases[zeroId]
    let sucBody = r.cases[sucId]
    # The rule templates use [eliminator parameters, constructor fields]
    # as innermost de Bruijn variables.  For the common Nat fold, the
    # successor field is represented by `scrut - 1` and recursive calls are
    # retained by the normal tR path below.
    let zeroExpr = emit(zeroBody, env)
    let prev = newTree(nnkInfix, ident"-", scrut, newLit(1))
    let sucExpr = emit(sucBody, env & @[prev])
    result = quote do:
      block:
        if `scrut` == 0:
          `zeroExpr`
        else:
          `sucExpr`

  proc emit(t: Term, env: seq[NimNode]): NimNode =
    if t.isNil: raise stageError(familyName, "nil checked term", loc)
    case t.kind
    of tV:
      if t.idx >= env.len: raise stageError(familyName, "out-of-scope variable", loc)
      env[t.idx]
    of tLam:
      raise stageError(familyName, "unapplied lambda", loc)
    of tApp:
      if t.fn.kind == tLam:
        return emit(t.fn.scope.bdy, @[emit(t.arg, env)] & env)
      let (head, args) = spine(t)
      let headName = if head.kind == tR: refName(globals, head.refId) else: ""
      if head.kind == tR and headName in globals and globals[headName].isElim:
        return emitRed(head, args, env)
      if head.kind == tR and head.refIsDefn and not head.refVal.isNil:
        if head.refId in activeDefs:
          if args.len != 1: raise stageError(familyName, "unsupported recursive arity", loc)
          return newCall(procName, emit(args[0], env))
        activeDefs.incl(head.refId)
        result = emit(tmApp(head.refVal.syn, t.arg), env)
        activeDefs.excl(head.refId)
        return result
      raise stageError(familyName, "unsupported application", loc)
    of tR:
      let name = refName(globals, t.refId)
      if name == "Nat": return newCall(bindSym"natRep")
      if name == "String": return newCall(bindSym"stringRep")
      if t.refIsDefn and not t.refVal.isNil:
        if t.refId in activeDefs:
          raise stageError(familyName, "recursive reference needs an argument", loc)
        activeDefs.incl(t.refId)
        result = emit(t.refVal.syn, env)
        activeDefs.excl(t.refId)
        return result
      raise stageError(familyName, "unsupported reference '" & name & "'", loc)
    of tPi:
      emitArrowRep(emit(t.dom, env), emit(t.scope.bdy, @[newLit(0)] & env))
    of tLet:
      emit(t.letScope.bdy, @[emit(t.letVal, env)] & env)
    of tNatLit:
      raise stageError(familyName, "Nat literal is not a TypeRep atom", loc)
    of tMeta:
      raise stageError(familyName, "metavariable in zonked term", loc)
    else:
      raise stageError(familyName, "unsupported term kind " & $t.kind, loc)

  var initialEnv: seq[NimNode] = @[]
  for i in countdown(hostParams.len - 1, 0):
    initialEnv.add(hostParams[i].name)
  var body = emit(term, initialEnv)
  var decl = newNimNode(nnkProcDef)
  decl.add(procName)
  decl.add(newEmptyNode())
  decl.add(newEmptyNode())
  var formal = newNimNode(nnkFormalParams)
  formal.add(ident"TypeRep")
  for p in hostParams:
    formal.add(newIdentDefs(p.name, p.hostType, newEmptyNode()))
  decl.add(formal)
  decl.add(newEmptyNode())
  decl.add(newEmptyNode())
  decl.add(newTree(nnkStmtList, newTree(nnkAsgn, ident"result", body)))
  newTree(nnkStmtList, decl, newTree(nnkCall, procName))

