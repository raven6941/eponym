## Production support for staged runtime type descriptors (issue #499).
##
## This module is intentionally independent of the evaluator.  The public
## descriptor has no Term/Value field and its constructors are private to this
## module; generated consumers use the small descriptor operations below.

import std/macros
import eponym_init

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

