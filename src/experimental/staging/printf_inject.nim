## Family-specific staged-inject prototype for issue #491.
##
## `injectPrintfType(fmt)` expands to a residual Nim function. `fmt` remains
## dynamic; the generated function computes the corresponding `TypeRep` with
## ordinary pattern matching and recursion. This experimental spike keeps the
## family equations explicit so the staging boundary can be reviewed before
## it is generalized to elaborated Eponym definitions.

import std/macros

type
  FormatKind* = enum
    fkNumber, fkString, fkEnd

  Format* = ref object
    kind*: FormatKind
    tail*: Format

  TypeRepKind* = enum
    trNat, trString, trArrow

  TypeRep* = ref object
    kind*: TypeRepKind
    domain*, codomain*: TypeRep

proc number*(tail: Format): Format = Format(kind: fkNumber, tail: tail)
proc stringArg*(tail: Format): Format = Format(kind: fkString, tail: tail)
proc endFormat*(): Format = Format(kind: fkEnd)

proc natRep*(): TypeRep = TypeRep(kind: trNat)
proc stringRep*(): TypeRep = TypeRep(kind: trString)
proc arrowRep*(domain, codomain: TypeRep): TypeRep =
  TypeRep(kind: trArrow, domain: domain, codomain: codomain)

proc `==`*(a, b: TypeRep): bool =
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of trNat, trString: true
  of trArrow: a.domain == b.domain and a.codomain == b.codomain

macro injectPrintfType*(staticPrefix: static[string],
                        runtimeSuffix: untyped): untyped =
  ## Partially evaluate a known format prefix and emit the residual for its
  ## dynamic suffix. `N` and `S` prefix characters are consumed at macro time;
  ## the generated function receives the remaining format dynamically.
  let residual = genSym(nskProc, "printfTypeResidual")
  var resultRep = newCall(residual, runtimeSuffix)
  for i in countdown(staticPrefix.len - 1, 0):
    case staticPrefix[i]
    of 'N':
      resultRep = newCall(bindSym"arrowRep", newCall(bindSym"natRep"), resultRep)
    of 'S':
      resultRep = newCall(bindSym"arrowRep", newCall(bindSym"stringRep"),
        resultRep)
    else:
      error("PrintfType prefix accepts only 'N' and 'S'")

  result = quote do:
    block:
      proc `residual`(format: Format): TypeRep =
        case format.kind
        of fkEnd:
          stringRep()
        of fkNumber:
          arrowRep(natRep(), `residual`(format.tail))
        of fkString:
          arrowRep(stringRep(), `residual`(format.tail))
      `resultRep`

proc `$`*(rep: TypeRep): string =
  if rep.isNil: return "<nil>"
  case rep.kind
  of trNat: "Nat"
  of trString: "String"
  of trArrow: "(" & $rep.domain & " -> " & $rep.codomain & ")"
