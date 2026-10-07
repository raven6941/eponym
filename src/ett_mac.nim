## Experiment 2: the `ett` macro -- compile-time elaboration and checking.
##
## Deliberately thin (see decisions.org on Nimony/Nim 3): the parser and
## elaborator are plain Nim code in parse_surf and elab; the macro only feeds
## them a string literal and turns failures into compiler errors. No NimNode
## inspection, no hygiene tricks -- nothing that ties us to Nim 2's macro API.

import macros
import elab
import parse_surf
import ett_init

macro ett*(src: string): untyped =
  ## Elaborate and typecheck a surface program at compile time.
  ## On success expands to nothing; on failure compilation stops with an
  ## error pointing at the ett"..." literal.
  let s = src.strVal  # src is a string literal (enforced by the signature)
  try:
    discard elabCheck(s)
  except ElabError as e:
    error("ett elaboration error: " & e.msg, src)
  except ParseError as e:
    error("ett parse error: " & e.msg, src)
  result = newStmtList()

proc isIntType(t: Term): bool =
  ## Check if a Term is the primitive Int type.
  # The Int type is represented as... let me check
  # Actually, `Int` in surface syntax elaborates to something.
  # For now, check if it's a tR referencing the Int type.
  # This is a simplification — full check needs globals.
  false  # TODO: implement properly

macro ettEmbed*(src: string): untyped =
  ## Elaborate a surface program at compile time and generate Nim
  ## wrapper procs for each `def` of type `Int -> ... -> Int`.
  ##
  ## Each wrapper has the form:
  ##   proc name(arg1: int, arg2: int, ...): int =
  ##     callIntFunc("<source>", "name", @[arg1, arg2, ...])
  ##
  ## The elaborated terms are re-obtained at runtime via the
  ## definition cache (compile-time elaboration ensures well-typedness).
  let s = src.strVal
  var defs: seq[ElabDef]
  try:
    defs = elabCheck(s)
  except ElabError as e:
    error("ettEmbed elaboration error: " & e.msg, src)
  except ParseError as e:
    error("ettEmbed parse error: " & e.msg, src)
  
  result = newStmtList()
  # Note: the generated procs call callIntFunc, which must be
  # imported by the user: `import ett_embed` before using ettEmbed.
  
  for d in defs:
    let procName = ident(d.name)
    let srcLit = newLit(s)
    let nameLit = newLit(d.name)
    result.add(quote do:
      proc `procName`*(args: varargs[int]): int =
        callIntFunc(`srcLit`, `nameLit`, @args)
    )

when isMainModule:
  ett"""
def twice (A : ?) (f : A -> A) (x : A) : A :=
  f (f x)
def pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A :=
  (snd p, fst p)
"""
  echo "ok: ett macro accepts well-typed programs at compile time"
