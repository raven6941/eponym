## Experiment 2: the `ett` macro -- compile-time elaboration and checking.
##
## Deliberately thin (see decisions.org on Nimony/Nim 3): the parser and
## elaborator are plain Nim code in parse_surf and elab; the macro only feeds
## them a string literal and turns failures into compiler errors. No NimNode
## inspection, no hygiene tricks -- nothing that ties us to Nim 2's macro API.

import macros
import elab
import parse_surf

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

when isMainModule:
  ett"""
def twice (A : ?) (f : A -> A) (x : A) : A :=
  f (f x)
def pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A :=
  (snd p, fst p)
"""
  echo "ok: ett macro accepts well-typed programs at compile time"
