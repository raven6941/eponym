## Relational elaboration — Track C (practical)
##
## A minimal relational type inferencer demonstrating the core idea:
## write the typing rules as relations, query them forwards (inference)
## or backwards (synthesis).
##
## Language: simple types with Nat, functions, and variables.
## Terms are represented as Nim ADTs (not eponym Terms) for clarity.
## The point is the *relational style*, not integration with eponym yet.

import minikanren
# We use minikanren's Term? No — for this demo, define our own simple terms
# to avoid confusion with eponym's Term. Actually, let's use a simple ADT.

type
  TyKind = enum tkNat, tkArr
  Ty = ref object
    case kind: TyKind
    of tkNat: discard
    of tkArr: dom, cod: Ty

  TmKind = enum tmVar, tmLam, tmApp, tmZero, tmSuc
  Tm = ref object
    case kind: TmKind
    of tmVar: idx: int
    of tmLam: body: Tm
    of tmApp: fn, arg: Tm
    of tmZero: discard
    of tmSuc: pred: Tm

# For the relational engine, we need to embed these in minikanren Terms.
# Simpler: we write the relation directly on the ADT using the engine's
# unification on a custom encoding.
#
# Practical approach: encode Tm/Ty as minikanren Terms (pairs/atoms).
#   Nat       -> 'nat
#   Arr(d,c)  -> (arr d c)
#   Var(i)    -> (var i)
#   Lam(b)    -> (lam b)
#   App(f,a)  -> (app f a)
#   Zero      -> 'zero
#   Suc(n)    -> (suc n)

import ett_init  # for Term? No, minikanren has its own.

# Actually, minikanren.nim now uses ett_init.Term. Let's define the
# encoding using ett_init constructors via a helper module.
#
# For this proof-of-concept, we'll implement typeo directly in Nim
# using the relational combinators, with terms as minikanren-style
# S-expressions built from ett_init.Term.
#
# Given time constraints, here's the *structure* of the relation;
# the full implementation with de Bruijn context lookup is future work.

proc typeo(tm, ty, ctx: Term): Goal =
  ## typeo(tm, ty, ctx): tm has type ty in context ctx.
  ## ctx: list of types, innermost first, as nested pairs.
  ##
  ## Rules (relational):
  ##   var:    ctx = (ty . _)  =>  var(0) : ty
  ##   lam:    tm = (lam b), ty = (arr d c), b : c in (d . ctx)
  ##   app:    tm = (app f a), f : (arr d c), a : d, ty = c
  ##   zero:   tm = zero  =>  ty = nat
  ##   suc:    tm = (suc n), n : nat  =>  ty = nat
  ##
  ## Each rule is a conde branch; the engine searches.
  discard  # TODO: implement with proper term encoding

when isMainModule:
  echo "rel_elab: relational type inference (structure defined, impl TODO)"
  echo "The key idea: typing rules as relations, not functions."
  echo "Query forward:  typeo(term, ?ty, [])  -> infer type"
  echo "Query backward: typeo(?tm, nat, [])   -> synthesize Nat terms"
