## Language-specialized relational engine for STLC+Nat
##
## Instead of generic RTerm S-exprs (with string atoms, case dispatch
## on every operation), use a dedicated ADT for the object language.
##
## This specializes the *engine* to the *language* (not just the query).
## Compare:
## - Generic: RTerm(kind: rkAtom, name: "zero") — string compare, case dispatch
## - Specialized: Tm(kind: tmZero) — direct tag check, no strings
##
## The relation (typeo) stays relational; only the representation changes.

import minikanren  # for Subst, Stream, Goal — still generic for now
import strutils   # for parseInt

# --- Dedicated term representation ---

type
  TmKind* = enum
    tmZero, tmSuc, tmVar, tmLam, tmApp

  Tm* = ref object
    case kind*: TmKind
    of tmZero: nil
    of tmSuc: pred*: Tm
    of tmVar: idx*: int
    of tmLam: body*: Tm
    of tmApp: fn*, arg*: Tm

  TyKind* = enum
    tyNat, tyArr

  Ty* = ref object
    case kind*: TyKind
    of tyNat: nil
    of tyArr: dom*, cod*: Ty

proc `$`*(t: Tm): string =
  case t.kind
  of tmZero: "zero"
  of tmSuc: "(suc " & $t.pred & ")"
  of tmVar: "(var " & $t.idx & ")"
  of tmLam: "(lam " & $t.body & ")"
  of tmApp: "(app " & $t.fn & " " & $t.arg & ")"

proc `$`*(t: Ty): string =
  case t.kind
  of tyNat: "nat"
  of tyArr: "(arr " & $t.dom & " " & $t.cod & ")"

# --- Conversion from RTerm (for testing) ---

proc toTm*(r: RTerm): Tm =
  ## Convert a ground RTerm S-expr to dedicated Tm.
  ## Only works for ground terms (no vars).
  if r.kind == rkAtom:
    if r.name == "zero": return Tm(kind: tmZero)
    else: raise newException(ValueError, "unknown atom: " & r.name)
  elif r.kind == rkPair:
    let head = r.head
    if head.kind == rkAtom:
      case head.name
      of "suc": return Tm(kind: tmSuc, pred: toTm(r.tail.head))
      of "var": return Tm(kind: tmVar, idx: parseInt(r.tail.head.name))
      of "lam": return Tm(kind: tmLam, body: toTm(r.tail.head))
      of "app": return Tm(kind: tmApp, fn: toTm(r.tail.head), arg: toTm(r.tail.tail.head))
      else: raise newException(ValueError, "unknown head: " & head.name)
  raise newException(ValueError, "not a ground term")

# --- Direct synthesis (no relational overhead) ---
# This is the fully specialized engine for synthNat:
# no RTerm, no Subst, no unify, no Stream, no worklist.

iterator synthNatDirect*(): Tm =
  ## Generate all Nat terms, smallest first.
  ## This is what a fully specialized engine produces:
  ## the relation compiled to direct generation.
  var queue: seq[Tm] = @[Tm(kind: tmZero)]
  var i = 0
  while true:
    let t = queue[i]
    inc i
    yield t
    queue.add(Tm(kind: tmSuc, pred: t))

when isMainModule:
  import times
  import rel_elab
  import staged_synth
  
  echo "=== Language-specialized engine vs generic ==="
  echo ""
  
  # Generic staged (RTerm)
  let q = freshVar()
  let start1 = cpuTime()
  var count1 = 0
  for t in run(q, synthNat(q), 100):
    inc count1
  let time1 = cpuTime() - start1
  echo "Generic staged (RTerm): ", count1, " terms in ", time1*1000, "ms"
  
  # Specialized direct (Tm)
  let start2 = cpuTime()
  var count2 = 0
  for t in synthNatDirect():
    inc count2
    if count2 >= 100: break
  let time2 = cpuTime() - start2
  echo "Specialized direct (Tm): ", count2, " terms in ", time2*1000, "ms"
  
  echo ""
  if time2 > 0:
    echo "Speedup: ", time1/time2, "x"
  echo ""
  echo "The specialized version eliminates:"
  echo "  - RTerm case dispatch and string atom comparisons"
  echo "  - Subst allocation and linear walk"
  echo "  - Generic unify with occurs check"
  echo "  - Stream tree construction and worklist interpretation"
  echo "  - Goal closure allocations"
