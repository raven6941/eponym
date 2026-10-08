## Relational engine — Track C (independent)
##
## A practical miniKanren-style relational engine. Self-contained:
## no dependency on the elaborator (ett_init) or any other eponym module.
## Useful for relational programming in general, not just elaboration.
##
## Terms are simple S-expressions: variables, atoms, pairs.
##   - var(id): logic variable
##   - atom(name): symbolic atom (e.g. "nat", "zero", "42")
##   - pair(h, t): cons cell; nil is atom("nil")
##
## Provides: unification with occurs check, goals (==, conj, disj, conde),
## fresh variable introduction, and run for querying.

import sequtils
import strutils

# --- Terms ------------------------------------------------------------

type
  RKind* = enum rkVar, rkAtom, rkPair
  RTerm* = ref object
    case kind*: RKind
    of rkVar: id*: int
    of rkAtom: name*: string
    of rkPair: head*, tail*: RTerm

proc rvar*(id: int): RTerm = RTerm(kind: rkVar, id: id)
proc ratom*(name: string): RTerm = RTerm(kind: rkAtom, name: name)
proc rpair*(h, t: RTerm): RTerm = RTerm(kind: rkPair, head: h, tail: t)
proc rnil*(): RTerm = ratom("nil")
proc rint*(n: int): RTerm = ratom($n)

proc rlist*(elems: seq[RTerm]): RTerm =
  result = rnil()
  for i in countdown(elems.high, 0):
    result = rpair(elems[i], result)

proc `$`*(t: RTerm): string =
  case t.kind
  of rkVar: "?v" & $t.id
  of rkAtom: t.name
  of rkPair:
    var parts: seq[string] = @[]
    var cur = t
    while cur.kind == rkPair:
      parts.add($cur.head)
      cur = cur.tail
    if cur.kind == rkAtom and cur.name == "nil":
      "(" & parts.join(" ") & ")"
    else:
      "(" & parts.join(" ") & " . " & $cur & ")"

# --- Substitutions ----------------------------------------------------

type
  Subst* = seq[(int, RTerm)]

proc emptySubst*(): Subst = @[]

proc walk*(t: RTerm, s: Subst): RTerm =
  var cur = t
  while cur.kind == rkVar:
    var found = false
    for (id, val) in s:
      if id == cur.id:
        cur = val
        found = true
        break
    if not found: break
  cur

proc occurs*(id: int, t: RTerm, s: Subst): bool =
  let wt = walk(t, s)
  case wt.kind
  of rkVar: wt.id == id
  of rkPair: occurs(id, wt.head, s) or occurs(id, wt.tail, s)
  else: false

proc unify*(u, v: RTerm, s: Subst): tuple[ok: bool, s2: Subst] =
  let u2 = walk(u, s)
  let v2 = walk(v, s)
  if u2.kind == rkVar and v2.kind == rkVar and u2.id == v2.id:
    return (true, s)
  if u2.kind == rkVar:
    if occurs(u2.id, v2, s): return (false, s)
    var ns = s; ns.add((u2.id, v2)); return (true, ns)
  if v2.kind == rkVar:
    if occurs(v2.id, u2, s): return (false, s)
    var ns = s; ns.add((v2.id, u2)); return (true, ns)
  if u2.kind == rkPair and v2.kind == rkPair:
    let (ok1, s1) = unify(u2.head, v2.head, s)
    if not ok1: return (false, s)
    return unify(u2.tail, v2.tail, s1)
  if u2.kind == rkAtom and v2.kind == rkAtom and u2.name == v2.name:
    return (true, s)
  (false, s)

# --- Goals ------------------------------------------------------------

type
  Goal* = proc(s: Subst): seq[Subst] {.closure.}

const MaxResults* = 1000

proc `==`*(u, v: RTerm): Goal =
  return proc(s: Subst): seq[Subst] =
    let (ok, s2) = unify(u, v, s)
    if ok: @[s2] else: @[]

proc conj*(g1, g2: Goal): Goal =
  return proc(s: Subst): seq[Subst] =
    result = @[]
    for s1 in g1(s):
      for s2 in g2(s1):
        result.add(s2)
        if result.len >= MaxResults: return

proc disj*(g1, g2: Goal): Goal =
  return proc(s: Subst): seq[Subst] =
    result = g1(s)
    for s2 in g2(s):
      result.add(s2)
      if result.len >= MaxResults: return

proc conde*(clauses: seq[Goal]): Goal =
  if clauses.len == 0:
    return proc(s: Subst): seq[Subst] = @[]
  result = clauses[^1]
  for i in countdown(clauses.high - 1, 0):
    let g = clauses[i]
    let rest = result
    result = disj(g, rest)

# --- Fresh ------------------------------------------------------------

var freshCounter* = 0

proc freshVar*(): RTerm =
  inc freshCounter
  rvar(freshCounter)

proc fresh*(body: proc(x: RTerm): Goal {.closure.}): Goal =
  ## Lazy: body called when goal runs, not when constructed.
  return proc(s: Subst): seq[Subst] =
    let v = freshVar()
    body(v)(s)

proc fresh2*(body: proc(x, y: RTerm): Goal {.closure.}): Goal =
  return proc(s: Subst): seq[Subst] =
    let a = freshVar(); let b = freshVar()
    body(a, b)(s)

proc fresh3*(body: proc(x, y, z: RTerm): Goal {.closure.}): Goal =
  return proc(s: Subst): seq[Subst] =
    let a = freshVar(); let b = freshVar(); let c = freshVar()
    body(a, b, c)(s)

proc fresh4*(body: proc(a, b, c, d: RTerm): Goal {.closure.}): Goal =
  return proc(s: Subst): seq[Subst] =
    let x1 = freshVar(); let x2 = freshVar()
    let x3 = freshVar(); let x4 = freshVar()
    body(x1, x2, x3, x4)(s)

# --- Run --------------------------------------------------------------

proc reify*(t: RTerm, s: Subst): RTerm =
  let wt = walk(t, s)
  case wt.kind
  of rkVar: wt
  of rkPair: rpair(reify(wt.head, s), reify(wt.tail, s))
  else: wt

proc run*(q: RTerm, g: Goal, n = 10): seq[RTerm] =
  freshCounter = 0
  let substs = g(emptySubst())
  result = @[]
  for i in 0 ..< min(n, substs.len):
    result.add(reify(q, substs[i]))
