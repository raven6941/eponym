## Relational engine in Nim — Track C
##
## A practical miniKanren-style relational engine. Not dogmatic about
## miniKanren specifics; optimized for the elaboration use case:
##   - Terms are eponym Terms (with logic vars as metavariables)
##   - Depth-first search with backtracking (not fair interleaving)
##   - Simple, debuggable, fast enough for elaboration
##
## The goal: write relational definitions of elaboration, e.g.
##   typeo(term, type)  — relates a term to its type
## Run forward for inference, backward for synthesis.

import ett_init
import tables

# --- Logic variables ------------------------------------------------
# We reuse the elaborator's metavariable infrastructure.
# A logic var is a Term of kind tMeta (metavariable).

# --- Substitutions --------------------------------------------------
# A Subst maps metavar IDs to Terms. We use the MetaStore from elab.

# For a standalone relational engine (not tied to elab's MetaStore),
# we define a simple subst here. The elaboration relation will bridge.

type
  RVar = int  # relational variable ID

  RTermKind = enum
    rkVar     # logic variable
    rkTerm    # embedded eponym Term (ground or with vars)

  RTerm = ref object
    case kind: RTermKind
    of rkVar: id: RVar
    of rkTerm: tm: Term  # eponym term; may contain rkVar via tMeta?

# Actually — simpler: use eponym Terms directly, with tMeta as logic vars.
# The relational engine works over Term, Subst is seq[(varId, Term)].

type
  Subst* = seq[(int, Term)]

proc emptySubst*(): Subst = @[]

proc walk*(t: Term, s: Subst): Term =
  ## Follow metavar bindings.
  var cur = t
  while cur.kind == tMeta:
    var found = false
    for (id, val) in s:
      if id == cur.metaId:
        cur = val
        found = true
        break
    if not found: break
  cur

proc occurs*(varId: int, t: Term, s: Subst): bool =
  let wt = walk(t, s)
  case wt.kind
  of tMeta: wt.metaId == varId
  of tApp: occurs(varId, wt.fn, s) or occurs(varId, wt.arg, s)
  of tLam, tPi, tSi: occurs(varId, wt.dom, s) or occurs(varId, wt.scope.bdy, s)
  of tPair: occurs(varId, wt.pFst, s) or occurs(varId, wt.pSnd, s)
  else: false

proc unifyRel*(u, v: Term, s: Subst): tuple[ok: bool, s2: Subst] =
  ## Unify two Terms under subst. Returns (false, s) on failure.
  ## This is a simplified version; the full elaborator uses unify.nim.
  let u2 = walk(u, s)
  let v2 = walk(v, s)
  if u2.kind == tMeta and v2.kind == tMeta and u2.metaId == v2.metaId:
    return (true, s)
  if u2.kind == tMeta:
    if occurs(u2.metaId, v2, s): return (false, s)
    var ns = s
    ns.add((u2.metaId, v2))
    return (true, ns)
  if v2.kind == tMeta:
    if occurs(v2.metaId, u2, s): return (false, s)
    var ns = s
    ns.add((v2.metaId, u2))
    return (true, ns)
  # Structural (simplified; full version in unify.nim handles more)
  if u2.kind != v2.kind: return (false, s)
  case u2.kind
  of tApp:
    let (ok1, s1) = unifyRel(u2.fn, v2.fn, s)
    if not ok1: return (false, s)
    return unifyRel(u2.arg, v2.arg, s1)
  of tC:
    # Constants: compare by equality (simplified)
    if u2.c == v2.c: (true, s) else: (false, s)
  of tR:
    if u2.refId == v2.refId: (true, s) else: (false, s)
  of tInt:
    if u2.intVal == v2.intVal: (true, s) else: (false, s)
  else:
    # For simplicity, use structural equality for other kinds
    if u2 == v2: (true, s) else: (false, s)

# --- Goals ----------------------------------------------------------
# A Goal is a proc taking a Subst and returning a seq of Substs.
# Depth-first, with a global result limit for practicality.

type
  Goal* = proc(s: Subst): seq[Subst] {.closure.}

var maxResults* = 1000  # safety cap

proc `==`*(u, v: Term): Goal =
  return proc(s: Subst): seq[Subst] =
    let (ok, s2) = unifyRel(u, v, s)
    if ok: @[s2] else: @[]

proc conj*(g1, g2: Goal): Goal =
  return proc(s: Subst): seq[Subst] =
    result = @[]
    for s1 in g1(s):
      for s2 in g2(s1):
        result.add(s2)
        if result.len >= maxResults: return

proc disj*(g1, g2: Goal): Goal =
  return proc(s: Subst): seq[Subst] =
    result = g1(s)
    for s2 in g2(s):
      result.add(s2)
      if result.len >= maxResults: return

proc conde*(clauses: seq[Goal]): Goal =
  if clauses.len == 0:
    return proc(s: Subst): seq[Subst] = @[]
  result = clauses[^1]
  for i in countdown(clauses.high - 1, 0):
    let g = clauses[i]
    let rest = result
    result = disj(g, rest)

# --- Fresh ----------------------------------------------------------

var freshId = 0

proc freshVar*(): Term =
  inc freshId
  Term(kind: tMeta, metaId: freshId, metaSpine: @[])

proc fresh*(body: proc(x: Term): Goal {.closure.}): Goal =
  let v = freshVar()
  body(v)

# --- Run ------------------------------------------------------------

proc reify*(t: Term, s: Subst): Term =
  let wt = walk(t, s)
  case wt.kind
  of tMeta: wt  # unbound; keep as-is
  of tApp: tmApp(reify(wt.fn, s), reify(wt.arg, s))
  else: wt

proc run*(q: Term, g: Goal, n = 10): seq[Term] =
  ## Run goal, return up to n reified results for query var q.
  freshId = 0
  let substs = g(emptySubst())
  result = @[]
  for i in 0 ..< min(n, substs.len):
    result.add(reify(q, substs[i]))

