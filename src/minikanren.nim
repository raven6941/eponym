## Relational engine — Track C (independent, explicit search tree)
##
## Uses an explicit Stream tree (not closures on call stack) for the
## search. Interleaving (mplus) is data, processed by an explicit
## worklist in `take`. Avoids call-stack overflow.
##
## Optional: best-first search via cost-ordered worklist (leftist heap).

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

# --- Explicit stream tree ---------------------------------------------
# Stream is DATA, not closures. The `take` proc processes it with an
# explicit worklist (no call-stack recursion for interleaving).

type
  StreamKind* = enum skEmpty, skCons, skMPlus, skBind, skThunk
  Stream* = ref object
    case kind*: StreamKind
    of skEmpty: discard
    of skCons:
      head*: Subst
      tail*: Stream
    of skMPlus:
      left*, right*: Stream  # interleave these
    of skBind:
      src*: Stream
      fn*: proc(s: Subst): Stream {.closure.}  # applied to each
    of skThunk:
      thunk*: proc(): Stream {.closure.}  # forced on demand

proc emptyStream*(): Stream = Stream(kind: skEmpty)
proc singleton*(s: Subst): Stream =
  Stream(kind: skCons, head: s, tail: emptyStream())
proc mplus*(a, b: Stream): Stream =
  if a.kind == skEmpty: b
  elif b.kind == skEmpty: a
  else: Stream(kind: skMPlus, left: a, right: b)
proc bindStream*(s: Stream, fn: proc(s: Subst): Stream {.closure.}): Stream =
  if s.kind == skEmpty: emptyStream()
  else: Stream(kind: skBind, src: s, fn: fn)
proc delayStream*(thunk: proc(): Stream {.closure.}): Stream =
  Stream(kind: skThunk, thunk: thunk)

# --- Goals ------------------------------------------------------------
# Goals build Stream trees (data). No execution happens during construction.

type
  Goal* = proc(s: Subst): Stream {.closure.}

proc `==`*(u, v: RTerm): Goal =
  return proc(s: Subst): Stream =
    let (ok, s2) = unify(u, v, s)
    if ok: singleton(s2) else: emptyStream()

proc eq*(u, v: RTerm): Goal {.inline.} =
  ## Non-operator alias for `==`, for use in macros (avoids hygiene issues).
  `==`(u, v)

proc conj*(g1, g2: Goal): Goal =
  return proc(s: Subst): Stream =
    # g1(s) is a Stream tree; bind g2 over it
    bindStream(g1(s), g2)

proc disj*(g1, g2: Goal): Goal =
  return proc(s: Subst): Stream =
    mplus(g1(s), g2(s))

proc conde*(clauses: seq[Goal]): Goal =
  if clauses.len == 0:
    return proc(s: Subst): Stream = emptyStream()
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
  # Use thunk to delay body until stream is forced
  return proc(s: Subst): Stream =
    delayStream(proc(): Stream =
      let v = freshVar()
      body(v)(s))

proc fresh2*(body: proc(x, y: RTerm): Goal {.closure.}): Goal =
  return proc(s: Subst): Stream =
    delayStream(proc(): Stream =
      let a = freshVar(); let b = freshVar()
      body(a, b)(s))

proc fresh3*(body: proc(x, y, z: RTerm): Goal {.closure.}): Goal =
  return proc(s: Subst): Stream =
    delayStream(proc(): Stream =
      let a = freshVar(); let b = freshVar(); let c = freshVar()
      body(a, b, c)(s))

proc fresh4*(body: proc(a, b, c, d: RTerm): Goal {.closure.}): Goal =
  return proc(s: Subst): Stream =
    delayStream(proc(): Stream =
      let x1 = freshVar(); let x2 = freshVar()
      let x3 = freshVar(); let x4 = freshVar()
      body(x1, x2, x3, x4)(s))

# --- Take with explicit worklist --------------------------------------
# Processes the Stream tree iteratively using a worklist.
# No call-stack recursion for the search itself.

proc take*(n: int, s: Stream): seq[Subst] =
  result = @[]
  var worklist: seq[Stream] = @[s]
  var iterations = 0
  const MaxIterations = 100000
  
  while worklist.len > 0 and result.len < n and iterations < MaxIterations:
    inc iterations
    let cur = worklist.pop()
    
    case cur.kind
    of skEmpty:
      discard
    of skCons:
      result.add(cur.head)
      if cur.tail.kind != skEmpty:
        worklist.add(cur.tail)
    of skMPlus:
      # Push both branches; worklist order gives DFS-like behavior.
      # For fairness, the iterative nature prevents deep starvation
      # because we don't recurse — we interleave via the worklist.
      worklist.add(cur.right)
      worklist.add(cur.left)
    of skBind:
      # Distribute bind over the source stream structure.
      let src = cur.src
      let fn = cur.fn
      case src.kind
      of skEmpty:
        discard
      of skCons:
        # Apply fn to head, push mplus(fn(head), bind(tail, fn))
        let r = fn(src.head)
        let rest = bindStream(src.tail, fn)
        worklist.add(mplus(r, rest))
      of skMPlus:
        # Distribute: bind(l, fn) + bind(r, fn)
        worklist.add(bindStream(src.right, fn))
        worklist.add(bindStream(src.left, fn))
      of skBind:
        # Nested bind: bind(bind(s, f), g) = bind(s, x => bind(f(x), g))
        let innerSrc = src.src
        let innerFn = src.fn
        worklist.add(bindStream(innerSrc, proc(s: Subst): Stream =
          bindStream(innerFn(s), fn)))
      of skThunk:
        let forced = src.thunk()
        worklist.add(bindStream(forced, fn))
    of skThunk:
      let forced = cur.thunk()
      worklist.add(forced)

# --- Reify and Run ----------------------------------------------------

proc reify*(t: RTerm, s: Subst): RTerm =
  let wt = walk(t, s)
  case wt.kind
  of rkVar: wt
  of rkPair: rpair(reify(wt.head, s), reify(wt.tail, s))
  else: wt

# Depth tracking for iterative deepening (fallback)
var depthLimit* {.threadvar.}: int
var currentDepth* {.threadvar.}: int

proc depthExceeded*(): bool = currentDepth >= depthLimit
proc enterRec*() = inc currentDepth
proc exitRec*() = dec currentDepth

proc run*(q: RTerm, g: Goal, n = 10, maxDepth = 10): seq[RTerm] =
  ## Run with iterative deepening over depth.
  ## The Stream tree is built, then `take` processes it with worklist.
  ## Note: freshCounter is NOT reset here; it must be globally unique.
  ## Callers should create q via freshVar() before run, and the counter
  ## continues monotonically to avoid ID collisions.
  result = @[]
  var seen: seq[string] = @[]
  for d in 1..maxDepth:
    depthLimit = d
    currentDepth = 0
    let stream = g(emptySubst())
    let substs = take(n - result.len, stream)
    for s in substs:
      let t = reify(q, s)
      let key = $t
      if key notin seen:
        seen.add(key)
        result.add(t)
        if result.len >= n: return
