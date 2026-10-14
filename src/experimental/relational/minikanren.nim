## Relational engine — Track C (independent, explicit search tree)
##
## Uses an explicit Stream tree (not closures on call stack) for the
## search. Interleaving (mplus) is data, processed by an explicit
## worklist in `take`. Avoids call-stack overflow.
##
## Optional: best-first search via cost-ordered worklist (leftist heap).

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
  
  # SetEqConstraint: set(cells) must equal set(values).
  # cells: the logic variables (or ground terms)
  # values: the required values (ground terms)
  # This is a global constraint — stronger than pairwise =/=.
  # Propagation: when a cell binds to v, remove v from values and the
  # cell from cells. If one cell and one value remain, bind them
  # (the "naked single" — the last cell is determined).
  SetEqConstraint* = object
    cells*: seq[RTerm]
    values*: seq[RTerm]
  
  # State extends Subst with constraint stores.
  # diseqs: list of (u, v) pairs that must NOT become equal.
  # seteqs: list of set-equality constraints for global propagation.
  State* = object
    subst*: Subst
    diseqs*: seq[(RTerm, RTerm)]
    seteqs*: seq[SetEqConstraint]

proc emptySubst*(): Subst = @[]
proc emptyState*(): State = State(subst: @[], diseqs: @[], seteqs: @[])

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
      head*: State
      tail*: Stream
    of skMPlus:
      left*, right*: Stream  # interleave these
    of skBind:
      src*: Stream
      fn*: proc(s: State): Stream {.closure.}  # applied to each
    of skThunk:
      thunk*: proc(): Stream {.closure.}  # forced on demand

proc emptyStream*(): Stream = Stream(kind: skEmpty)
proc singleton*(s: State): Stream =
  Stream(kind: skCons, head: s, tail: emptyStream())
proc mplus*(a, b: Stream): Stream =
  if a.kind == skEmpty: b
  elif b.kind == skEmpty: a
  else: Stream(kind: skMPlus, left: a, right: b)
proc bindStream*(s: Stream, fn: proc(s: State): Stream {.closure.}): Stream =
  if s.kind == skEmpty: emptyStream()
  elif s.kind == skBind:
    # Flatten nested bind eagerly: bind(bind(src, f), g) = bind(src, x => bind(f(x), g))
    # This ensures conj associativity. Doing it here (construction time)
    # rather than in take (execution time) avoids worklist ordering issues.
    let innerSrc = s.src
    let innerFn = s.fn
    let outerFn = fn
    bindStream(innerSrc, proc(x: State): Stream {.closure.} =
      bindStream(innerFn(x), outerFn))
  else: Stream(kind: skBind, src: s, fn: fn)
proc delayStream*(thunk: proc(): Stream {.closure.}): Stream =
  Stream(kind: skThunk, thunk: thunk)

# --- Goals ------------------------------------------------------------
# Goals build Stream trees (data). No execution happens during construction.
# Goals now operate on State (subst + constraint store), not just Subst.

type
  Goal* = proc(s: State): Stream {.closure.}

proc checkDiseqs(s: State): bool =
  ## Check if any disequality constraint is violated in state s.
  ## A disequality (u, v) is violated if u and v unify without new bindings
  ## (i.e., they are already equal under the current subst).
  for (u, v) in s.diseqs:
    let (ok, s2) = unify(u, v, s.subst)
    if ok and s2.len == s.subst.len:
      # They unify with no new bindings → already equal → violation
      return false
  true

proc propagateSetEqs(s: State): tuple[ok: bool, s2: State] =
  ## Propagate set-equality constraints to fixpoint.
  ## For each setEq(cells, values):
  ## - Walk cells; partition into bound and unbound
  ## - Bound cells must have values in the values set; remove them
  ## - If one unbound cell and one value remain: bind them (naked single)
  ## - If counts mismatch: fail
  ## Returns (false, s) on failure, (true, s2) with updated state.
  var subst = s.subst
  var seteqs = s.seteqs
  var changed = true
  
  while changed:
    changed = false
    var newSeteqs: seq[SetEqConstraint] = @[]
    
    for ce in seteqs:
      var unboundCells: seq[RTerm] = @[]
      var remainingValues = ce.values
      
      # Partition cells into bound/unbound, checking bound values
      for c in ce.cells:
        let wc = walk(c, subst)
        if wc.kind == rkVar:
          unboundCells.add(c)  # keep original (may be var)
        else:
          # Bound: check wc is in remainingValues, remove it
          var foundIdx = -1
          for i, v in remainingValues:
            let (ok, _) = unify(wc, v, subst)
            # unify with no new bindings means equal
            if ok:
              # Check if they're already equal (no new bindings needed)
              let wv = walk(v, subst)
              if $wc == $wv:  # structural equality via string (ground terms)
                foundIdx = i
                break
          if foundIdx < 0:
            return (false, s)  # bound to value not in set → fail
          remainingValues.delete(foundIdx)
      
      # Check counts
      if unboundCells.len != remainingValues.len:
        return (false, s)  # mismatch → fail
      
      if unboundCells.len == 0:
        # All bound, all values used → constraint satisfied, drop it
        changed = true  # (removing a constraint counts as change)
      elif unboundCells.len == 1:
        # Naked single: the last cell must be the last value
        let (ok, subst2) = unify(unboundCells[0], remainingValues[0], subst)
        if not ok:
          return (false, s)
        subst = subst2
        changed = true
        # Constraint satisfied, don't add to newSeteqs
      else:
        # Still have multiple unbound: keep the reduced constraint
        if unboundCells.len < ce.cells.len or remainingValues.len < ce.values.len:
          changed = true
        newSeteqs.add(SetEqConstraint(cells: unboundCells, values: remainingValues))
    
    seteqs = newSeteqs
  
  (true, State(subst: subst, diseqs: s.diseqs, seteqs: seteqs))

proc `==`*(u, v: RTerm): Goal =
  return proc(s: State): Stream =
    let (ok, s2) = unify(u, v, s.subst)
    if not ok:
      return emptyStream()
    var s2state = State(subst: s2, diseqs: s.diseqs, seteqs: s.seteqs)
    # Constraint propagation: check disequalities
    if not checkDiseqs(s2state):
      return emptyStream()
    # Propagate set-equality constraints (may bind more vars)
    let (pok, pstate) = propagateSetEqs(s2state)
    if not pok:
      return emptyStream()
    # Re-check disequalities after setEq propagation (new bindings)
    if not checkDiseqs(pstate):
      return emptyStream()
    singleton(pstate)

proc `=/=`*(u, v: RTerm): Goal =
  ## Disequality: u and v must NOT become equal.
  ## - If they are already equal (unify with no new bindings): fail.
  ## - If they cannot unify: succeed (constraint satisfied).
  ## - Otherwise: store the constraint and succeed (check later).
  return proc(s: State): Stream =
    let (ok, s2) = unify(u, v, s.subst)
    if not ok:
      # Cannot unify → disequality satisfied
      return singleton(s)
    if s2.len == s.subst.len:
      # Already equal → disequality violated
      return emptyStream()
    # Could become equal later → store constraint
    var diseqs2 = s.diseqs
    diseqs2.add((u, v))
    singleton(State(subst: s.subst, diseqs: diseqs2, seteqs: s.seteqs))

proc setEqo*(cells: seq[RTerm], values: seq[RTerm]): Goal =
  ## Global set-equality constraint: set(cells) == set(values).
  ## cells: logic variables (or ground terms)
  ## values: the required values (ground terms, e.g. [1..9])
  ## Propagation happens in == via propagateSetEqs.
  return proc(s: State): Stream =
    var seteqs2 = s.seteqs
    seteqs2.add(SetEqConstraint(cells: cells, values: values))
    let s2 = State(subst: s.subst, diseqs: s.diseqs, seteqs: seteqs2)
    # Run initial propagation (may fail immediately if inconsistent)
    let (ok, pstate) = propagateSetEqs(s2)
    if ok: singleton(pstate) else: emptyStream()

proc computeDomain*(v: RTerm, s: State): seq[RTerm] =
  ## Compute the current domain of variable v from the constraint store.
  ## The domain is implied by the conjunction of constraints:
  ## - Start with values from setEq constraints containing v
  ## - Remove values taken by bound peers in those constraints
  ## - Remove values that would violate disequalities
  ## This is the "finite domain modeled by conj" — the domain isn't
  ## a static disjunction, but derived from the current constraints.
  let wv = walk(v, s.subst)
  if wv.kind != rkVar:
    return @[wv]  # already bound: singleton domain
  
  var possible: seq[string] = @[]  # use string keys for dedup
  var possibleTerms: seq[RTerm] = @[]
  
  # Collect from setEq constraints
  for ce in s.seteqs:
    var containsV = false
    for c in ce.cells:
      let wc = walk(c, s.subst)
      if wc.kind == rkVar and wc.id == wv.id:
        containsV = true
        break
    if containsV:
      for val in ce.values:
        # Check if val is taken by a bound peer
        var taken = false
        for c in ce.cells:
          let wc = walk(c, s.subst)
          if wc.kind != rkVar and $wc == $val:
            taken = true
            break
        if not taken:
          let key = $val
          if key notin possible:
            possible.add(key)
            possibleTerms.add(val)
  
  # Filter by disequalities: if v =/= x and x is bound to val, remove val
  result = @[]
  for i, val in possibleTerms:
    var violates = false
    for (a, b) in s.diseqs:
      let wa = walk(a, s.subst)
      let wb = walk(b, s.subst)
      # Case: v =/= wb where wb is ground and equals val
      if wa.kind == rkVar and wa.id == wv.id and wb.kind != rkVar and $wb == $val:
        violates = true
        break
      if wb.kind == rkVar and wb.id == wv.id and wa.kind != rkVar and $wa == $val:
        violates = true
        break
    if not violates:
      result.add(val)

proc eq*(u, v: RTerm): Goal {.inline.} =
  ## Non-operator alias for `==`, for use in macros (avoids hygiene issues).
  `==`(u, v)

proc conj*(g1, g2: Goal): Goal =
  return proc(s: State): Stream =
    # g1(s) is a Stream tree; bind g2 over it
    bindStream(g1(s), g2)

proc disj*(g1, g2: Goal): Goal =
  return proc(s: State): Stream =
    mplus(g1(s), g2(s))

proc branchMostConstrained*(vars: seq[RTerm]): Goal =
  ## Fail-first search: branch on the most constrained variable.
  ## - Compute current domain for each unbound var (from constraints)
  ## - Pick the var with smallest domain > 1 (most constrained)
  ## - Disjoin over its domain values, recurse
  ## - If all bound: succeed. If any domain empty: fail.
  ## The order is controlled dynamically — this is the "conj whose
  ## order we can control": we choose which var to branch on based
  ## on the current constraint store, not a fixed order.
  return proc(s: State): Stream =
    # Find unbound vars and their domains
    var bestVar: RTerm = nil
    var bestDomain: seq[RTerm] = @[]
    var allBound = true
    
    for v in vars:
      let wv = walk(v, s.subst)
      if wv.kind == rkVar:
        allBound = false
        let dom = computeDomain(v, s)
        if dom.len == 0:
          return emptyStream()  # empty domain → fail fast
        if bestVar.isNil or dom.len < bestDomain.len:
          bestVar = v
          bestDomain = dom
    
    if allBound:
      return singleton(s)
    
    # Branch on bestVar's domain
    # Build disjunction: (bestVar == d1 AND recurse) OR (bestVar == d2 AND recurse) ...
    var g: Goal = nil
    for d in bestDomain:
      let val = d
      let bv = bestVar
      let branch = conj(`==`(bv, val), branchMostConstrained(vars))
      if g.isNil:
        g = branch
      else:
        g = disj(g, branch)
    
    g(s)

proc conde*(clauses: seq[Goal]): Goal =
  if clauses.len == 0:
    return proc(s: State): Stream = emptyStream()
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
  return proc(s: State): Stream =
    delayStream(proc(): Stream =
      let v = freshVar()
      body(v)(s))

proc fresh2*(body: proc(x, y: RTerm): Goal {.closure.}): Goal =
  return proc(s: State): Stream =
    delayStream(proc(): Stream =
      let a = freshVar(); let b = freshVar()
      body(a, b)(s))

proc fresh3*(body: proc(x, y, z: RTerm): Goal {.closure.}): Goal =
  return proc(s: State): Stream =
    delayStream(proc(): Stream =
      let a = freshVar(); let b = freshVar(); let c = freshVar()
      body(a, b, c)(s))

proc fresh4*(body: proc(a, b, c, d: RTerm): Goal {.closure.}): Goal =
  return proc(s: State): Stream =
    delayStream(proc(): Stream =
      let x1 = freshVar(); let x2 = freshVar()
      let x3 = freshVar(); let x4 = freshVar()
      body(x1, x2, x3, x4)(s))

# --- Take with explicit worklist --------------------------------------
# Processes the Stream tree iteratively using a worklist.
# No call-stack recursion for the search itself.
#
# FAIRNESS: The worklist is FIFO (queue), not LIFO (stack).
# This gives interleaved search: when skMPlus pushes left and right,
# they are processed in order, and each branch's children go to the
# back. Infinite branches cannot starve finite ones because we
# round-robin through the queue. This is the standard miniKanren
# interleaving, implemented iteratively.

proc take*(n: int, s: Stream): seq[State] =
  result = @[]
  var worklist: seq[Stream] = @[s]
  var head = 0  # FIFO index; avoids O(n) delete(0)
  var iterations = 0
  const MaxIterations = 100000
  
  while head < worklist.len and result.len < n and iterations < MaxIterations:
    inc iterations
    let cur = worklist[head]
    inc head
    # Periodically compact to avoid unbounded growth of the seq
    if head > 1000 and head * 2 > worklist.len:
      worklist = worklist[head..^1]
      head = 0
    
    case cur.kind
    of skEmpty:
      discard
    of skCons:
      result.add(cur.head)
      if cur.tail.kind != skEmpty:
        worklist.add(cur.tail)
    of skMPlus:
      # Push both branches; FIFO worklist gives interleaved (fair) search.
      # Left is processed before right, and their children go to the back,
      # so infinite branches round-robin with finite ones instead of starving them.
      worklist.add(cur.left)
      worklist.add(cur.right)
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
        worklist.add(bindStream(innerSrc, proc(s: State): Stream =
          bindStream(innerFn(s), fn)))
      of skThunk:
        let forced = src.thunk()
        worklist.add(bindStream(forced, fn))
    of skThunk:
      let forced = cur.thunk()
      worklist.add(forced)

# --- Reify and Run ----------------------------------------------------

proc reify*(t: RTerm, s: State): RTerm =
  let wt = walk(t, s.subst)
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
    let stream = g(emptyState())
    let states = take(n - result.len, stream)
    for s in states:
      let t = reify(q, s)
      let key = $t
      if key notin seen:
        seen.add(key)
        result.add(t)
        if result.len >= n: return
