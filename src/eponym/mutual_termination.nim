## Issue #42: size-change termination for mutually recursive declaration groups.
##
## For each call site the elaborator supplies a *size-change graph*: arcs from
## the caller's formals (index 0 = scrutinee) to the callee's formals, labeled
## strict (`<`) when the argument is a strict subterm of the caller's formal
## and non-strict (`<=`) when it is the formal itself. The checker computes the
## closure under graph composition and requires every composed self-loop graph
## to contain a strict self-arc — the Lee/Jones/Ben-Amram criterion. An
## infinite call path would repeat some function with an idempotent composed
## graph; a strict self-arc makes infinite strict decrease impossible.
##
## NOTE on an earlier, unsound revision: "every directed cycle contains a
## decreasing edge" does NOT suffice. Counterexample:
##   f (suc (suc zero)) = g (suc zero);  g (suc m) = f (suc (suc zero))
## loops forever (`f (suc (suc zero)) -> g (suc zero) -> f (suc (suc zero))`),
## yet the f->g edge decreases (n is a subterm). The decrease must *thread
## through* the cycle — g discards its decreased argument and calls f on a
## constant — so composition along the cycle is required, not a per-edge test.
##
## Public API:
##   checkSct(calls: seq[SctCall])  # raises SctError on violation, naming a
##                                  # witness cycle.

import std/[tables, strutils, sets, hashes, algorithm, deques]
import preterm

type
  SctError* = object of CatchableError
    loc*: Loc

  SctArc* = tuple[src: int, strict: bool, tgt: int]
    ## An arc from the caller's formal `src` (0 = scrutinee) to the callee's
    ## formal `tgt`; `strict` = the argument is a *strict* subterm of the
    ## caller's formal (vs `<=`, the formal itself).

  SctCall* = object
    caller*, callee*: string
    nSrc*, nTgt*: int   ## formal counts (for documentation; arcs carry indices)
    arcs*: seq[SctArc]
    loc*: Loc

proc mkSctErr(loc: Loc, msg: string): ref SctError =
  (ref SctError)(msg: msg, loc: loc)

proc normArcs(arcs: seq[SctArc]): seq[SctArc] =
  ## Sorted, deduplicated; a strict arc subsumes a non-strict one on the
  ## same (src, tgt) pair.
  var strictSeen = initHashSet[(int, int)]()
  for (s, st, t) in arcs:
    if st: strictSeen.incl((s, t))
  var seen = initHashSet[(int, int)]()
  for (s, _, t) in arcs:
    if (s, t) notin seen:
      seen.incl((s, t))
      result.add((s, (s, t) in strictSeen, t))
  result.sort(proc(a, b: SctArc): int =
    if a.src != b.src: cmp(a.src, b.src)
    elif a.tgt != b.tgt: cmp(a.tgt, b.tgt)
    else: cmp(a.strict, b.strict))

proc compose*(a, b: seq[SctArc]): seq[SctArc] =
  ## Compose size-change graphs: a is f->g, b is g->h; result is f->h.
  ## An arc is strict if either leg is strict.
  var raw: seq[SctArc] = @[]
  for (x, s1, y) in a:
    for (y2, s2, z) in b:
      if y == y2:
        raw.add((x, s1 or s2, z))
  normArcs(raw)

proc witnessCycle(caller: string,
                  adj: Table[string, seq[(string, Loc)]]): seq[string] =
  ## Shortest directed cycle through `caller` (BFS); empty if none.
  ## Returns [caller, ..., caller].
  var prev = initTable[string, string]()
  var q = initDeque[string]()
  q.addLast(caller)
  prev[caller] = ""
  while q.len > 0:
    let u = q.popFirst()
    for (v, _) in adj.getOrDefault(u, @[]):
      if v == caller and u != caller:
        # cycle: caller -> ... -> u -> caller; prev-chain gives u -> caller
        var rev: seq[string] = @[]
        var cur = u
        while cur != caller:
          rev.add(cur)
          cur = prev[cur]
        rev.reverse()
        return @[caller] & rev & @[caller]
      if v notin prev:
        prev[v] = u
        q.addLast(v)
  @[]

proc checkSct*(calls: seq[SctCall]) =
  ## Size-change termination over the call-site graphs. Raises SctError
  ## (naming a witness cycle) if some function admits a composed self-loop
  ## with no strict self-arc.
  type EKey = tuple[caller, callee: string]
  var closure = initTable[EKey, seq[seq[SctArc]]]()
  var adj = initTable[string, seq[(string, Loc)]]()
  var edgeLoc = initTable[EKey, Loc]()

  proc addEdge(closure: var Table[EKey, seq[seq[SctArc]]],
               adj: Table[string, seq[(string, Loc)]],
               caller, callee: string, arcs: seq[SctArc], loc: Loc) =
    let k: EKey = (caller, callee)
    let g = normArcs(arcs)
    if g notin closure.getOrDefault(k, @[]):
      closure.mgetOrPut(k, @[]).add(g)
      if k notin edgeLoc: edgeLoc[k] = loc
      # extend right: (caller->callee);(callee->h)
      for (h, _) in adj.getOrDefault(callee, @[]):
        let kh: EKey = (callee, h)
        for hh in closure.getOrDefault(kh, @[]):
          addEdge(closure, adj, caller, h, compose(g, hh), loc)
      # extend left: (h->caller);(caller->callee)
      for h in adj.keys:
        let kh: EKey = (h, caller)
        if kh == k: continue
        for hh in closure.getOrDefault(kh, @[]):
          addEdge(closure, adj, h, callee, compose(hh, g), loc)

  for c in calls:
    # adjacency first, so extensions see the full graph
    adj.mgetOrPut(c.caller, @[]).add((c.callee, c.loc))
  for c in calls:
    addEdge(closure, adj, c.caller, c.callee, c.arcs, c.loc)

  # Deterministic failure order: collect all violating functions, sort.
  var violators: seq[string] = @[]
  for k in closure.keys:
    if k.caller != k.callee: continue
    for h in closure[k]:
      var ok = false
      for (x, st, y) in h:
        if x == y and st:
          ok = true
          break
      if not ok:
        violators.add(k.caller)
        break
  violators.sort()
  if violators.len > 0:
    let f = violators[0]
    let cyc = witnessCycle(f, adj)
    let cycStr = if cyc.len > 0: cyc.join(" -> ")
                 else: f & " -> " & f
    raise mkSctErr(edgeLoc.getOrDefault((f, f), noLoc),
      "mutually recursive group may not terminate: no strictly " &
      "decreasing argument threads through the cycle " & cycStr &
      " (every composed call cycle through '" & f &
      "' needs an argument that is a strict subterm of the caller's " &
      "formal; issue #42)")
