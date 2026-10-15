## Issue #42: termination checking for mutually recursive declaration groups.
##
## Size-change-flavored criterion over PreTerm, reusing #36's walk style:
## build the call graph of a declaration group, record for each call edge
## which argument positions are structurally smaller (a bare variable bound
## by the caller's pattern — the same "direct subterm" notion as
## checkStructuralRec), and accept the group iff every directed cycle
## contains at least one decreasing edge.
##
## NOTE (scope of this first chunk): pure graph machinery plus the cycle
## check over hand-supplied MutDecl inputs. Wiring into the elaborator's
## declaration processing (group detection across defs in one block and
## extracting patVars from clause patterns) is the next chunk.
##
## Public API:
##   buildCallGraph(decls) -> seq[CallEdge]
##   checkMutualBlock(decls)  # raises MutualTerminationError on a
##                            # decrease-free cycle, naming the cycle.

import std/[tables, strutils]
import preterm

type
  MutualTerminationError* = object of CatchableError
    loc*: Loc

  CallEdge* = object
    caller*, callee*: string
    decArgs*: seq[int]  ## 0-based argument positions that are structurally smaller
    loc*: Loc

  MutDecl* = object
    name*: string
    body*: PreTerm
    patVars*: seq[string]  ## pattern-bound vars eligible as "structurally smaller"

proc mkMutErr(loc: Loc, msg: string): ref MutualTerminationError =
  (ref MutualTerminationError)(msg: msg, loc: loc)

proc flattenSpine(t: PreTerm): seq[PreTerm] =
  ## Application spine, function first.
  var h = t
  var rev: seq[PreTerm] = @[]
  while h.kind == pkApp:
    rev.add(h.c2)
    h = h.c1
  result.add(h)
  for i in countdown(rev.high, 0):
    result.add(rev[i])

proc walkBody(t: PreTerm, d: MutDecl, names: seq[string],
              edges: var seq[CallEdge]) =
  if t == nil: return
  case t.kind
  of pkApp:
    let sp = flattenSpine(t)
    if sp[0].kind == pkVar and sp[0].name in names:
      var dec: seq[int] = @[]
      for i in 1 ..< sp.len:
        if sp[i].kind == pkVar and sp[i].name in d.patVars:
          dec.add(i - 1)
      edges.add(CallEdge(caller: d.name, callee: sp[0].name,
                         decArgs: dec, loc: t.loc))
    for s in sp:
      walkBody(s, d, names, edges)
  of pkLam, pkPi, pkSigma, pkPair, pkLet, pkAnn:
    if t.c1 != nil: walkBody(t.c1, d, names, edges)
    if t.c2 != nil: walkBody(t.c2, d, names, edges)
    if t.c3 != nil: walkBody(t.c3, d, names, edges)
  of pkFst, pkSnd, pkProj:
    walkBody(t.c1, d, names, edges)
  else:
    discard

proc buildCallGraph*(decls: seq[MutDecl]): seq[CallEdge] =
  ## Collect one edge per call to a group member in every body.
  var names: seq[string] = @[]
  for d in decls: names.add(d.name)
  for d in decls:
    walkBody(d.body, d, names, result)

proc checkCycles(edges: seq[CallEdge]) =
  ## Reject any directed cycle with no decreasing edge. Naive per-start DFS:
  ## declaration groups are tiny, so no visited-set pruning is needed (and
  ## pruning would risk missing cycles through already-visited nodes).
  var adj = initTable[string, seq[int]]()
  for i, e in edges:
    adj.mgetOrPut(e.caller, @[]).add(i)
  for start in adj.keys:
    var onStack: seq[string] = @[start]
    var edgePath: seq[int] = @[]
    var itStack: seq[(string, int)] = @[(start, 0)]
    while itStack.len > 0:
      let (node, ni) = itStack[^1]
      let nbrs = adj.getOrDefault(node, @[])
      if ni >= nbrs.len:
        discard itStack.pop()
        if edgePath.len > 0: discard edgePath.pop()
        discard onStack.pop()
        continue
      itStack[^1] = (node, ni + 1)
      let e = edges[nbrs[ni]]
      let pos = onStack.find(e.callee)
      if pos >= 0:
        let cyc = edgePath[pos .. ^1] & @[nbrs[ni]]
        var hasDec = false
        for ci in cyc:
          if edges[ci].decArgs.len > 0:
            hasDec = true
            break
        if not hasDec:
          var names: seq[string] = @[]
          for ci in cyc: names.add(edges[ci].caller)
          names.add(e.callee)
          # Deterministic rotation: start at the lexicographically
          # smallest name so the message is stable regardless of DFS
          # start order.
          let cycle = names[0 .. ^2]  # drop the closing repeat
          var startPos = 0
          for i in 1 ..< cycle.len:
            if cycle[i] < cycle[startPos]: startPos = i
          var ordered = cycle[startPos .. ^1] & cycle[0 ..< startPos]
          ordered.add(ordered[0])
          raise mkMutErr(e.loc,
            "mutually recursive group has a cycle with no decreasing " &
            "argument: " & ordered.join(" -> ") &
            "; every cycle must contain a call on a structurally smaller " &
            "argument (issue #42)")
      else:
        onStack.add(e.callee)
        edgePath.add(nbrs[ni])
        itStack.add((e.callee, 0))

proc checkMutualBlock*(decls: seq[MutDecl]) =
  ## Accept iff every directed cycle in the group's call graph contains a
  ## decreasing edge. Raises MutualTerminationError otherwise.
  checkCycles(buildCallGraph(decls))
