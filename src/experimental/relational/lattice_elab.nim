## Lattice-monotone elaboration prototype — issue #170.
##
## The relational spec (rel_elab_dep.checko/infero) rewritten so that no rule
## ever branches: there are no disjuncts over alternatives, no logic
## variables, no streams. Instead, elaboration threads an explicit state
## (LatState) whose values form lattices:
##
## - every node (a term/type occurrence) carries a possibility set of heads
##   (Shape); top = all heads, bottom = the empty set;
## - every node carries a NatLat for natural-number indices
##   (unknown / exact k / bottom);
## - nodes are related by a union-find: equating two nodes meets their
##   lattices, and congruent pair constructions union their kids pairwise
##   (congruence closure — the e-node skeleton from the issue).
##
## Every rule is a single deterministic sequence of meets. Contradiction is
## a *value in the state* (bottom), detected by the meet operation at the
## step that creates it, with provenance (which node, which constraint) —
## never by exhausting a search stream, never by cut.
##
## Deliberate refinements over the spec (documented, not hidden):
## - The spec rejects when the expected type is not *syntactically* a
##   pi/vec (tagOf check); the lattice version *refines* an unknown type
##   node to {hPi}/{hVec} and materializes its structure. Refine, don't
##   reject (Aaron's principle).
## - nil's `disj(idx == zero, idx == rint(0))` becomes a single
##   meetNat(idx, exact 0): both index spellings map to exact 0 in the
##   NatLat, so the representation case-split disappears entirely.
##
## On the ground Vec-fragment corpus the term shapes are degenerate
## (singletons recorded at numbering); the lattice work happens on type
## nodes. The term-side lattice is infrastructure for the synthesis
## direction (issue step 5): running the relation backwards starts from a
## different partial state and saturates.

import minikanren
import rel_elab_dep  # constructors + isNatLit
import options
import strutils

# --- Lattices ---------------------------------------------------------------

type
  Head* = enum
    hNil, hCons, hZero, hSuc, hNatLit, hLam, hApp, hVar, hPi,
    hNat, hVec, hUniv

const AllHeads*: set[Head] = {hNil, hCons, hZero, hSuc, hNatLit, hLam, hApp,
                              hVar, hPi, hNat, hVec, hUniv}

type
  NatLat* = object
    ## Lattice over natural numbers: unknown (top), exact k, or bottom.
    bot*: bool
    known*: bool
    val*: int

proc natTop*(): NatLat = NatLat(bot: false, known: false, val: 0)
proc natExact*(k: int): NatLat = NatLat(bot: false, known: true, val: k)
proc natBot*(): NatLat = NatLat(bot: true, known: false, val: 0)

proc meetNat*(a, b: NatLat): NatLat =
  if a.bot or b.bot: return natBot()
  if a.known and b.known:
    if a.val == b.val: return a
    return natBot()
  if a.known: return a
  if b.known: return b
  return natTop()

proc `$`*(n: NatLat): string =
  if n.bot: "bot"
  elif n.known: "exact(" & $n.val & ")"
  else: "top"

# --- State -------------------------------------------------------------------

type
  ConstrKind = enum ckNone, ckAtom, ckPair
  Constr = object
    case kind: ConstrKind
    of ckNone: discard
    of ckAtom: atomName: string
    of ckPair:
      tag: string
      kids: seq[int]

  FailInfo* = object
    node*: string
    want*: string
    have*: string

  LatState* = object
    parent*: seq[int]
    descs*: seq[string]
    shape*: seq[set[Head]]
    natl*: seq[NatLat]
    constr*: seq[Constr]
    failure*: Option[FailInfo]

proc `$`*(f: FailInfo): string =
  "bottom at " & f.node & ": wanted " & f.want & ", had " & f.have

proc initLatState*(): LatState =
  LatState(parent: @[], descs: @[], shape: @[], natl: @[],
           constr: @[], failure: none(FailInfo))

proc setFailure(st: var LatState, node, want, have: string) =
  ## Bottom is monotone: the first contradiction sticks, with provenance.
  if st.failure.isNone:
    st.failure = some(FailInfo(node: node, want: want, have: have))

proc find*(st: var LatState, id: int): int =
  var r = id
  while st.parent[r] != r: r = st.parent[r]
  var cur = id
  while st.parent[cur] != r:
    let nxt = st.parent[cur]
    st.parent[cur] = r
    cur = nxt
  r

proc shapeOf(t: RTerm): set[Head] =
  ## Ground truth for a node: the head actually present. Logic variables
  ## and unrecognized heads are top (no information).
  case t.kind
  of rkVar: AllHeads
  of rkAtom:
    case t.name
    of "nil": {hNil}
    of "zero": {hZero}
    of "nat": {hNat}
    of "univ": {hUniv}
    else:
      if isNatLit(t): {hNatLit} else: AllHeads
  of rkPair:
    if t.head.kind != rkAtom: return AllHeads
    case t.head.name
    of "cons": {hCons}
    of "suc": {hSuc}
    of "lam": {hLam}
    of "app": {hApp}
    of "var": {hVar}
    of "pi": {hPi}
    of "vec": {hVec}
    else: AllHeads

proc natLatOf(t: RTerm): NatLat =
  ## Ground truth for a node's numeric value, where defined.
  case t.kind
  of rkAtom:
    if t.name == "zero": return natExact(0)
    if isNatLit(t):
      try: return natExact(parseInt(t.name))
      except ValueError: return natTop()
    return natTop()
  of rkPair:
    if t.head.kind == rkAtom and t.head.name == "suc" and
       t.tail.kind == rkPair:
      let m = natLatOf(t.tail.head)
      if not m.bot and m.known: return natExact(m.val + 1)
    return natTop()
  of rkVar: natTop()

proc shortDesc(t: RTerm, id: int): string =
  ## O(1) node description for provenance. Rendering the full subterm here
  ## (`$t`) made numbering O(n^2) total — bench_lattice_elab showed invalid
  ## latency growing ~n^1.7 on cons-chains (886us at n=32 vs 91us at n=8).
  ## The head tag + node id locates the contradiction just as well.
  case t.kind
  of rkAtom: t.name
  of rkVar: "var#" & $id
  of rkPair:
    if t.head.kind == rkAtom: t.head.name & "#" & $id
    else: "pair#" & $id

proc number*(st: var LatState, t: RTerm): int =
  ## Assign an id to an occurrence; numbering *is* the initial refinement:
  ## ground shape and numeric value are met into the fresh top node.
  result = st.parent.len
  st.parent.add(result)
  st.descs.add(shortDesc(t, result))
  st.shape.add(shapeOf(t))
  st.natl.add(natLatOf(t))
  # Placeholder first: the recursive kid-numbering below appends to every
  # seq, so the parent's constr must reserve its slot up front (it used to
  # be appended after, misaligning constr for all pair nodes).
  st.constr.add(Constr(kind: ckNone))
  case t.kind
  of rkAtom:
    st.constr[result] = Constr(kind: ckAtom, atomName: t.name)
  of rkVar:
    discard  # stays ckNone: a genuine unknown
  of rkPair:
    let tag = if t.head.kind == rkAtom: t.head.name else: ""
    var kids: seq[int] = @[]
    var cur = t.tail
    while cur.kind == rkPair:
      kids.add(st.number(cur.head))
      cur = cur.tail
    st.constr[result] = Constr(kind: ckPair, tag: tag, kids: kids)

proc freshNode*(st: var LatState, desc: string): int =
  ## A truly unknown node: top shape, top natl, no construction.
  result = st.parent.len
  st.parent.add(result)
  st.descs.add(desc)
  st.shape.add(AllHeads)
  st.natl.add(natTop())
  st.constr.add(Constr(kind: ckNone))

proc singleOf(s: set[Head]): Head =
  doAssert s.card == 1, "singleOf on non-singleton " & $s
  for x in s: return x
  doAssert false, "unreachable"
  hNil

proc materialize(st: var LatState, r: int) =
  ## A construction-less node whose shape refined to a singleton type head
  ## gains structure with fresh kids. This is monotone refinement, not
  ## guessing: the shape already determined the head.
  if st.constr[r].kind != ckNone: return
  if st.shape[r].card != 1: return
  case singleOf(st.shape[r])
  of hPi:
    let d = st.freshNode("pi.dom")
    let c = st.freshNode("pi.cod")
    st.constr[r] = Constr(kind: ckPair, tag: "pi", kids: @[d, c])
  of hVec:
    let a = st.freshNode("vec.elem")
    let n = st.freshNode("vec.idx")
    st.constr[r] = Constr(kind: ckPair, tag: "vec", kids: @[a, n])
  of hNat:
    st.constr[r] = Constr(kind: ckAtom, atomName: "nat")
  of hUniv:
    st.constr[r] = Constr(kind: ckAtom, atomName: "univ")
  else: discard

# --- Meets (the only way the state changes) -----------------------------------

proc meetShape*(st: var LatState, id: int, s: set[Head], why: string): bool =
  let r = st.find(id)
  let ns = st.shape[r] * s
  if ns == {}:
    st.setFailure(st.descs[r], why, "shape " & $st.shape[r])
    return false
  st.shape[r] = ns
  st.materialize(r)
  true

proc meetNatIdx(st: var LatState, id: int, n: NatLat, why: string): bool =
  let r = st.find(id)
  let nn = meetNat(st.natl[r], n)
  if nn.bot:
    st.setFailure(st.descs[r], why, "index is " & $st.natl[r])
    return false
  st.natl[r] = nn
  true

proc constrAgree(a, b: Constr): bool =
  if a.kind != b.kind: return false
  case a.kind
  of ckNone: true
  of ckAtom: a.atomName == b.atomName
  of ckPair: a.tag == b.tag and a.kids.len == b.kids.len

proc unionEq(st: var LatState, a, b: int, why: string): bool =
  ## Equate two nodes: meet shapes and natls; congruent constructions
  ## union their kids pairwise (congruence closure). Bottom is detected
  ## here, locally, by the meet — never by search exhaustion.
  let ra = st.find(a)
  var rb = st.find(b)
  if ra == rb: return true
  let ns = st.shape[ra] * st.shape[rb]
  let nn = meetNat(st.natl[ra], st.natl[rb])
  if ns == {}:
    st.setFailure(st.descs[ra] & " =Type 0= " & st.descs[rb], why,
                  "shapes " & $st.shape[ra] & " vs " & $st.shape[rb])
    return false
  if nn.bot:
    st.setFailure(st.descs[ra] & " =Type 0= " & st.descs[rb], why,
                  "indices " & $st.natl[ra] & " vs " & $st.natl[rb])
    return false
  let ca = st.constr[ra]
  let cb = st.constr[rb]
  if not constrAgree(ca, cb):
    st.setFailure(st.descs[ra] & " =Type 0= " & st.descs[rb], why,
                  "constructions disagree")
    return false
  st.parent[rb] = ra
  st.shape[ra] = ns
  st.natl[ra] = nn
  if st.constr[ra].kind == ckNone:
    st.constr[ra] = cb
  st.materialize(ra)
  # Congruence: kids of equal pairs are equal.
  if ca.kind == ckPair and cb.kind == ckPair:
    for i in 0 ..< ca.kids.len:
      if not st.unionEq(ca.kids[i], cb.kids[i], why & " (congruence)"):
        return false
  true

proc kid(st: var LatState, id: int, i: int): int =
  let r = st.find(id)
  st.materialize(r)
  let c = st.constr[r]
  doAssert c.kind == ckPair, "kid: no pair construction at " & st.descs[r]
  doAssert i < c.kids.len, "kid: index out of range at " & st.descs[r]
  c.kids[i]

proc atomNameOf(st: var LatState, id: int): string =
  let r = st.find(id)
  doAssert st.constr[r].kind == ckAtom, "atomNameOf on non-atom"
  st.constr[r].atomName

proc vecNode(st: var LatState, aId, nId: int): int =
  result = st.freshNode("vec-node")
  st.shape[result] = {hVec}
  st.constr[result] = Constr(kind: ckPair, tag: "vec",
                             kids: @[st.find(aId), st.find(nId)])

proc piNode(st: var LatState, dId, cId: int): int =
  result = st.freshNode("pi-node")
  st.shape[result] = {hPi}
  st.constr[result] = Constr(kind: ckPair, tag: "pi",
                             kids: @[st.find(dId), st.find(cId)])

proc predIndex(st: var LatState, idxId: int): tuple[ok: bool, pred: int] =
  ## The tail's expected index for cons against Vec A idx: the predecessor.
  ## Structural when the index is ground; falls back to the NatLat.
  let r = st.find(idxId)
  case st.constr[r].kind
  of ckPair:
    if st.constr[r].tag == "suc" and st.constr[r].kids.len == 1:
      return (true, st.constr[r].kids[0])
    st.setFailure(st.descs[r], "successor index", "tag " & st.constr[r].tag)
    return (false, -1)
  of ckAtom:
    if isNatLit(ratom(st.constr[r].atomName)):
      let k = parseInt(st.constr[r].atomName)
      if k > 0: return (true, st.number(rint(k - 1)))
    st.setFailure(st.descs[r], "positive index", st.constr[r].atomName)
    return (false, -1)
  of ckNone:
    let nl = st.natl[r]
    if not nl.bot and nl.known and nl.val > 0:
      return (true, st.number(rint(nl.val - 1)))
    st.setFailure(st.descs[r], "positive index", "index is " & $nl)
    return (false, -1)

# --- Rules: no branching, only meets ------------------------------------------

proc inferLat(tmId: int, ctx: seq[int], st: var LatState): tuple[ok: bool, tyId: int]

proc checkLat*(tmId, tyId: int, ctx: seq[int], st: var LatState): bool =
  ## Check the term at tmId against the type at tyId. Single deterministic
  ## pass: dispatch on the term's (ground) head is rule selection, not
  ## search — exactly one rule applies, and it only meets.
  if st.failure.isSome: return false
  let rtm = st.find(tmId)
  let rc = st.constr[rtm]
  case rc.kind
  of ckAtom:
    let name = rc.atomName
    if name == "nil":
      # nil : Vec A 0. Both index spellings (zero / rint 0) are exact 0 in
      # the NatLat: one meet, no disjunction over representations.
      if not st.meetShape(tyId, {hVec}, "nil needs a Vec type"): return false
      return st.meetNatIdx(st.kid(tyId, 1), natExact(0), "nil needs index 0")
    elif name == "zero" or isNatLit(ratom(name)):
      return st.meetShape(tyId, {hNat}, "nat literal needs Nat type")
    elif name == "nat" or name == "univ":
      return st.meetShape(tyId, {hUniv}, "type former needs Type 0 type")
    else:
      st.setFailure(st.descs[rtm], "known atom head", name)
      return false
  of ckPair:
    case rc.tag
    of "cons":
      if not st.meetShape(tyId, {hVec}, "cons needs a Vec type"): return false
      let aId = st.kid(tyId, 0)
      let (ok, predId) = st.predIndex(st.kid(tyId, 1))
      if not ok: return false
      let tailTy = st.vecNode(aId, predId)
      if not checkLat(rc.kids[0], aId, ctx, st): return false
      return checkLat(rc.kids[1], tailTy, ctx, st)
    of "suc":
      if not st.meetShape(tyId, {hNat}, "suc needs Nat type"): return false
      return checkLat(rc.kids[0], tyId, ctx, st)
    of "lam":
      if not st.meetShape(tyId, {hPi}, "lam needs Pi type"): return false
      return checkLat(rc.kids[0], st.kid(tyId, 1), ctx & @[st.kid(tyId, 0)], st)
    of "var":
      let i = parseInt(st.atomNameOf(rc.kids[0]))
      if i < 0 or i >= ctx.len:
        st.setFailure(st.descs[rtm], "bound variable", "index " & $i)
        return false
      return st.unionEq(tyId, ctx[i], "variable lookup")
    of "pi":
      if not st.meetShape(tyId, {hUniv}, "Pi former needs Type 0 type"): return false
      let u = st.number(ratom("univ"))
      if not checkLat(rc.kids[0], u, ctx, st): return false
      return checkLat(rc.kids[1], u, ctx & @[rc.kids[0]], st)
    of "vec":
      if not st.meetShape(tyId, {hUniv}, "Vec former needs Type 0 type"): return false
      let u = st.number(ratom("univ"))
      let n = st.number(ratom("nat"))
      if not checkLat(rc.kids[0], u, ctx, st): return false
      return checkLat(rc.kids[1], n, ctx, st)
    of "app":
      # The spec's fallback (infer, then unify) as a single meet: no
      # re-traversal with backtracking, just one union of type nodes.
      let (ok, infTy) = inferLat(tmId, ctx, st)
      if not ok: return false
      return st.unionEq(tyId, infTy, "check: inferred vs expected")
    else:
      st.setFailure(st.descs[rtm], "known pair tag", rc.tag)
      return false
  of ckNone:
    # Synthesis direction (issue step 5): the term node is unknown. Refine
    # it from the type side — the same rules, a different partial state.
    # Genuinely ambiguous cases (unknown index, Nat inhabitants) keep the
    # ambiguity in the state and return true; the driver reports the
    # undetermined nodes as Stuck, distinct from Bottom.
    let rty = st.find(tyId)
    st.materialize(rty)
    if st.failure.isSome: return false
    if st.shape[rty].card != 1:
      return true  # type itself ambiguous: nothing determined yet
    case singleOf(st.shape[rty])
    of hVec:
      let idxId = st.kid(tyId, 1)
      let nl = st.natl[st.find(idxId)]
      if nl.bot: return false  # failure already recorded by the meet
      if not nl.known:
        # nil-vs-cons genuinely ambiguous: keep it in the state, no branch.
        return st.meetShape(tmId, {hNil, hCons}, "synth: Vec inhabitant")
      if nl.val == 0:
        if not st.meetShape(tmId, {hNil}, "synth: Vec A 0 inhabitant"):
          return false
        st.constr[st.find(tmId)] = Constr(kind: ckAtom, atomName: "nil")
        return st.meetNatIdx(idxId, natExact(0), "synth: nil index")
      # idx = suc k: the spine is determined; elements stay holes.
      if not st.meetShape(tmId, {hCons}, "synth: Vec A (suc k) inhabitant"):
        return false
      let rtm2 = st.find(tmId)
      let h = st.freshNode("synth.head")
      let tl = st.freshNode("synth.tail")
      st.constr[rtm2] = Constr(kind: ckPair, tag: "cons", kids: @[h, tl])
      let aId = st.kid(tyId, 0)
      let (okp, predId) = st.predIndex(idxId)
      if not okp: return false
      let tailTy = st.vecNode(aId, predId)
      if not checkLat(h, aId, ctx, st): return false
      return checkLat(tl, tailTy, ctx, st)
    of hNat:
      # zero / suc-chains / literals all inhabit Nat: preserve ambiguity.
      return st.meetShape(tmId, {hZero, hSuc, hNatLit}, "synth: Nat inhabitant")
    of hPi:
      return st.meetShape(tmId, {hLam}, "synth: Pi inhabitant")
    of hUniv:
      return st.meetShape(tmId, {hPi, hVec, hNat}, "synth: former")
    else:
      return true  # e.g. hNil as a *type*: no rule; leave stuck

proc inferLat(tmId: int, ctx: seq[int], st: var LatState): tuple[ok: bool, tyId: int] =
  ## Infer the type node for the term at tmId. Fresh unknowns (app domain /
  ## codomain) are top nodes refined later by unionEq — never logic
  ## variables, never search.
  if st.failure.isSome: return (false, -1)
  let rtm = st.find(tmId)
  let rc = st.constr[rtm]
  case rc.kind
  of ckAtom:
    let name = rc.atomName
    if name == "zero" or isNatLit(ratom(name)):
      return (true, st.number(ratom("nat")))
    st.setFailure(st.descs[rtm], "inferable head", name)
    return (false, -1)
  of ckPair:
    case rc.tag
    of "suc":
      let n = st.number(ratom("nat"))
      if not checkLat(rc.kids[0], n, ctx, st): return (false, -1)
      return (true, n)
    of "var":
      let i = parseInt(st.atomNameOf(rc.kids[0]))
      if i < 0 or i >= ctx.len:
        st.setFailure(st.descs[rtm], "bound variable", "index " & $i)
        return (false, -1)
      return (true, ctx[i])
    of "app":
      # One rule for both of the spec's sub-cases (f a lam / f not a lam):
      # checking f against Pi(top, top) subsumes infer-then-unify, since
      # checkLat on a var head unions rather than failing on non-pi.
      let d = st.freshNode("app.dom")
      let c = st.freshNode("app.cod")
      let pi = st.piNode(d, c)
      if not checkLat(rc.kids[0], pi, ctx, st): return (false, -1)
      if not checkLat(rc.kids[1], d, ctx, st): return (false, -1)
      return (true, c)
    of "pi", "vec":
      let u = st.number(ratom("univ"))
      let n = st.number(ratom("nat"))
      if not checkLat(rc.kids[0], u, ctx, st): return (false, -1)
      # pi's codomain lives under the domain binder; vec's index does not
      # (extending there would shift de Bruijn indices inside n).
      let (kidTy, kidCtx) =
        if rc.tag == "pi": (u, ctx & @[rc.kids[0]]) else: (n, ctx)
      if not checkLat(rc.kids[1], kidTy, kidCtx, st): return (false, -1)
      return (true, u)
    else:
      st.setFailure(st.descs[rtm], "inferable head", rc.tag)
      return (false, -1)
  of ckNone:
    st.setFailure(st.descs[rtm], "determined term head", "unknown")
    return (false, -1)

# --- Driver --------------------------------------------------------------------

type
  LatResult* = object
    ok*: bool
    failure*: Option[FailInfo]
    stuck*: seq[string]  ## undetermined nodes on ok (Stuck, not Bottom)
    output*: RTerm  ## elaborated term, rebuilt from the converged state

proc rebuildHoles*(st: var LatState, id: int): tuple[t: RTerm, holes: seq[string]] =
  ## Output determination (issue §3) extended to partial states: the
  ## elaborated term is built from the converged state's constructions;
  ## nodes that never refined past a threshold become holes (rkVar
  ## leaves), reported separately — the Stuck outcome, distinct from
  ## Bottom. This is the hole representation the design doc anticipates:
  ## a permanently-partial node, no separate stuck-task machinery.
  var r = id
  while st.parent[r] != r: r = st.parent[r]
  case st.constr[r].kind
  of ckAtom:
    (ratom(st.constr[r].atomName), @[])
  of ckPair:
    var spine = rnil()
    var holes: seq[string] = @[]
    let kids = st.constr[r].kids
    for i in countdown(kids.high, 0):
      let (kt, kh) = st.rebuildHoles(kids[i])
      holes.add(kh)
      spine = rpair(kt, spine)
    (rpair(ratom(st.constr[r].tag), spine), holes)
  of ckNone:
    (rvar(r), @[st.descs[r] & " (shape " & $st.shape[r] & ")"])

proc rebuild*(st: var LatState, id: int): RTerm =
  ## Output determination (issue §3): the elaborated term is *built* from
  ## the converged state's constructions, not returned by recursion.
  ## Ground checking-mode runs must fully determine the term.
  let (t, holes) = st.rebuildHoles(id)
  doAssert holes.len == 0, "rebuild: undetermined node(s): " & holes.join(", ")
  t

proc dumpState*(st: var LatState) =
  ## Inspectable state: every node's class, shape, natl, construction.
  for i in 0 ..< st.parent.len:
    let r = st.find(i)
    var cs = "Type 0"
    case st.constr[r].kind
    of ckNone: cs = "none"
    of ckAtom: cs = "atom(" & st.constr[r].atomName & ")"
    of ckPair: cs = "pair(" & st.constr[r].tag & ",kids=" & $st.constr[r].kids & ")"
    echo "node ", i, " root=", r, " desc=", st.descs[i],
      " shape=", st.shape[r], " natl=", st.natl[r], " constr=", cs

proc checkLatTop*(tm, ty, ctx: RTerm): LatResult =
  ## Check tm against ty in ctx. Returns the verdict, the reified
  ## contradiction on rejection, and the rebuilt output on acceptance.
  var st = initLatState()
  let tmId = st.number(tm)
  let tyId = st.number(ty)
  var ctxIds: seq[int] = @[]
  var cur = ctx
  while cur.kind == rkPair:
    ctxIds.add(st.number(cur.head))
    cur = cur.tail
  let ok = checkLat(tmId, tyId, ctxIds, st) and st.failure.isNone
  result.ok = ok
  result.failure = st.failure
  if ok:
    result.output = st.rebuild(tmId)

proc synthLatTop*(ty, ctx: RTerm): LatResult =
  ## Backwards driver (issue step 5): the term starts as a fully unknown
  ## node; the *same* checkLat rules saturate from the type side. The
  ## outcome is three-valued: reject (Bottom, with provenance), accept
  ## (fully determined output), or Stuck (partial state — holes awaiting
  ## information from outside elaboration).
  var st = initLatState()
  let tmId = st.freshNode("synth.root")
  let tyId = st.number(ty)
  var ctxIds: seq[int] = @[]
  var cur = ctx
  while cur.kind == rkPair:
    ctxIds.add(st.number(cur.head))
    cur = cur.tail
  let ok = checkLat(tmId, tyId, ctxIds, st) and st.failure.isNone
  result.ok = ok
  result.failure = st.failure
  if ok:
    let (t, holes) = st.rebuildHoles(tmId)
    result.output = t
    result.stuck = holes
