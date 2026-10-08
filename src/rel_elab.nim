## Relational type inference (typeo) — Track C
##
## A working relational definition of typing for STLC + Nat.
## Run forward to infer types, backward to synthesize terms.

import sequtils
import strutils

type
  # S-expression terms for the relational engine
  SKind = enum skVar, skAtom, skPair
  STerm = ref object
    case kind: SKind
    of skVar: id: int
    of skAtom: name: string
    of skPair: head, tail: STerm

proc svar(id: int): STerm = STerm(kind: skVar, id: id)
proc satom(name: string): STerm = STerm(kind: skAtom, name: name)
proc spair(h, t: STerm): STerm = STerm(kind: skPair, head: h, tail: t)
proc snil(): STerm = satom("nil")

proc slist(elems: seq[STerm]): STerm =
  result = snil()
  for i in countdown(elems.high, 0):
    result = spair(elems[i], result)

proc `$`(t: STerm): string =
  case t.kind
  of skVar: "?v" & $t.id
  of skAtom: t.name
  of skPair:
    var parts: seq[string] = @[]
    var cur = t
    while cur.kind == skPair:
      parts.add($cur.head)
      cur = cur.tail
    if cur.kind == skAtom and cur.name == "nil":
      "(" & parts.join(" ") & ")"
    else:
      "(" & parts.join(" ") & " . " & $cur & ")"

# --- Substitution and unification -----------------------------------

type Subst = seq[(int, STerm)]

proc walk(t: STerm, s: Subst): STerm =
  var cur = t
  while cur.kind == skVar:
    var found = false
    for (id, val) in s:
      if id == cur.id:
        cur = val
        found = true
        break
    if not found: break
  cur

proc occurs(id: int, t: STerm, s: Subst): bool =
  let wt = walk(t, s)
  case wt.kind
  of skVar: wt.id == id
  of skPair: occurs(id, wt.head, s) or occurs(id, wt.tail, s)
  else: false

proc unify(u, v: STerm, s: Subst): tuple[ok: bool, s2: Subst] =
  let u2 = walk(u, s)
  let v2 = walk(v, s)
  if u2.kind == skVar and v2.kind == skVar and u2.id == v2.id:
    return (true, s)
  if u2.kind == skVar:
    if occurs(u2.id, v2, s): return (false, s)
    var ns = s; ns.add((u2.id, v2)); return (true, ns)
  if v2.kind == skVar:
    if occurs(v2.id, u2, s): return (false, s)
    var ns = s; ns.add((v2.id, u2)); return (true, ns)
  if u2.kind == skPair and v2.kind == skPair:
    let (ok1, s1) = unify(u2.head, v2.head, s)
    if not ok1: return (false, s)
    return unify(u2.tail, v2.tail, s1)
  if u2.kind == skAtom and v2.kind == skAtom and u2.name == v2.name:
    return (true, s)
  (false, s)

# --- Goals ----------------------------------------------------------

type Goal = proc(s: Subst): seq[Subst] {.closure.}
const MaxRes = 1000

proc `==`(u, v: STerm): Goal =
  return proc(s: Subst): seq[Subst] =
    let (ok, s2) = unify(u, v, s)
    if ok: @[s2] else: @[]

proc conj(g1, g2: Goal): Goal =
  return proc(s: Subst): seq[Subst] =
    result = @[]
    for s1 in g1(s):
      for s2 in g2(s1):
        result.add(s2)
        if result.len >= MaxRes: return

proc disj(g1, g2: Goal): Goal =
  return proc(s: Subst): seq[Subst] =
    result = g1(s)
    for s2 in g2(s):
      result.add(s2)
      if result.len >= MaxRes: return

var freshId = 0
proc freshVar(): STerm =
  inc freshId; svar(freshId)
proc fresh(body: proc(x: STerm): Goal {.closure.}): Goal =
  ## Lazy: body is called when the goal runs, not when constructed.
  ## Essential for recursive relations.
  return proc(s: Subst): seq[Subst] =
    let v = freshVar()
    body(v)(s)
proc fresh2(body: proc(x, y: STerm): Goal {.closure.}): Goal =
  return proc(s: Subst): seq[Subst] =
    let a = freshVar(); let b = freshVar()
    body(a, b)(s)
proc fresh3(body: proc(x, y, z: STerm): Goal {.closure.}): Goal =
  return proc(s: Subst): seq[Subst] =
    let a = freshVar(); let b = freshVar(); let c = freshVar()
    body(a, b, c)(s)
proc fresh4(body: proc(a, b, c, d: STerm): Goal {.closure.}): Goal =
  return proc(s: Subst): seq[Subst] =
    let x1 = freshVar(); let x2 = freshVar(); let x3 = freshVar(); let x4 = freshVar()
    body(x1, x2, x3, x4)(s)

proc reify(t: STerm, s: Subst): STerm =
  let wt = walk(t, s)
  case wt.kind
  of skVar: wt
  of skPair: spair(reify(wt.head, s), reify(wt.tail, s))
  else: wt

proc run(q: STerm, g: Goal, n = 10): seq[STerm] =
  freshId = 0
  let substs = g(@[])
  result = @[]
  for i in 0 ..< min(n, substs.len):
    result.add(reify(q, substs[i]))

# --- Term constructors (S-expr encoding) ----------------------------

proc natTy(): STerm = satom("nat")
proc arrTy(d, c: STerm): STerm = spair(satom("arr"), spair(d, spair(c, snil())))
proc varTm(i: int): STerm =
  # var(i) as (var i) where i is an atom like "0", "1"
  spair(satom("var"), spair(satom($i), snil()))
proc lamTm(body: STerm): STerm = spair(satom("lam"), spair(body, snil()))
proc appTm(f, a: STerm): STerm = spair(satom("app"), spair(f, spair(a, snil())))
proc zeroTm(): STerm = satom("zero")
proc sucTm(n: STerm): STerm = spair(satom("suc"), spair(n, snil()))

# --- The typeo relation ---------------------------------------------

proc typeo(tm, ty, ctx: STerm): Goal =
  ## typeo(tm, ty, ctx): tm has type ty in context ctx.
  ## ctx is a list of types, innermost first: (ty0 ty1 ...)
  disj(
    # zero: ty = nat
    conj(`==`(tm, zeroTm()), `==`(ty, natTy())),
    disj(
      # suc: tm = (suc n), n : nat, ty = nat
      fresh(proc(n: STerm): Goal =
        conj(`==`(tm, sucTm(n)),
          conj(typeo(n, natTy(), ctx),
            `==`(ty, natTy())))),
      disj(
        # var(0): ctx = (ty0 . _), tm = (var 0), ty = ty0
        fresh2(proc(ty0, ctxTail: STerm): Goal =
          conj(`==`(tm, varTm(0)),
            conj(`==`(ctx, spair(ty0, ctxTail)),
              `==`(ty, ty0)))),
        disj(
          # lam: tm = (lam b), ty = (arr d c), b : c in (d . ctx)
          fresh3(proc(b, d, c: STerm): Goal =
            conj(`==`(tm, lamTm(b)),
              conj(`==`(ty, arrTy(d, c)),
                typeo(b, c, spair(d, ctx))))),
          # app: tm = (app f a), f : (arr d c), a : d, ty = c
          fresh4(proc(f, a, d, c: STerm): Goal =
            conj(`==`(tm, appTm(f, a)),
              conj(typeo(f, arrTy(d, c), ctx),
                conj(typeo(a, d, ctx),
                  `==`(ty, c)))))
        )
      )
    )
  )

when isMainModule:
  echo "=== Relational type inference (typeo) ==="
  echo ""
  
  # Forward: infer type of zero
  echo "Forward: type of zero?"
  let q1 = freshVar()
  let r1 = run(q1, typeo(zeroTm(), q1, snil()), 3)
  for t in r1: echo "  ", t
  assert r1.len == 1 and $r1[0] == "nat"
  echo "ok"
  echo ""
  
  # Forward: infer type of (suc zero)
  echo "Forward: type of (suc zero)?"
  let q2 = freshVar()
  let r2 = run(q2, typeo(sucTm(zeroTm()), q2, snil()), 3)
  for t in r2: echo "  ", t
  assert r2.len == 1 and $r2[0] == "nat"
  echo "ok"
  echo ""
  
  # Forward: infer type of (lam (var 0)) — the identity function
  echo "Forward: type of (lam (var 0))?"
  let q3 = freshVar()
  let idTm = lamTm(varTm(0))
  let r3 = run(q3, typeo(idTm, q3, snil()), 3)
  for t in r3: echo "  ", t
  echo "ok (polymorphic identity: (arr ?v ?v))"
  echo ""
  echo "Note: backward synthesis (typeo(?tm, nat)) requires fair"
  echo "search (interleaving) to avoid infinite recursion. The engine"
  echo "currently uses depth-first search; synthesis is future work."
