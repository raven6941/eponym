## Minimal QTT checker prototype — GH issue #64
##
## Experiments with Quantitative Type Theory quantities (0/1/ω) for affine
## checking of session channels. This is NOT an integration into Eponym's
## core; it's a standalone prototype to answer: "is there a feasible path?"
##
## Fragment: vars, lam with quantity annotation, app, let, and hardcoded
## session operations. Quantities:
##   0   erased (cannot be used)
##   1   linear (must be used exactly once)
##   ω   unrestricted (normal)

import tables

type
  Quantity* = enum
    q0      # erased
    q1      # linear (exactly once)
    qOmega  # unrestricted

  TyKind* = enum
    tkNat, tkSession, tkChan, tkPi, tkSigma

  Ty* = ref object
    case kind*: TyKind
    of tkNat, tkSession:
      discard
    of tkChan:
      sess*: Ty
    of tkPi:
      qty*: Quantity
      dom*: Ty
      cod*: Ty
    of tkSigma:
      fst*: Ty
      snd*: Ty

  TmKind* = enum
    tmVar, tmLam, tmApp, tmLet, tmZero,
    tmSend, tmRecv, tmClose, tmMkChan, tmPair, tmFst, tmSnd

  Tm* = ref object
    case kind*: TmKind
    of tmVar:
      name*: string
    of tmLam:
      lamQty*: Quantity
      lamName*: string
      lamTy*: Ty
      body*: Tm
    of tmApp:
      fn*: Tm
      arg*: Tm
    of tmLet:
      letName*: string
      letVal*: Tm
      letBody*: Tm
    of tmZero:
      discard
    of tmSend, tmRecv, tmClose, tmMkChan:
      discard
    of tmPair:
      p1*: Tm
      p2*: Tm
    of tmFst, tmSnd:
      pr*: Tm

  CtxEntry* = object
    qty*: Quantity
    used*: bool
    ty*: Ty

  CheckError* = object of CatchableError

  Checker* = ref object
    ctx*: Table[string, CtxEntry]
    # usage log for error messages
    trace*: seq[string]

proc newChecker*(): Checker =
  Checker(ctx: initTable[string, CtxEntry](), trace: @[])

proc lookup(c: Checker, name: string): CtxEntry =
  if name notin c.ctx:
    raise newException(CheckError, "unbound variable: " & name)
  result = c.ctx[name]
  # Enforce quantity on use
  case result.qty
  of q0:
    raise newException(CheckError,
      "erased variable used: " & name)
  of q1:
    if result.used:
      raise newException(CheckError,
        "linear variable used more than once: " & name)
    # mark used
    var e = c.ctx[name]
    e.used = true
    c.ctx[name] = e
  of qOmega:
    discard # unrestricted: no tracking

proc checkTm*(c: Checker, tm: Tm, expected: Ty): Ty =
  ## Check tm against expected type, tracking usage. Returns the type.
  case tm.kind
  of tmVar:
    let e = c.lookup(tm.name)
    # TODO: unify e.ty with expected (skip for prototype; assume matches)
    return e.ty
  of tmLam:
    # Extend context with the binder
    if tm.lamName in c.ctx:
      raise newException(CheckError, "shadowing not supported in prototype: " & tm.lamName)
    c.ctx[tm.lamName] = CtxEntry(qty: tm.lamQty, used: false, ty: tm.lamTy)
    let bodyTy = c.checkTm(tm.body, expected) # TODO: expected should be codomain
    # Verify linear usage
    let e = c.ctx[tm.lamName]
    if e.qty == q1 and not e.used:
      raise newException(CheckError,
        "linear variable not used: " & tm.lamName)
    c.ctx.del(tm.lamName)
    return bodyTy
  of tmApp:
    let fTy = c.checkTm(tm.fn, nil) # TODO: infer
    let aTy = c.checkTm(tm.arg, nil)
    # TODO: check fTy is Pi, aTy matches dom
    return nil # placeholder
  of tmLet:
    let vTy = c.checkTm(tm.letVal, nil)
    if tm.letName in c.ctx:
      raise newException(CheckError, "shadowing not supported: " & tm.letName)
    # let-bound vars are unrestricted unless annotated; for the prototype,
    # we track them as linear if their type is Chan
    let q = if vTy != nil and vTy.kind == tkChan: q1 else: qOmega
    c.ctx[tm.letName] = CtxEntry(qty: q, used: false, ty: vTy)
    let bTy = c.checkTm(tm.letBody, expected)
    let e = c.ctx[tm.letName]
    if e.qty == q1 and not e.used:
      raise newException(CheckError,
        "linear variable not used: " & tm.letName)
    c.ctx.del(tm.letName)
    return bTy
  of tmZero:
    return Ty(kind: tkNat)
  of tmSend, tmRecv, tmClose, tmMkChan, tmPair, tmFst, tmSnd:
    # Hardcoded ops for the prototype; real impl would look up types
    return nil

# --- Test: doubleSend should be rejected -----------------------------------

proc testDoubleSend*(): bool =
  ## let ch1 = sendNat ... ch in
  ## let ch2 = sendNat ... ch in  # BUG: ch reused
  ## Should raise CheckError.
  let c = newChecker()
  # ch : Chan (linear)
  c.ctx["ch"] = CtxEntry(qty: q1, used: false,
    ty: Ty(kind: tkChan, sess: Ty(kind: tkSession)))
  try:
    # First use: ok, marks ch as used
    discard c.lookup("ch")
    # Second use: should fail
    discard c.lookup("ch")
    return false # should not reach here
  except CheckError:
    return true

proc testSingleUse*(): bool =
  ## Single use of a linear variable should succeed.
  let c = newChecker()
  c.ctx["ch"] = CtxEntry(qty: q1, used: false,
    ty: Ty(kind: tkChan, sess: Ty(kind: tkSession)))
  try:
    discard c.lookup("ch")
    # Simulate end of scope: check it was used
    let e = c.ctx["ch"]
    return e.used
  except CheckError:
    return false

proc testUnusedLinear*(): bool =
  ## A linear variable that is never used should be rejected at scope end.
  ## (This is checked by the lam/let cases, not lookup.)
  return true # placeholder; the lam case handles this

when isMainModule:
  echo "doubleSend rejected: ", testDoubleSend()
  echo "single use ok: ", testSingleUse()

# --- Full session flow test ------------------------------------------------

proc testSessionFlow*(): bool =
  ## Simulates:
  ##   lam (ch :1 Chan). let ch1 = send ch in let p = recv ch1 in close (snd p)
  ## Each channel is used exactly once. Should succeed.
  let c = newChecker()
  # ch :1 Chan
  c.ctx["ch"] = CtxEntry(qty: q1, used: false,
    ty: Ty(kind: tkChan, sess: Ty(kind: tkSession)))
  try:
    # send ch : uses ch, produces ch1
    discard c.lookup("ch")
    c.ctx["ch1"] = CtxEntry(qty: q1, used: false,
      ty: Ty(kind: tkChan, sess: Ty(kind: tkSession)))
    # recv ch1 : uses ch1, produces p
    discard c.lookup("ch1")
    c.ctx["p"] = CtxEntry(qty: qOmega, used: false, ty: nil) # pair, unrestricted
    # close (snd p) : uses p (but p is omega, so no tracking)
    discard c.lookup("p")
    # Verify all linear vars were used
    for name, e in c.ctx.pairs:
      if e.qty == q1 and not e.used:
        echo "FAIL: linear var not used: ", name
        return false
    return true
  except CheckError as e:
    echo "FAIL: ", e.msg
    return false

proc testDoubleSendFull*(): bool =
  ## Simulates:
  ##   lam (ch :1 Chan). let ch1 = send ch in let ch2 = send ch in ...
  ## Second use of ch should fail.
  let c = newChecker()
  c.ctx["ch"] = CtxEntry(qty: q1, used: false,
    ty: Ty(kind: tkChan, sess: Ty(kind: tkSession)))
  try:
    discard c.lookup("ch")  # first send: ok
    discard c.lookup("ch")  # second send: should fail
    return false
  except CheckError:
    return true

when isMainModule:
  echo "session flow ok: ", testSessionFlow()
  echo "doubleSend full rejected: ", testDoubleSendFull()
